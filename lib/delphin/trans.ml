open Basis ;; 
(* Translator from Delphin external syntax to Delphin internal syntax *)

(* Author: Richard Fontana, Carsten Schuermann *)

module type TRANS = sig
  module DextSyn : Dextsyn.DEXTSYN

  exception Error of string

  val internalizeSig : unit -> unit

  val transFor :
    (* IntSyn.dctx * *)
    DextSyn.form ->
    Tomega.for_sml

  val transDecs : DextSyn.decs -> Tomega.prg
  val externalizePrg : Tomega.prg -> Tomega.prg
  (* val transPro : DextSyn.Prog -> Tomega.Prg *)
end
(* Translator from Delphin external syntax to Delphin internal syntax *)

(* Author:  Carsten Schuermann *)

module Trans (DextSyn' : Dextsyn.DEXTSYN) = struct
  module DextSyn = DextSyn'
  module D = DextSyn'
  module L = Lexer
  module I = IntSyn
  module LS = Stream
  module T = Tomega
  module TA = TomegaAbstract

  exception Error of string

  type internal = Empty | Const of int * int | Type of int

  let maxCid = Global.maxCid
  let internal = (Array.array (maxCid + 1, Empty) : internal Array.array)
  (* Invariant   for_sml each cid which has been internalize out of a block,
       internal(cid) = Const(n, i), where n is the number of some variables and
       i is the projection index
       for_sml each type family
       internal(cid) = Type (cid'), where cid' is the orginial type family.
    *)

  (* checkEOF f = r

      Invariant:
      If   f is the end of stream
      then r is a region

      Side effect: May raise Parsing.Error
    *)

  let rec checkEOF = function
    | LS.Cons ((L.EOF, r), s') -> r
    | LS.Cons ((t, r), _) ->
        Parsing.error (r, "Expected `}', found " ^ L.toString t)
  (* Note that this message is inapplicable when we use
            checkEOF in stringToterm --rf *)

  (* stringToDec s = dec

       Invariant:
       If   s is a string representing a declaration,
       then dec is the result of parsing it
       otherwise Parsing.error is raised.
    *)

  let rec stringTodec s =
    let f = LS.expose (L.lexStream (TextIO.openString s)) in
    let (x, yOpt), f' = ParseTerm.parseDec' f in
    let r2 = checkEOF f' in
    let dec =
      match yOpt (* below use region arithmetic --cs !!!  *) with
      | None -> ReconTerm.dec0 (x, r2)
      | Some y -> ReconTerm.dec (x, y, r2)
    in
    dec

  let rec stringToblocks s =
    let f = LS.expose (L.lexStream (TextIO.openString s)) in
    let dl, f' = ParseTerm.parseCtx' f in
    dl
  (* stringToWorlds s = W

       Invariant:
       If   s is a string representing an expression,
       then W is the result of parsing it
       otherwise Parsing.error is raised.
    *)

  let rec stringToWorlds s =
    let f = LS.expose (L.lexStream (TextIO.openString s)) in
    let t, f' = ParseTerm.parseQualIds' f in
    let r2 = checkEOF f' in
    t
  (* closure (G, V) = V'

       Invariant:
       {G}V = V'
    *)

  let rec closure = function
    | I.Null, V -> V
    | I.Decl (G, D), V -> closure (G, I.Pi ((D, I.Maybe), V))
  (* internalizeBlock  (n, G, Vb, S) (L2, s) = ()

       Invariant:
       If   |- G ctx                the context of some variables
       and  G |- Vb :  type         the type of the block
       and  G |- L1, L2 decs
       and  G1, L1 |- L2 decs       block declarations still to be traversed
       and  G, b:Vb |- s : G1, L1
       and  n is the current projection
       then internalizeBlock adds new declarations into the signature that
              correspond to the block declarations.
    *)

  let rec internalizeBlock = function
    | _, ([], _) -> ()
    | (n, G, Vb, S), (I.Dec (Some name, V) :: L2, s) ->
        (* G, B |- V' : type *)
        (* G |- {B} V' : type *)
        let name' = "o_" ^ name in
        let V1 = I.EClo (V, s) in
        let V2 = I.Pi ((I.Dec (None, Vb), I.Maybe), V1) in
        let V3 = closure (G, V2) in
        let m = I.ctxLength G in
        let condec = I.ConDec (name', None, m, I.Normal, V3, I.Type) in
        let _ = TypeCheck.check (V3, I.Uni I.Type) in
        let _ =
          if !Global.chatter >= 4 then print (Print.conDecToString condec ^ "\n")
          else ()
        in
        let cid = I.sgnAdd condec in
        let _ = Names.installConstName cid in
        let _ = Array.update (internal, cid, Const (m, n)) in
        internalizeBlock
          (n + 1, G, Vb, S)
          (L2, I.Dot (I.Exp (I.Root (I.Const cid, S)), s))
  (* makeSpine (n, G, S) = S'

       Invariant:
       If  G0 = G, G'
       and |G'| = n
       and G0 |- S : V >> V'   for_sml some V, V'
       then S' extends S
       and G0 |- S' : V >> type.
    *)

  let rec makeSpine = function
    | _, I.Null, S -> S
    | n, I.Decl (G, D), S ->
        makeSpine (n + 1, G, I.App (I.Root (I.BVar (n + 1), I.Nil), S))
  (* interalizeCondec condec = ()

       Invariant:
       If   condec is a condec,
       then all pi declarations are internalized if condec was a blockdec
    *)

  let rec internalizeCondec = function
    | cid, I.ConDec _ -> ()
    | cid, I.ConDef _ -> ()
    | cid, I.AbbrevDef _ -> ()
    | cid, I.BlockDec (name, _, Gsome, Lpi) ->
        let V' = closure (Gsome, I.Uni I.Type) in
        let C = I.ConDec (name ^ "'", None, 0, I.Normal, V', I.Kind) in
        let a = I.sgnAdd C in
        let _ = Array.update (internal, a, Type cid) in
        let _ = Names.installConstName a in
        let S = makeSpine (0, Gsome, I.Nil) in
        let Vb = I.Root (I.Const a, S) in
        let S' = makeSpine (0, I.Decl (Gsome, I.Dec (None, Vb)), I.Nil) in
        internalizeBlock (1, Gsome, Vb, S') (Lpi, I.shift)
    | cid, I.SkoDec _ -> ()
  (* sigToCtx () = ()

       Invariant:
       G is the internal representation of the global signature
       It converts every block declaration to a type family (stored in the global
       signature) and a list of declarations.
    *)

  let rec internalizeSig () =
    (* we might want to save max, here to restore the original
                 signature after parsing is over  --cs Thu Apr 17 09:46:29 2003 *)
    let max, _ = I.sgnSize () in
    let rec internalizeSig' n =
      if n >= max then ()
      else (
        internalizeCondec (n, I.sgnLookup n);
        internalizeSig' (n + 1))
    in
    internalizeSig' 0
  (* Externalization *)

  let rec dropSpine = function
    | 0, S -> S
    | n, I.App (_, S) -> dropSpine (n - 1, S)

  let rec makeSub = function
    | I.Nil, s -> s
    | I.App (U, S), s -> makeSub (S, I.Dot (I.Exp U, s))

  let rec externalizeExp' = function
    | U -> U
    | I.Pi ((D, DP), U) -> I.Pi ((externalizeDec D, DP), externalizeExp U)
    | I.Root (H, S) -> I.Root (H, externalizeSpine S)
    | I.Root (H, S) -> (
        match I.constUni c with
        | I.Kind -> I.Root (H, externalizeSpine S)
        | I.Type ->
            let (Const (n, i)) = Array.sub (internal, c) in
            let (I.App (I.Root (I.BVar b, I.Nil), S')) = dropSpine (n, S) in
            I.Root (I.Proj (I.Bidx b, i), externalizeSpine S'))
    | I.Root (I.Proj _, _) -> raise Domain
    | I.Root (I.Skonst _, _) -> raise Domain
    | I.Root (I.Def _, _) -> raise Domain
    | I.Root (I.NSDef _, _) -> raise Domain
    | I.Root (I.FVar _, _) -> raise Domain
    | I.Root (I.FgnConst _, _) -> raise Domain
    | I.Redex (U, S) -> I.Redex (externalizeExp U, externalizeSpine S)
    | I.Lam (D, U) -> I.Lam (externalizeDec D, externalizeExp U)

  and externalizeExp U = externalizeExp' (Whnf.normalize (U, I.id))
  and externalizeBlock B = B
  and externalizeDec (I.Dec (name, V)) = I.Dec (name, externalizeExp V)

  and externalizeSpine = function
    | I.Nil -> I.Nil
    | I.App (U, S) -> I.App (externalizeExp U, externalizeSpine S)

  and externalizeSub = function
    | s -> s
    | I.Dot (F, s) -> I.Dot (externalizeFront F, externalizeSub s)

  and externalizeFront = function
    | F -> F
    | I.Exp U -> I.Exp (externalizeExp U)
    | I.Block B -> I.Block (externalizeBlock B)
    | F -> F

  let rec externalizePrg = function
    | n, T.Lam (D, P) ->
        T.Lam (externalizeMDec (n, D), externalizePrg (n + 1, P))
    | n, T.New P -> T.New (externalizePrg (n, P))
    | n, T.Box (W, P) -> T.Box (W, externalizePrg (n, P))
    | n, T.Choose P -> T.Choose (externalizePrg (n, P))
    | n, T.PairExp (U, P) -> T.PairExp (externalizeExp U, externalizePrg (n, P))
    | n, T.PairPrg (P1, P2) ->
        T.PairPrg (externalizePrg (n, P1), externalizePrg (n, P2))
    | n, T.PairBlock (B, P) ->
        T.PairBlock (externalizeBlock B, externalizePrg (n, P))
    | n, T.Unit -> T.Unit
    | n, T.Var k -> T.Var k
    | n, T.Const c -> T.Const c
    | n, T.Redex (P, S) ->
        T.Redex (externalizePrg (n, P), externalizeMSpine (n, S))
    | n, T.Rec (D, P) ->
        T.Rec (externalizeMDec (n, D), externalizePrg (n + 1, P))
    | n, T.Case (T.Cases O) -> T.Case (T.Cases (externalizeCases O))
    | n, T.Let (D, P1, P2) ->
        T.Let
          ( externalizeMDec (n, D),
            externalizePrg (n, P1),
            externalizePrg (n + 1, P2) )

  and externalizeMDec = function
    | n, T.UDec D -> (
        match Array.sub (internal, a) with
        | Type a' ->
            T.UDec
              (I.BDec (name, (a', makeSub (externalizeSpine S, I.Shift n))))
        | _ -> T.UDec (externalizeDec D))
    | n, T.UDec D -> T.UDec (externalizeDec D)
    | n, T.PDec (s, F) -> T.PDec (s, externalizeFor (n, F))

  and externalizeFor = function
    | n, T.World (W, F) -> T.World (W, externalizeFor (n, F))
    | n, T.All ((D, Q), F) ->
        T.All ((externalizeMDec (n, D), Q), externalizeFor (n + 1, F))
    | n, T.Ex ((D, Q), F) ->
        T.Ex ((externalizeDec D, Q), externalizeFor (n + 1, F))
    | n, T.True -> T.True
    | n, T.And (F1, F2) -> T.And (externalizeFor (n, F1), externalizeFor (n, F2))

  and externalizeMSpine = function
    | n, T.Nil -> T.Nil
    | n, T.AppExp (U, S) -> T.AppExp (externalizeExp U, externalizeMSpine (n, S))
    | n, T.AppBlock (B, S) ->
        T.AppBlock (externalizeBlock B, externalizeMSpine (n, S))
    | n, T.AppPrg (P, S) ->
        T.AppPrg (externalizePrg (n, P), externalizeMSpine (n, S))

  and externalizeCases = function
    | [] -> []
    | (Psi, t, P) :: O ->
        let n = I.ctxLength Psi in
        (externalizeMCtx Psi, externalizeMSub (n, t), externalizePrg (n, P))
        :: externalizeCases O

  and externalizeMSub = function
    | n, t -> t
    | n, T.Dot (F, t) -> T.Dot (externalizeMFront (n, F), externalizeMSub (n, t))

  and externalizeMFront = function
    | n, F -> F
    | n, T.Prg P -> T.Prg (externalizePrg (n, P))
    | n, T.Exp U -> T.Exp (externalizeExp U)
    | n, T.Block B -> T.Block (externalizeBlock B)
    | n, F -> F

  and externalizeMCtx = function
    | I.Null -> I.Null
    | I.Decl (Psi, D) ->
        I.Decl (externalizeMCtx Psi, externalizeMDec (I.ctxLength Psi, D))
  (* Translation starts here *)

  let rec transTerm = function
    | D.Rtarrow (t1, t2) ->
        let s1, c1 = transTerm t1 in
        let s2, c2 = transTerm t2 in
        (s1 ^ " -> " ^ s2, c1 @ c2)
    | D.Ltarrow (t1, t2) ->
        let s1, c1 = transTerm t1 in
        let s2, c2 = transTerm t2 in
        (s1 ^ " <- " ^ s2, c1 @ c2)
    | D.Type -> ("type", [])
    | D.Id s -> (
        let qid = Names.Qid ([], s) in
        match Names.constLookup qid with
        | None -> (s, [])
        | Some cid -> (
            match I.sgnLookup cid with
            | I.BlockDec _ -> (s ^ "'", [])
            | _ -> (s, [])))
    | D.Pi (D, t) ->
        let s1, c1 = transDec D in
        let s2, c2 = transTerm t in
        ("{" ^ s1 ^ "}" ^ s2, c1 @ c2)
    | D.Fn (D, t) ->
        let s1, c1 = transDec D in
        let s2, c2 = transTerm t in
        ("[" ^ s1 ^ "]" ^ s2, c1 @ c2)
    | D.App (t1, t2) ->
        let s1, c1 = transTerm t1 in
        let s2, c2 = transTerm t2 in
        (s1 ^ " " ^ s2, c1 @ c2)
    | D.Omit -> ("_", [])
    | D.Paren t ->
        let s, c = transTerm t in
        ("(" ^ s ^ ")", c)
    | D.Of (t1, t2) ->
        let s1, c1 = transTerm t1 in
        let s2, c2 = transTerm t2 in
        (s1 ^ ":" ^ s2, c1 @ c2)
    | D.Dot (t, s2) ->
        let s1, c1 = transTerm t in
        ("o_" ^ s2 ^ " " ^ s1, c1)

  and transDec (D.Dec (s, t)) =
    let s', c = transTerm t in
    (s ^ ":" ^ s', c)

  let rec transWorld = function
    | D.WorldIdent s ->
        let qid = Names.Qid ([], s) in
        let cid =
          match Names.constLookup qid with
          | None ->
              raise
                (Names.Error
                   ("Undeclared label "
                   ^ Names.qidToString (valOf (Names.constUndef qid))
                   ^ "."))
          | Some cid -> cid
        in
        [ cid ]
    | D.Plus (W1, W2) -> transWorld W1 @ transWorld W2
    | D.Concat (W1, W2) -> transWorld W1 @ transWorld W2
    | D.Times W -> transWorld W

  let rec transFor' (Psi, D) =
    let G = I.Decl (I.Null, D) in
    let (ReconTerm.JWithCtx (I.Decl (I.Null, D'), ReconTerm.JNothing)) =
      ReconTerm.reconWithCtx (Psi, ReconTerm.jwithctx (G, ReconTerm.jnothing))
    in
    D'
  (* transFor (ExtDctx, ExtF) = (Psi, F)

       Invariant:
       If   |- ExtDPsi extdecctx
       and  |- ExtF extfor
       then |- Psi <= ExtDPsi
       and  Psi |- F <= ExtF
    *)

  let rec transFor = function
    | Psi, D.True -> T.True
    | Psi, D.And (EF1, EF2) -> T.And (transFor (Psi, EF1), transFor (Psi, EF2))
    | Psi, D.Forall (D, F) ->
        let D'', [] = transDec D in
        let D' = transFor' (Psi, stringTodec D'') in
        T.All ((T.UDec D', T.Explicit), transFor (I.Decl (Psi, D'), F))
    | Psi, D.Exists (D, F) ->
        let D'', [] = transDec D in
        let D' = transFor' (Psi, stringTodec D'') in
        T.Ex ((D', T.Explicit), transFor (I.Decl (Psi, D'), F))
    | Psi, D.ForallOmitted (D, F) ->
        let D'', [] = transDec D in
        let D' = transFor' (Psi, stringTodec D'') in
        T.All ((T.UDec D', T.Implicit), transFor (I.Decl (Psi, D'), F))
    | Psi, D.ExistsOmitted (D, F) ->
        let D'', [] = transDec D in
        let D' = transFor' (Psi, stringTodec D'') in
        T.Ex ((D', T.Implicit), transFor (I.Decl (Psi, D'), F))
    | Psi, D.World (W, EF) ->
        T.World (T.Worlds (transWorld W), transFor (Psi, EF))
  (* stringToTerm s = U

       Invariant:
       If   s is a string representing an expression,
       then U is the result of parsing it
       otherwise Parsing.error is raised.
    *)

  let rec stringToterm s =
    let f = LS.expose (L.lexStream (TextIO.openString s)) in
    let t, f' = ParseTerm.parseTerm' f in
    let r2 = checkEOF f' in
    t
  (* head (dH) = n

       Invariant:
       n is the name of the function head dH
    *)

  let rec head = function
    | D.Head s -> s
    | D.AppLF (H, _) -> head H
    | D.AppMeta (H, _) -> head H
  (* lamClosure (F, P) = P'

       Invariant:
       If   . |- F formula
       and  . |- F = all D1. ... all Dn. F' formula
         for_sml  . |- F' formula that does not commence with a universal quantifier
       and . |- P :: F'
       then P' = lam D1 ... lam Dn P
    *)

  let rec lamClosure = function
    | T.All ((D, _), F), P -> T.Lam (D, lamClosure (F, P))
    | T.World (_, F), P -> lamClosure (F, P)
    | T.Ex _, P -> P

  let rec exists = function
    | c, [] -> raise (Error "Current world is not subsumed")
    | c, c' :: cids -> if c = c' then () else exists (c, cids)

  let rec subsumed = function
    | [], cids' -> ()
    | c :: cids, cids' ->
        exists (c, cids');
        subsumed (cids, cids')

  let rec checkForWorld = function
    | T.World (W, F), t', T.Worlds cids' ->
        (* check that W is at W' *)
        let _ = subsumed (cids', cids) in
        (F, t', W)
    | FtW -> FtW
  (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for_sml any G
       then Psi0, G[t] |- t : Psi, G
    *)

  let rec dotn = function t, 0 -> t | t, n -> I.dot1 (dotn (t, n - 1))
  (* append (Psi1, Psi2) = Psi3

       Invariant:
       If   |- Psi1 ctx
       and  |- Psi2 ctx
       then |- Psi3 = Psi1, Psi2 ctx
    *)

  let rec append = function
    | Psi, I.Null -> Psi
    | Psi, I.Decl (Psi', D) -> I.Decl (append (Psi, Psi'), D)

  let rec parseTerm (Psi, (s, V)) =
    let term', c = transTerm s in
    let term = stringToterm term' in
    let (ReconTerm.JOf ((U, occ), (_, _), L)) =
      ReconTerm.reconWithCtx (T.coerceCtx Psi, ReconTerm.jof' (term, V))
    in
    U

  let rec parseDec (Psi, s) =
    let dec', c = transDec s in
    let dec = stringTodec dec' in
    let (ReconTerm.JWithCtx (I.Decl (I.Null, D), ReconTerm.JNothing)) =
      ReconTerm.reconWithCtx
        ( T.coerceCtx Psi,
          ReconTerm.jwithctx (I.Decl (I.Null, dec), ReconTerm.jnothing) )
    in
    let (I.Dec (Some n, _)) = D in
    D
  (* transDecs ((Psi, t), dDs, sc, W) = x

       Invariant:
       If   . |- t :: Psi
       and  Psi |- dDs decs
       and  W is the valid world
       and  sc is the success continuation that input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this output: anything.
       then eventually x = ().     --cs
    *)

  let rec transDecs = function
    | Psi, D.Empty, sc, W -> sc (Psi, W)
    | Psi, D.FormDecl (FormD, Ds), sc, W -> transForDec (Psi, FormD, Ds, sc, W)
    | Psi, D.ValDecl (ValD, Ds), sc, W -> transValDec (Psi, ValD, Ds, sc, W)
    | Psi, D.NewDecl (D, Ds), sc, W ->
        let D' = T.UDec (parseDec (Psi, D)) in
        (*          T.Let (T.PDec (NONE, T.True), T.Lam (D', transDecs (I.Decl (Psi, D'), Ds, sc, W)), T.Unit) *)
        T.Let
          ( T.PDec (None, T.True),
            T.Lam (D', transDecs (I.Decl (Psi, D'), Ds, sc, W)),
            T.Var 1 )
        (* T.True is not right! -- cs Sat Jun 28 11:43:30 2003  *)
    | _ ->
        raise
          (Error
             "Constant declaration must be followed by a constant definition")

  and lookup = function
    | I.Null, n, s -> raise (Error ("Undeclared constant " ^ s))
    | I.Decl (G, T.PDec (None, _)), n, s -> lookup (G, n + 1, s)
    | I.Decl (G, T.UDec _), n, s -> lookup (G, n + 1, s)
    | I.Decl (G, T.PDec (Some s', F)), n, s ->
        if s = s' then (n, T.forSub (F, T.Shift n)) else lookup (G, n + 1, s)

  and transHead = function
    | Psi, D.Head s, args ->
        let n, F = lookup (Psi, 1, s) in
        transHead' ((F, T.id), I.Nil, args)
    | Psi, D.AppLF (h, t), args -> transHead (Psi, h, t :: args)

  and transHead' = function
    | (T.World (_, F), s), S, args -> transHead' ((F, s), S, args)
    | (T.All ((T.UDec (I.Dec (_, V)), T.Implicit), F'), s), S, args ->
        let X =
          I.newEVar (I.Decl (I.Null, I.NDec), I.EClo (V, T.coerceSub s))
        in
        transHead' ((F', T.Dot (T.Exp X, s)), I.App (X, S), args)
    | (T.All ((T.UDec (I.Dec (_, V)), T.Explicit), F'), s), S, t :: args ->
        let term', c = transTerm t in
        let term = stringToterm term' in
        let (ReconTerm.JOf ((U, occ), (_, _), L)) =
          ReconTerm.reconWithCtx
            (I.Null, ReconTerm.jof' (term, I.EClo (V, T.coerceSub s)))
        in
        transHead' ((F', T.Dot (T.Exp U, s)), I.App (U, S), args)
    | (F, s), S, [] -> ((F, s), S)

  and spineToSub = function
    | (I.Nil, _), s' -> s'
    | (I.App (U, S), t), s' ->
        T.Dot (T.Exp (I.EClo (U, t)), spineToSub ((S, t), s'))

  and transPattern = function
    | p, (T.Ex ((I.Dec (_, V), T.Implicit), F'), s) ->
        transPattern
          ( p,
            ( F',
              T.Dot
                ( T.Exp
                    (I.EVar (ref None, I.Null, I.EClo (V, T.coerceSub s), ref [])),
                  s ) ) )
    | D.PatInx (t, p), (T.Ex ((I.Dec (_, V), T.Explicit), F'), s) ->
        let term', c = transTerm t in
        let term = stringToterm term' in
        let (ReconTerm.JOf ((U, occ), (_, _), L)) =
          ReconTerm.reconWithCtx
            (I.Null, ReconTerm.jof' (term, I.EClo (V, T.coerceSub s)))
        in
        T.PairExp (U, transPattern (p, (F', T.Dot (T.Exp U, s))))
    | D.PatUnit, (F, s) -> T.Unit

  and transFun1 = function
    | Psi, (s', F), D.FunDecl (D.Fun (eH, eP), Ds), sc, W ->
        let s = head eH in
        let _ =
          if s = s' then ()
          else
            raise
              (Error "Function defined is different from function declared.")
        in
        transFun2
          ( Psi,
            (s, F),
            D.FunDecl (D.Bar (eH, eP), Ds),
            sc,
            fun Cs -> (T.Case (T.Cases Cs), W) )
    | Psi, (s', F), D.FunDecl (D.FunAnd (eH, eP), Ds), sc, W ->
        raise (Error "Mutual recursive functions not yet implemented")
    | _ -> raise (Error "Function declaration expected")

  and transFun2 = function
    | Psi, (s, F), D.FunDecl (D.Bar (eH, eP), Ds), sc, k, W ->
        transFun3 (Psi, (s, F), eH, eP, Ds, sc, k, W)
    | Psi, (s, F), Ds, sc, k, W ->
        let D = T.PDec (Some s, F) in
        let P' = T.Rec (D, lamClosure (F, k [])) in
        (P', Ds)

  and transFun3 (Psi, (s, F), eH, eP, Ds, sc, k, W) =
    (*                val F' = T.forSub (F, t) *)
    (* |Psi''| = m0 + m' *)
    (* Psi0, Psi'[^m0] |- t0 : Psi' *)
    (*        val t1 = T.Dot (T.Prg (T.Root (T.Var (m'+1), T.Nil)), T.Shift (m'))   (* BUG !!!! Wed Jun 25 11:23:13 2003 *)
                                        (* Psi0, Psi'[^m0] |- t1 : F[^m0]  *)
*)
    (*        val _ = print (TomegaPrint.forToString (Names.ctxName (T.coerceCtx Psi''), myF) ^ "\n") *)
    let _ =
      if head eH <> s then
        raise (Error "Functions don't all have the same name")
      else ()
    in
    let _ = Names.varReset I.Null in
    let Psi0 = I.Decl (Psi, T.PDec (Some s, F)) in
    let (F', t'), S = transHead (Psi0, eH, []) in
    let Psi', S' = Abstract.abstractSpine (S, I.id) in
    let Psi'' = append (Psi0, T.embedCtx Psi') in
    let m0 = I.ctxLength Psi0 in
    let m' = I.ctxLength Psi' in
    let t0 = dotn (I.Shift m0, m') in
    let t'' = spineToSub ((S', t0), T.Shift m') in
    let P = transProgI (Psi'', eP, (F', t'), W) in
    transFun2 (Psi, (s, F), Ds, sc, fun Cs -> (k ((Psi'', t'', P) :: Cs), W))

  and transForDec (Psi, D.Form (s, eF), Ds, sc, W) =
    (*        val _ = print s
          val _ = print " :: "
          val _ = print (TomegaPrint.forToString (T.embedCtx G, F'') ^ "\n") *)
    let G = Names.ctxName (T.coerceCtx Psi) in
    let F = transFor (G, eF) in
    let F'' = T.forSub (F, T.id) in
    let _ = TomegaTypeCheck.checkFor (Psi, F'') in
    let P, Ds' = transFun1 (Psi, (s, F'), Ds, sc, W) in
    let D = T.PDec (Some s, F'') in
    T.Let
      (D, T.Box (W, P), transDecs (I.Decl (Psi, D), Ds', (fun P' -> sc P'), W))

  and transValDec (Psi, D.Val (EPat, eP, eFopt), Ds, sc, W) =
    (*        val t = T.Dot (T.Prg Pat', T.id)  was --cs Tue Jun 24 13:04:55 2003 *)
    let P, (F', t') =
      match eFopt with
      | None -> transProgS (Psi, eP, W, [])
      | Some eF ->
          let F' = transFor (T.coerceCtx Psi, eF) in
          let P' = transProgIN (Psi, eP, F', W) in
          (P', (F', T.id))
    in
    let F'' = T.forSub (F', t') in
    let Pat = transPattern (EPat, (F', t')) in
    let D = T.PDec (None, F'') in
    let Psi', Pat' = Abstract.abstractTomegaPrg Pat in
    let m = I.ctxLength Psi' in
    let t = T.Dot (T.Prg Pat', T.Shift m) in
    let Psi'' = append (Psi, Psi') in
    let P'' = transDecs (Psi'', Ds, sc, W) in
    T.Let (D, P, T.Case (T.Cases [ (Psi'', t, P'') ]))

  and transProgI (Psi, eP, Ft, W) = transProgIN (Psi, eP, T.forSub Ft, W)

  and transProgIN = function
    | Psi, D.Unit, T.True, W -> T.Unit
    | Psi, P, T.Ex ((I.Dec (_, V), T.Explicit), F'), W ->
        let U = parseTerm (Psi, (s, V)) in
        let P' = transProgI (Psi, EP, (F', T.Dot (T.Exp U, T.id)), W) in
        T.PairExp (U, P')
    | Psi, D.Let (eDs, eP), F, W ->
        transDecs
          ( Psi,
            eDs,
            fun (Psi', W') ->
              ( transProgI
                  ( Psi',
                    eP,
                    (F, T.Shift (I.ctxLength Psi' - I.ctxLength Psi)),
                    W' ),
                W ) )
    | Psi, D.Choose (eD, eP), F, W ->
        let D' = parseDec (Psi, eD) in
        let Psi'' = I.Decl (Psi, T.UDec D') in
        T.Choose (T.Lam (T.UDec D', transProgI (Psi'', eP, (F, T.Shift 1), W)))
    | Psi, D.New ([], eP), F, W -> transProgIN (Psi, eP, F, W)
    | Psi, D.New (eD :: eDs, eP), F, W ->
        let D' = parseDec (Psi, eD) in
        let Psi'' = I.Decl (Psi, T.UDec D') in
        T.New
          (T.Lam
             ( T.UDec D',
               transProgI (Psi'', D.New (eD :: eDs, eP), (F, T.Shift 1), W) ))
    | Psi, P, F, W ->
        (* check that F == F' *)
        let P', (F', _) = transProgS (Psi, P, W, []) in
        let () = () in
        P'

  and transProgS = function
    | Psi, D.Unit, W, args -> (T.Unit, (T.True, T.id))
    | Psi, D.AppTerm (EP, s), W, args -> transProgS (Psi, EP, W, s :: args)
    | Psi, D.Const name, W, args ->
        (*         val lemma = T.lemmaName name
           val F = T.lemmaFor lemma *)
        let n, F = lookup (Psi, 1, name) in
        let S, Fs' = transProgS' (Psi, (F, T.id), W, args) in
        (T.Redex (T.Var n, S), Fs')
    | Psi, D.Choose (eD, eP), W, args ->
        let D' = parseDec (Psi, eD) in
        let P, (F, t) = transProgS (I.Decl (Psi, T.UDec D'), eP, W, args) in
        (T.Choose (T.Lam (T.UDec D', P)), (F, t))
    | Psi, D.New ([], eP), W, args -> transProgS (Psi, eP, W, args)
    | Psi, D.New (eD :: eDs, eP), W, args ->
        let D' = parseDec (Psi, eD) in
        let P, (F, t) =
          transProgS (I.Decl (Psi, T.UDec D'), D.New (eDs, eP), W, args)
        in
        let (T.UDec D'') = externalizeMDec (I.ctxLength Psi, T.UDec D') in
        let B, _ = T.deblockify (I.Decl (I.Null, D'')) in
        let F' = TA.raiseFor (B, (F, T.coerceSub t)) in
        (T.New (T.Lam (T.UDec D', P)), (F', T.id))
  (* bug: forgot to raise F[t] to F' --cs Tue Jul  1 10:49:52 2003 *)

  and transProgS' = function
    | Psi, (T.World (_, F), s), W, args -> transProgS' (Psi, (F, s), W, args)
    | Psi, (T.All ((T.UDec (I.Dec (_, V)), T.Implicit), F'), s), W, args ->
        (*        val X = I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil) *)
        let G = T.coerceCtx Psi in
        let X = I.newEVar (G, I.EClo (V, T.coerceSub s)) in
        let S, Fs' = transProgS' (Psi, (F', T.Dot (T.Exp X, s)), W, args) in
        (T.AppExp (Whnf.normalize (X, I.id), S), Fs')
    | Psi, (T.All ((T.UDec (I.Dec (_, V)), T.Explicit), F'), s), W, t :: args ->
        (*        val (F'', s'', _) = checkForWorld (F', T.Dot (T.Exp U, s), W) *)
        let U = parseTerm (Psi, (t, I.EClo (V, T.coerceSub s))) in
        let S, Fs' = transProgS' (Psi, (F', T.Dot (T.Exp U, s)), W, args) in
        (T.AppExp (U, S), Fs')
    | Psi, (F, s), _, [] -> (T.Nil, (F, s))
  (*
     | transProgS ((Psi, env), D.Pair (EP1, EP2), W) =
        let
          val (P1, (F1, t1)) = transProgS ((Psi, env), EP1, W)
          val (P2, (F2, t2)) = transProgS ((Psi, env), EP2, W)
        in
          (T.PairPrg (P1, P2), (T.And (F1, F2), T.comp (t1, t2)))
        end

     | transProgS ((Psi, env), D.AppProg (EP1, EP2), W) =
        let
          val (P1, (T.And (F1, F2), t)) = transProgS ((Psi, env), EP1, W)
          val P2 = transProgIN ((Psi, env), EP2, T.FClo (F1, t), W)
          val (F'', t'', W) = checkForWorld (F2, t, W)
        in
          (T.Redex (P1, T.AppPrg (P2, T.Nil)), (F'', t''))
        end


      | transProgS ((Psi, env), D.Inx (s, EP), W) =  raise Error "Cannot infer existential types"

(*      | transProgS ((Psi, env), D.Lam (s, EP), W) =
        let
          val dec = stringTodec s
          val (I.Decl (Psi', (D, _, _)), P, F) = transProgI (I.Decl (Psi, dec), EP)
          val (F', t', _) = checkForWorld (F, T.id, W)
        in
          (T.Lam (T.UDec D, P), (T.All (D, F'), t'))
        end
*)
      | transProgS ((Psi, env), D.New (s, eP), W)  =
        let
          val _ = print "["
          val G = Names.ctxName (T.coerceCtx Psi)
          val _ = print (Print.ctxToString (I.Null, G) ^ "\n")
          val (U, V) = parseTerm ((Psi, env), s ^ " type")
(*        val _ = print (Print.expToString (G, U) ^ "\n") *)

          fun extract (G, Us) = extractW (G, Whnf.whnf Us)
          and extractW (G, (I.Pi ((I.Dec (_, _), _), V'), s)) =
                extract (I.Decl(G, I.decSub (D, s)), (V', I.dot1 s))
            | extractW (G, _) = G

          val G' = extract (I.Null, (U, I.id))
          val Dlist = T.ctxToBDecs (T.coerceCtx Psi, G', W)

          fun project ((G, env), []) = (env, 1)   (* is this the right starting point --cs *)
            | project ((G, env), x :: N) =
              let
                val (env', k) = project ((G, env), N)
                val U = I.Root (I.Proj (I.Bidx 1, k), I.Nil)
                val V =  TypeCheck.infer' (G, U)
              in
                ((U, V, x) :: env', k+1)
              end

          fun extend ((Psi', env'), []) = (Psi', env')
            | extend ((Psi', env'), (N, D) :: Dlist') =
              let
                val (Psi'', env'') = extend ((Psi', env'),  Dlist')
                val Psi''' = I.Decl (Psi'', T.UDec D)
                val I.BDec (_, (cid, s)) = D
                val G''' = T.coerceCtx Psi'''
                val env''' = map (fn (U, V, name) =>
                    (I.EClo (U, I.shift), I.EClo (V, I.shift), name)) env''
                val (env'''', _) = project ((G''', env'''), N)
              in
                (Psi''',  env'''')
               end

          val (Psi', env') = extend ((Psi, env), Dlist)
          val _ = printCtx (Names.ctxName (T.coerceCtx Psi'), env')

          fun universalClosure ([], F) = F
            | universalClosure ((_, D) :: Ds, F)  = T.All (T.UDec D, universalClosure (Ds, F))

          val (P', (F, t)) = transProgS ((Psi, env), eP, W)
          val F' = T.forSub (F, t)
          val F'' = universalClosure (Dlist, F')
          val P'' = lamClosure (F'', P')
        in
          (P'', (F'', T.id))
        end
*)

  (* transProgram Ds = P

       Invariant:
       If Ds is a list of declarations then P is
       the translated program, that does not do anything
    *)

  let rec transProgram Ds =
    transDecs (I.Null, Ds, fun (Psi, W) -> (T.Unit, T.Worlds []))

  let transFor =
   fun F ->
    let F' = transFor (I.Null, F) in
    F'
  (*    val makePattern = makePattern *)

  (*    val transPro = fn P => let val (P', _) = transProgS ((I.Null, []), P, T.Worlds []) in P' end *)

  let transDecs = transProgram
  let internalizeSig = internalizeSig
  let externalizePrg = fun P -> externalizePrg (0, P)
  (*    val transDecs = fn Ds => transDecs ((I.Null, []), NONE, Ds, fn (Psi,  W) => T.Unit, T.Worlds [])
*)
end

(* functor Trans *)
