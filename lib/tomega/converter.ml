open Basis ;; 
(* Converter from relational representation to a functional
   representation of proof terms *)

(* Author: Carsten Schuermann *)

module type CONVERTER = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure Tomega : Tomega.TOMEGA !*)
  exception Error of string
  exception Error' of Tomega.sub

  val convertFor : IntSyn.cid list -> Tomega.for_sml
  val convertPrg : IntSyn.cid list -> Tomega.prg

  val installPrg :
    IntSyn.cid list ->
    IntSyn.cid * Tomega.lemma list (* projections *) * Tomega.lemma list

  (* selections *)
  val convertGoal : Tomega.dec IntSyn.ctx * IntSyn.exp -> Tomega.prg
end

(* Signature Conv.CONVERTER *)
(* Converter from relational representation to a functional
   representation of proof terms *)

(* Author: Carsten Schuermann *)

module Converter
    (Global : Global.GLOBAL)
    (Abstract : Abstract.ABSTRACT)
    (ModeTable : Modetable.MODETABLE)
    (Names : Names.NAMES)
    (Unify : Unify.UNIFY)
    (Whnf : Whnf.WHNF)
    (Print : Print.PRINT)
    (TomegaPrint : TOMEGAPRINT)
    (WorldSyn : Worldsyn.WORLDSYN)
    (Worldify : Worldify.WORLDIFY)
    (TomegaTypeCheck : TOMEGATYPECHECK)
    (Subordinate : Subordinate.SUBORDINATE)
    (TypeCheck : Typecheck.TYPECHECK)
    (Redundant : Redundant.REDUNDANT)
    (TomegaAbstract : TOMEGAABSTRACT) : Conv.CONVERTER = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  exception Error of string
  exception Error' of Tomega.sub

  module T = Tomega
  module I = IntSyn
  module M = ModeSyn
  module S = Subordinate
  module A = Abstract
  module TA = TomegaAbstract
  (* ABP - 4/20/03, determine if Front is (I.Idx 1) *)

  let rec isIdx1 = function I.Idx 1 -> true | _ -> false

  let rec modeSpine a =
    match ModeTable.modeLookup a with
    | None -> raise (Error "Mode declaration expected")
    | Some mS -> mS

  let rec typeOf a =
    match I.sgnLookup a with
    | I.ConDec (name, _, _, _, V, I.Kind) -> V
    | _ -> raise (Error "Type Constant declaration expected")

  let rec nameOf a =
    match I.sgnLookup a with
    | I.ConDec (name, _, _, _, V, I.Kind) -> name
    | _ -> raise (Error "Type Constant declaration expected")

  let rec chatter chlev f =
    if !Global.chatter >= chlev then print ("[tomega] " ^ f ()) else ()
  (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)

  let rec strengthenExp (U, s) = Whnf.normalize (Whnf.cloInv (U, s), I.id)
  let rec strengthenSub (s, t) = Whnf.compInv (s, t)
  (* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)

  let rec strengthenDec = function
    | I.Dec (name, V), s -> I.Dec (name, strengthenExp (V, s))
    | I.BDec (name, (L, t)), s -> I.BDec (name, (L, strengthenSub (t, s)))
  (* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- w : G1
       then G1 |- G' = G[w^-1] ctx
       and  G0 |- w' : G1, G'
    *)

  let rec strengthenCtx = function
    | I.Null, s -> (I.Null, s)
    | I.Decl (G, D), s ->
        let G', s' = strengthenCtx (G, s) in
        (I.Decl (G', strengthenDec (D, s')), I.dot1 s')
  (* strengthenFor (F, s) = F'

       If   Psi0 |- F for_sml
       and  Psi0 |- s :: Psi1
       then Psi1 |- F' = F[s^-1] ctx
    *)

  let rec strengthenFor = function
    | T.True, s -> T.True
    | T.And (F1, F2), s -> T.And (strengthenFor (F1, s), strengthenFor (F2, s))
    | T.All ((T.UDec D, Q), F), s ->
        T.All ((T.UDec (strengthenDec (D, s)), Q), strengthenFor (F, I.dot1 s))
    | T.Ex ((D, Q), F), s ->
        T.Ex ((strengthenDec (D, s), Q), strengthenFor (F, I.dot1 s))
  (* strengthenOrder (O, s) = O'

       If   Psi0 |- O order
       and  Psi0 |- s :: Psi1
       then Psi1 |- O' = O[s^-1] ctx
    *)

  let rec strengthenOrder = function
    | Order.Arg ((U, s1), (V, s2)), s ->
        Order.Arg ((U, strengthenSub (s1, s)), (V, strengthenSub (s2, s)))
    | Order.Simul Os, s ->
        Order.Simul (map (fun O -> strengthenOrder (O, s)) Os)
    | Order.Lex Os, s -> Order.Lex (map (fun O -> strengthenOrder (O, s)) Os)
  (* strengthenTC (TC, s) = TC'

       If   Psi0 |- TC : termination condition
       and  Psi0 |- s :: Psi1
       then Psi1 |- TC' = TC[s^-1] ctx
    *)

  let rec strengthenTC = function
    | T.Base O, s -> T.Base (strengthenOrder (O, s))
    | T.Conj (TC1, TC2), s ->
        T.Conj (strengthenTC (TC1, s), strengthenTC (TC2, s))
    | T.Abs (D, TC), s ->
        T.Abs (strengthenDec (D, s), strengthenTC (TC, I.dot1 s))

  let rec strengthenSpine = function
    | I.Nil, t -> I.Nil
    | I.App (U, S), t -> I.App (strengthenExp (U, t), strengthenSpine (S, t))
  (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s :: Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' :: Psi1, Psi'
    *)

  let rec strengthenPsi = function
    | I.Null, s -> (I.Null, s)
    | I.Decl (Psi, T.UDec D), s ->
        let Psi', s' = strengthenPsi (Psi, s) in
        (I.Decl (Psi', T.UDec (strengthenDec (D, s'))), I.dot1 s')
    | I.Decl (Psi, T.PDec (name, F, None, None)), s ->
        let Psi', s' = strengthenPsi (Psi, s) in
        ( I.Decl (Psi', T.PDec (name, strengthenFor (F, s'), None, None)),
          I.dot1 s' )
  (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)

  let rec strengthenPsi' = function
    | [], s -> ([], s)
    | T.UDec D :: Psi, s ->
        let D' = strengthenDec (D, s) in
        let s' = I.dot1 s in
        let Psi'', s'' = strengthenPsi' (Psi, s') in
        (T.UDec D' :: Psi'', s'')
  (* ctxSub (G, s) = (G', s')

       Invariant:
       if   Psi |- G ctx
       and  Psi' |- s : Psi
       then Psi' |- G' ctx
       and  Psi', G' |- s' : G
       and  G' = G [s],  declarationwise defined
    *)

  let rec ctxSub = function
    | I.Null, s -> (I.Null, s)
    | I.Decl (G, D), s ->
        let G', s' = ctxSub (G, s) in
        (I.Decl (G', I.decSub (D, s')), I.dot1 s)

  let rec validMode = function
    | M.Mnil -> ()
    | M.Mapp (M.Marg (M.Plus, _), mS) -> validMode mS
    | M.Mapp (M.Marg (M.Minus, _), mS) -> validMode mS
    | M.Mapp (M.Marg (M.Star, _), mS) ->
        raise (Error "+ or - mode expected, * found")

  let rec validSig = function
    | Psi0, [] -> ()
    | Psi0, (G, V) :: Sig ->
        let rec append = function
          | G, I.Null -> G
          | G, I.Decl (G', D) -> I.Decl (append (G, G'), D)
        in
        TypeCheck.typeCheck
          (T.coerceCtx (append (Psi0, T.embedCtx G)), (V, I.Uni I.Type));
        validSig (Psi0, Sig)

  let rec convertOneFor cid =
    (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for_sml G'
           then F'  is a formula excepting a another argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
    (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
    let V =
      match I.sgnLookup cid with
      | I.ConDec (name, _, _, _, V, I.Kind) -> V
      | _ -> raise (Error "Type Constant declaration expected")
    in
    let mS =
      match ModeTable.modeLookup cid with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS
    in
    let _ = validMode mS in
    let rec convertFor' = function
      | I.Pi ((D, _), V), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n ->
          let F', F'' =
            convertFor' (V, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n - 1)
          in
          fun F ->
            (T.All ((T.UDec (strengthenDec (D, w1)), T.Explicit), F' F), F'')
      | I.Pi ((D, _), V), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n ->
          let F', F'' =
            convertFor' (V, mS, I.comp (w1, I.shift), I.dot1 w2, n + 1)
          in
          (F', T.Ex ((I.decSub (D, w2), T.Explicit), F''))
      | I.Uni I.Type, M.Mnil, _, _, _ -> fun F -> (F, T.True)
      | _ -> raise (Error "type family must be +/- moded")
    in
    let rec shiftPlus mS =
      let rec shiftPlus' = function
        | M.Mnil, n -> n
        | M.Mapp (M.Marg (M.Plus, _), mS'), n -> shiftPlus' (mS', n + 1)
        | M.Mapp (M.Marg (M.Minus, _), mS'), n -> shiftPlus' (mS', n)
      in
      shiftPlus' (mS, 0)
    in
    let n = shiftPlus mS in
    let F, F' = convertFor' (V, mS, I.id, I.Shift n, n) in
    F F'
  (* createIH L = (Psi', P', F')

       Invariant:
       If   L is a list of type families
       and  Psi is a context
       then Psi' extends Psi' by declarations in L
       and  F' is the conjunction of the formuals
            that corresponds to each type family in L
       and  Psi' |- P' in F'
    *)

  let rec createIH = function
    | [] -> raise (Error "Empty theorem")
    | [ a ] ->
        let name = I.conDecName (I.sgnLookup a) in
        let F = convertOneFor a in
        (name, F)
    | a :: L ->
        let name = I.conDecName (I.sgnLookup a) in
        let F = convertOneFor a in
        let name', F' = createIH L in
        (name ^ "/" ^ name', T.And (F, F'))

  let rec convertFor L =
    let _, F' = createIH L in
    F'
  (* occursInExpN (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)

  let rec occursInExpN = function
    | k, I.Uni _ -> false
    | k, I.Pi (DP, V) -> occursInDecP (k, DP) || occursInExpN (k + 1, V)
    | k, I.Root (H, S) -> occursInHead (k, H) || occursInSpine (k, S)
    | k, I.Lam (D, V) -> occursInDec (k, D) || occursInExpN (k + 1, V)
    | k, I.FgnExp csfe ->
        I.FgnExpStd.fold csfe
          (fun (U, DP) -> DP || occursInExp (k, Whnf.normalize (U, I.id)))
          false

  and occursInHead = function
    | k, I.BVar k' -> k = k'
    | k, I.Const _ -> false
    | k, I.Def _ -> false
    | k, I.FgnConst _ -> false
    | k, I.Proj _ -> false

  and occursInSpine = function
    | _, I.Nil -> false
    | k, I.App (U, S) -> occursInExpN (k, U) || occursInSpine (k, S)

  and occursInDec (k, I.Dec (_, V)) = occursInExpN (k, V)
  and occursInDecP (k, (D, _)) = occursInDec (k, D)
  and occursInExp (k, U) = occursInExpN (k, Whnf.normalize (U, I.id))
  (* dot1inv w = w'

       Invariant:
       If   G, A |- w : G', A
       then G |- w' : G'
       and  w = 1.w' o ^
    *)

  let rec dot1inv w = strengthenSub (I.comp (I.shift, w), I.shift)
  (* shiftinv (w) = w'

       Invariant:
       If   G, A |- w : G'
       and  1 does not occur in w
       then w  = w' o ^
    *)

  let rec shiftinv w = strengthenSub (w, I.shift)
  let rec peel w = if isIdx1 (I.bvarSub (1, w)) then dot1inv w else shiftinv w
  let rec peeln = function 0, w -> w | n, w -> peeln (n - 1, peel w)

  let rec popn = function
    | 0, Psi -> (Psi, I.Null)
    | n, I.Decl (Psi, T.UDec D) ->
        let Psi', G' = popn (n - 1, Psi) in
        (Psi', I.Decl (G', D))
  (* domain (G2, w) = n'

       Invariant:
       If   G2 |- w: G1   and w weakening substitution
       then n' = |G1|
    *)

  let rec domain = function
    | G, I.Dot (I.Idx _, s) -> domain (G, s) + 1
    | I.Null, I.Shift 0 -> 0
    | G, I.Shift 0 -> domain (G, I.Dot (I.Idx 1, I.Shift 1))
    | I.Decl (G, _), I.Shift n -> domain (G, I.Shift (n - 1))
  (* strengthen (Psi, (a, S), w, m) = (Psi', w')

       This function traverses the spine, and finds
       all variables in a position input/output position m
       (hence strenghten might not be a good name for_sml it, because it is to general.)

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1 (but is a subset of Psi?)
    *)

  let rec strengthen (Psi, (a, S), w, m) =
    (* testBlock (G, (bw, w1)) = (bw', w')

           Invariant:
           If   |- G ctx
           and  |- G1 ctx
           and  |- G2 ctx
           and  G1 |- w1 : G2, G
           and  bw is a boolean value
           then there ex. a G1'
           s.t. |- G1' ctx
           and  G1' |- w' : G2
           and  bw' = bw or (G1 =/= G1')
         *)
    (* strengthen' (Psi1, Psi2, S, w1) =  (Psi', w')

           Invariant:
           If   |- Psi1 ctx
           and  Psi1 |- Psi2 ctx      (Psi2 is a list to maintain order)
           and  |- Psi3 ctx
           and  Psi1 |- w1 : Psi3     where w1 is a weakening substitution
           and  Psi1, Psi2 |- S : V1 > V2
           then |- Psi' ctx
           and  Psi1 |- w' : Psi'     where w' is a weakening substitution
           where Psi3 < Psi' < Psi1   (Psi' contains all variables of Psi3
                                       and all variables occuring in m
                                       position in S)
        *)
    let mS = modeSpine a in
    let rec args = function
      | I.Nil, M.Mnil -> []
      | I.App (U, S'), M.Mapp (M.Marg (m', _), mS) -> (
          let L = args (S', mS) in
          match M.modeEqual (m, m') with true -> U :: L | false -> L)
    in
    let rec strengthenArgs = function
      | [], s -> []
      | U :: L, s -> strengthenExp (U, s) :: strengthenArgs (L, s)
    in
    let rec occursInArgs = function
      | n, [] -> false
      | n, U :: L -> occursInExp (n, U) || occursInArgs (n, L)
    in
    let rec occursInPsi = function
      | n, ([], L) -> occursInArgs (n, L)
      | n, (T.UDec (I.Dec (_, V)) :: Psi1, L) ->
          occursInExp (n, V) || occursInPsi (n + 1, (Psi1, L))
      | n, (T.UDec (I.BDec (_, (cid, s))) :: Psi1, L) ->
          let (I.BlockDec (_, _, G, _)) = I.sgnLookup cid in
          occursInSub (n, s, G) || occursInPsi (n + 1, (Psi1, L))
    and occursInSub = function
      | _, _, I.Null -> false
      | n, I.Shift k, G ->
          occursInSub (n, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), G)
      | n, I.Dot (I.Idx k, s), I.Decl (G, _) -> n = k || occursInSub (n, s, G)
      | n, I.Dot (I.Exp U, s), I.Decl (G, _) ->
          occursInExp (n, U) || occursInSub (n, s, G)
      | n, I.Dot (I.Block _, s), I.Decl (G, _) -> occursInSub (n, s, G)
    and occursInG = function
      | n, I.Null, k -> k n
      | n, I.Decl (G, I.Dec (_, V)), k ->
          occursInG (n, G, fun n' -> occursInExp (n', V) || k (n' + 1))
    in
    let rec occursBlock (G, (Psi2, L)) =
      let rec occursBlock = function
        | I.Null, n -> false
        | I.Decl (G, D), n ->
            occursInPsi (n, (Psi2, L)) || occursBlock (G, n + 1)
      in
      occursBlock (G, 1)
    in
    let rec inBlock = function
      | I.Null, (bw, w1) -> (bw, w1)
      | I.Decl (G, D), (bw, w1) ->
          if isIdx1 (I.bvarSub (1, w1)) then inBlock (G, (true, dot1inv w1))
          else inBlock (G, (bw, strengthenSub (w1, I.shift)))
    in
    let rec blockSub = function
      | I.Null, w -> (I.Null, w)
      | I.Decl (G, I.Dec (name, V)), w ->
          let G', w' = blockSub (G, w) in
          let V' = strengthenExp (V, w') in
          (I.Decl (G', I.Dec (name, V')), I.dot1 w')
    in
    let rec strengthen' = function
      | I.Null, Psi2, L, w1 (* =  I.id *) -> (I.Null, I.id, I.id)
      | I.Decl (Psi1, LD), Psi2, L, w1 ->
          if isIdx1 (I.bvarSub (1, w1)) then
            let w1' = dot1inv w1 in
            let Psi1', w', z' = strengthen' (Psi1, LD :: Psi2, L, w1') in
            let V' = strengthenExp (V, w') in
            (I.Decl (Psi1', T.UDec (I.Dec (name, V'))), I.dot1 w', I.dot1 z')
          else if occursInPsi (1, (Psi2, L)) then
            let w1' = strengthenSub (w1, I.shift) in
            let Psi1', w', z' = strengthen' (Psi1, LD :: Psi2, L, w1') in
            let V' = strengthenExp (V, w') in
            ( I.Decl (Psi1', T.UDec (I.Dec (name, V'))),
              I.dot1 w',
              I.comp (z', I.shift) )
          else
            let w1' = strengthenSub (w1, I.shift) in
            let w2 = I.shift in
            let Psi2', w2' = strengthenPsi' (Psi2, w2) in
            let L' = strengthenArgs (L, w2') in
            let Psi1'', w', z' = strengthen' (Psi1, Psi2', L', w1') in
            (Psi1'', I.comp (w', I.shift), z')
      | I.Decl (Psi1, D), Psi2, L, w1 ->
          let w1' = dot1inv w1 in
          let Psi1', w', z' = strengthen' (Psi1, D :: Psi2, L, w1') in
          let F' = strengthenFor (F, w') in
          (I.Decl (Psi1', T.PDec (name, F', None, None)), I.dot1 w', I.dot1 z')
      | I.Decl (Psi1, LD), Psi2, L, w1 ->
          (* blocks are always used! *)
          let w1' = dot1inv w1 in
          let Psi1', w', z' = strengthen' (Psi1, LD :: Psi2, L, w1') in
          let s' = strengthenSub (s, w') in
          ( I.Decl (Psi1', T.UDec (I.BDec (name, (cid, s')))),
            I.dot1 w',
            I.dot1 z' )
    in
    strengthen' (Psi, [], args (S, mS), w)

  let rec lookupIH (Psi, L, a) =
    let rec lookupIH' (b :: L, a, k) =
      if a = b then k else lookupIH' (L, a, k - 1)
    in
    lookupIH' (L, a, I.ctxLength Psi)
  (* createSub (Psi, L) = t'

       Invariant:
       If  |- Psi = Psi0, Psi1 ctx
       and Psi0 contains all declarations for_sml invariants in L
       and |Psi0| = n
       and |L| = k
       and n = k + m - 1
       then Psi |- t' = m, m+1 ... n. ^n :  Psi0
    *)

  let rec createIHSub (Psi, L) = T.Shift (I.ctxLength Psi - 1 (*List.length L *))
  (* transformInit (Psi, (a, S), w1) = (w', s')

       Invariant:
       If   |- Psi ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w1 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi+ |- s' : Gamma+
       and  x1:A1 .. xn:An |- w: Gamma+    (w weakening substitution)
    *)

  let rec transformInit (Psi, L, (a, S), w1) =
    (* transformInit' ((S, mS), V, (w, s)) = (w', s')

           Invariant:
           If   Psi |- S : V > type
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *)
    let mS = modeSpine a in
    let V = typeOf a in
    let rec transformInit' = function
      | (I.Nil, M.Mnil), I.Uni I.Type, (w, s) -> (w, s)
      | (I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS)), I.Pi (_, V2), (w, s)
        ->
          let w' = I.comp (w, I.shift) in
          let s' = s in
          transformInit' ((S, mS), V2, (w', s'))
      | ( (I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS)),
          I.Pi ((I.Dec (name, V1), _), V2),
          (w, s) ) ->
          let V1' = strengthenExp (V1, w) in
          let w' = I.dot1 w in
          let U' = strengthenExp (U, w1) in
          let s' = T.dotEta (T.Exp U', s) in
          transformInit' ((S, mS), V2, (w', s'))
    in
    transformInit' ((S, mS), V, (I.id, createIHSub (Psi, L)))
  (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)

  let rec transformConc ((a, S), w) =
    let rec transformConc' = function
      | I.Nil, M.Mnil -> T.Unit
      | I.App (U, S'), M.Mapp (M.Marg (M.Plus, _), mS') ->
          transformConc' (S', mS')
      | I.App (U, S'), M.Mapp (M.Marg (M.Minus, _), mS') ->
          T.PairExp (strengthenExp (U, w), transformConc' (S', mS'))
    in
    transformConc' (S, modeSpine a)
  (* renameExp f U = U'

       Invariant:
       U' = U module application of f to any projectoin contained
       in U.
    *)

  let rec renameExp = function
    | f, U -> U
    | f, I.Pi ((D, DP), V) -> I.Pi ((renameDec f D, DP), renameExp f V)
    | f, I.Root (H, S) -> I.Root (renameHead f H, renameSpine f S)
    | f, I.Lam (D, U) -> I.Lam (renameDec f D, renameExp f U)

  and renameDec f (I.Dec (x, V)) = I.Dec (x, renameExp f V)
  and renameHead = function f, I.Proj bi -> f bi | f, H -> H

  and renameSpine = function
    | f, I.Nil -> I.Nil
    | f, I.App (U, S) -> I.App (renameExp f U, renameSpine f S)

  let rec rename (I.BDec (_, (c, s)), V) =
    let G, L = I.constBlock c in
    let rec makeSubst = function
      | n, G, s, [], f -> (G, f)
      | n, G, s, D :: L, f ->
          if Subordinate.belowEq (I.targetFam V', I.targetFam V) then
            makeSubst (n + 1, I.Decl (G, I.decSub (D, s)), I.dot1 s, L, f)
          else makeSubst (n, G, I.comp (s, I.shift), L, f)
    in
    let G', f = makeSubst (1, G, s, L, fun x -> I.Proj x) in
    (G, renameExp f V)

  let rec append = function
    | G, I.Null -> G
    | G, I.Decl (G', D) -> I.Decl (append (G, G'), D)
  (* traverseNeg (L, wmap, projs)  (Psi0, Psi, V) = ([w', PQ'], L')    [] means optional

           Invariant:
           If   |- Psi0 ctx      (context that contains induction hypotheses)
           and  Psi0 |- Psi ctx  (context of all assumptions)
           and  Psi0, Psi |- V : type
           then L' list of cases
           and  Psi0, Psi |- w' : Psi0, Psi'
           and  PQ'  is a pair that can generate a proof term
        *)

  let rec traverseNeg = function
    | (L, wmap, projs), ((Psi0, Psi), I.Pi ((D, I.Maybe), V2), w) -> (
        match
          traverseNeg (L, wmap, projs)
            ((Psi0, I.Decl (Psi, T.UDec D)), V2, I.dot1 w)
        with
        | Some (w', PQ') -> Some (peel w', PQ'))
    | (L, wmap, projs), ((Psi0, Psi), I.Pi ((D, I.No), V2), w) -> (
        match
          traverseNeg (L, wmap, projs)
            ((Psi0, I.Decl (Psi, T.UDec D)), V2, I.comp (w, I.shift))
        with
        | Some (w', PQ') ->
            traversePos (L, wmap, projs)
              ((Psi0, Psi, I.Null), V1, Some (peel w', PQ')))
    | (L, wmap, projs), ((Psi0, Psi), I.Root (I.Const a, S), w) ->
        (* Psi1 = Psi0, Psi *)
        (* Psi1 |- w0 : Psi0 *)
        (* |- Psi' ctx *)
        (* Psi1 |- w' : Psi' *)
        (* Psi' |- s'' : G+ *)
        (* G |- w'' : G+ *)
        let Psi1 = append (Psi0, Psi) in
        let w0 = I.Shift (I.ctxLength Psi) in
        let Psi', w', _ = strengthen (Psi1, (a, S), w0, M.Plus) in
        let w'', s'' = transformInit (Psi', L, (a, S), w') in
        let _ = TomegaTypeCheck.checkCtx Psi' in
        Some (w', fun P -> ((Psi', s'', P), transformConc ((a, S), w)))

  and traversePos = function
    | (L, wmap, projs), ((Psi0, Psi, G), I.Pi ((D, _), V), Some (w1, (P, Q))) ->
        let c' = wmap c in
        let n = I.ctxLength Psi0 + I.ctxLength G in
        let Gsome, Lpi = I.constBlock c in
        let _ =
          TypeCheck.typeCheckCtx
            (T.coerceCtx (append (append (Psi0, Psi), T.embedCtx G)))
        in
        let _ =
          TypeCheck.typeCheckSub
            (T.coerceCtx (append (append (Psi0, Psi), T.embedCtx G)), s, Gsome)
        in
        let Gsome', Lpi' = I.constBlock c' in
        let _ =
          TypeCheck.typeCheckCtx
            (T.coerceCtx (append (append (Psi0, Psi), T.embedCtx G)))
        in
        let _ =
          TypeCheck.typeCheckSub
            (T.coerceCtx (append (append (Psi0, Psi), T.embedCtx G)), s, Gsome')
        in
        traversePos (L, wmap, projs)
          ( (Psi0, Psi, I.Decl (G (* T.UDec *), I.BDec (x, (c', s)))),
            V,
            Some (I.dot1 w1, (P, Q)) )
    | (L, wmap, projs), ((Psi0, G, B), V, Some (w1, (P, Q))) ->
        (* Psi1 = Psi0, G, B *)
        (* n = |Psi0, G', B'| *)
        (* m = |Psi0| *)
        (* strengthened invariant Psi0 might be empty --cs Fri Apr 11 15:25:32 2003 *)
        (* apply ((S, mS), F')= (S'', F'')

                 Invariant:
                 Psi0, G, B |- S : V >> type
                   (mS is the corresponding mode spine)
                 and  Psi0, G', B |- F'  :: for_sml
                 then Psi0, G', B |- F'' :: for_sml
                 and  Psi0, G', B |- S'' :: F' >> F''
              *)
        (* Psi0, G', B' |- F'' :: for_sml *)
        (* Psi0, G', B' |- S'' :: F' >> F'' *)
        (* was T.Root  -cs Sun Jan  5 23:15:06 2003 *)
        (* Psi0, G', B' |- P'' :: F'' *)
        (* b = |B| = |B'| *)
        (* Psi0, G |- w1' : Psi0, G' *)
        (* |- Psi0, G', B' ctx *)
        (* n' = |Psi0, G'| *)
        (* Psi0, G' |- GB' ctx *)
        (* Psi0, G, B |- w1 : Psi0, G', B' *)
        (* Psi0, G', GB'  |- s' : Psi0, G', B' *)
        (* Psi0, G', GB' |- RR for_sml *)
        (* Psi0, G |- w1' : Psi0, G' *)
        (* Psi0, G' |- F''' for_sml *)
        (* lift (B, (P, F)) = (P', F')

                 Invariant:
                 If   Psi0, G, B |- P :: F
                 then Psi0, G |- P'  :: F'
                 and  P' =  (lam B. P)
                 and  F' = raiseFor (B, F)
              *)
        (* Psi0, G' |- P''' :: F''' *)
        (* |- Psi0, Psi1'' ctx *)
        (* Psi0, G, B |- w2 : Psi1'' *)
        (* Psi1'' = Psi0, G3, B3' *)
        (* |B| = |GB'| *)
        (* Psi'' |-  z2 : Psi0, G', B' *)
        (* Psi0, G, B |- w2 : Psi0, G3, B3' *)
        (* Psi0, G |- w3 : Psi0, G3 *)
        (* Psi0, G3 |-  z3 : Psi0, G' *)
        (* Psi2 = Psi0, G3 *)
        (* Psi0, G3, B3' |- Pat' :: For *)
        (* Psi0, G3 |- F4 for_sml *)
        (* ' F4 *)
        (* Psi0, G3 |- Pat :: F4  *)
        (* Here's a commutative diagram
                                           at work which one has to prove
                                           correct
                                        *)
        (* Psi0, G3 |- t :: Psi0, G', x :: F4  *)
        let Psi1 = append (Psi0, append (G, T.embedCtx B)) in
        let _ =
          TomegaTypeCheck.checkCtx (append (append (Psi0, G), T.embedCtx B))
        in
        let n = domain (Psi1, w1) in
        let m = I.ctxLength Psi0 in
        let rec lookupbase a =
          let s = I.conDecName (I.sgnLookup a) in
          let l = T.lemmaName s in
          let (T.ValDec (_, P, F)) = T.lemmaLookup l in
          (T.Const l, F)
        in
        let rec lookup = function
          | ([ b ], None, F), a ->
              if a = b then
                let P = T.Var n in
                (P, F)
              else lookupbase a
          | ([ b ], Some [ lemma ], F), a ->
              if a = b then
                let P = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil)) in
                (P, F)
              else lookupbase a
          | (b :: L, Some (lemma :: lemmas), T.And (F1, F2)), a ->
              if a = b then
                let P = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil)) in
                (P, F1)
              else lookup ((L, Some lemmas, F2), a)
        in
        let HP, F =
          if I.ctxLength Psi0 > 0 then
            let (T.PDec (_, F0, _, _)) = I.ctxLookup (Psi0, 1) in
            lookup ((L, projs, F0), a)
          else lookupbase a
        in
        let rec apply ((S, mS), Ft) = applyW ((S, mS), T.whnfFor Ft)
        and applyW = function
          | (I.Nil, M.Mnil), Ft' -> (T.Nil, T.forSub Ft')
          | (I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS)), (T.All (D, F'), t')
            ->
              (* Psi0, G', B' |- U' : V' *)
              (* Psi0, G', B' |- F'' :: for_sml *)
              (* Psi0, G', B' |- S'' : F' [t'] >> F'' *)
              let U' = strengthenExp (U, w1) in
              let S'', F'' = apply ((S, mS), (F', T.Dot (T.Exp U', t'))) in
              (T.AppExp (U', S''), F'')
              (* Psi0, G', B' |- U' ; S''
                                                       : all {x:V'} F' >> F'' *)
          | (I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS)), Ft ->
              applyW ((S, mS), Ft)
        in
        let S'', F'' = apply ((S, modeSpine a), (F, T.id)) in
        let _ =
          TomegaTypeCheck.checkFor
            ( append (append (Psi0, G), T.embedCtx B),
              T.forSub (F'', T.embedSub w1) )
        in
        let P'' = T.Redex (HP (*T.Var k' *), S'') in
        let b = I.ctxLength B in
        let w1' = peeln (b, w1) in
        let B', _ = strengthenCtx (B, w1') in
        let n' = n - I.ctxLength B' in
        let rec subCtx = function
          | I.Null, s -> (I.Null, s)
          | I.Decl (G, D), s ->
              let G', s' = subCtx (G, s) in
              (I.Decl (G', I.decSub (D, s')), I.dot1 s')
        in
        let B'', _ = subCtx (B', w1') in
        let _ =
          TomegaTypeCheck.checkCtx (append (append (Psi0, G), T.embedCtx B''))
        in
        let GB', iota = T.deblockify B' in
        let _ =
          try TypeCheck.typeCheckSub (GB', T.coerceSub iota, B')
          with TypeCheck.Error _ -> raise (Error' iota)
        in
        let RR = T.forSub (F'', iota) in
        let F''' = TA.raiseFor (GB', (RR, I.id)) in
        let rec lift = function
          | I.Null, P -> P
          | I.Decl (G, D), P ->
              let Bint, _ = T.deblockify (I.Decl (I.Null, D)) in
              lift (G, T.New (T.Lam (T.UDec D, P)))
        in
        let P''' = lift (B', P'') in
        let _ = TomegaTypeCheck.checkCtx (append (Psi0, G)) in
        let _ =
          TomegaTypeCheck.checkFor
            (append (Psi0, G), T.forSub (F''', T.embedSub w1'))
        in
        let Psi1'', w2, z2 = strengthen (Psi1, (a, S), w1, M.Minus) in
        let w3 = peeln (b, w2) in
        let z3 = peeln (b, z2) in
        let Psi2, B3' = popn (b, Psi1'') in
        let Pat' = transformConc ((a, S), w2) in
        let F4 = T.forSub (F''', T.embedSub z3) in
        let _ = TomegaTypeCheck.checkCtx Psi1'' in
        let _ = TomegaTypeCheck.checkCtx (append (Psi2, T.embedCtx B3')) in
        let _ =
          try TomegaTypeCheck.checkFor (Psi2, F4) with _ -> raise (Error "")
        in
        let B3, sigma3 = T.deblockify B3' in
        let Pat'' = T.normalizePrg (Pat', sigma3) in
        let Pat = TA.raisePrg (B3, Pat'', F4) in
        let _ = TomegaTypeCheck.checkPrg (Psi2, (Pat, F4)) in
        let t = T.Dot (T.Prg Pat, T.embedSub z3) in
        Some
          ( w3,
            fun p ->
              ( P
                  (T.Let
                     ( T.PDec (None, F''', None, None),
                       P''',
                       T.Case (T.Cases [ (Psi2, t, p) ]) )),
                Q ) )
  (* traverse (Psi0, L, Sig, wmap) = C'

       Invariant:
       If   |- Psi0  ctx
       and  L is a the theorem we would like to transform
       and  Sig is a signature
       and  forall (G, V) in Sig the following holds:
                    Psi0, G |- V : type
               and  head (V) in L
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
       then C' is a list of cases (corresponding to each (G, V) in Sig)
    *)

  let rec traverse (Psi0, L, Sig, wmap, projs) =
    let rec traverseSig' = function
      | [] -> []
      | (G, V) :: Sig -> (
          TypeCheck.typeCheck (append (T.coerceCtx Psi0, G), (V, I.Uni I.Type));
          match
            traverseNeg (L, wmap, projs) ((Psi0, T.embedCtx G), V, I.id)
          with
          | Some (wf, (P', Q')) -> traverseSig' Sig @ [ P' Q' ])
    in
    traverseSig' Sig
  (* transformWorlds (fams, W) = (W', wmap)

       Invariant:
       If   fams is the theorem to be compiled
       and  W a world with declarations,
       then W' is the new world stripped of all dynamic extensions
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
    *)

  let rec transformWorlds (fams, T.Worlds cids) =
    (* convertList (a, L, w) = L'

             Invariant:
             If   G0 |- G, L : ctx
             and  G0, G |- w : G0, G'
             then G0 |- G', L' ctx
          *)
    let rec transformList = function
      | [], w -> []
      | D :: L, w ->
          if
            List.foldr
              (fun (a, b) -> b && Subordinate.belowEq (a, I.targetFam V))
              true fams
          then transformList (L, I.comp (w, I.shift))
          else
            let L' = transformList (L, I.dot1 w) in
            I.Dec (x, strengthenExp (V, w)) :: L'
    in
    let rec transformWorlds' = function
      | [] -> ([], fun c -> raise (Error "World not found"))
      | cid :: cids' ->
          (* Design decision: Let's keep all of G *)
          let (I.BlockDec (s, m, G, L)) = I.sgnLookup cid in
          let L' = transformList (L, I.id) in
          let cids'', wmap = transformWorlds' cids' in
          let cid' = I.sgnAdd (I.BlockDec (s, m, G, L')) in
          (cid' :: cids'', fun c -> if c = cid then cid' else wmap c)
    in
    let cids', wmap = transformWorlds' cids in
    (T.Worlds cids', wmap)
  (* dynamicSig (Psi0, fams, W) = Sig'

       Invariant:
       If   |- Psi0 ctx
       and  fams are the typfamilies to be converted
       and  W is the world in which the translation takes place
       then Sig' = (G1;V1) ... (Gn;Vn)
       and  |- Psi0, Gi ctx
       and  Psi, Gi |- Vi : type.
    *)

  let rec dynamicSig (Psi0, a, T.Worlds cids) =
    (* findDec (G, n, L, s, S) = S'

             Invariant:
             If   G |-  L : ctx
             and  G |- w: G'
             then |- G', L' ctx
          *)
    (* mediateSub G = (G0, s)

             Invariant:
             If   . |- G ctx
             then Psi0 |- G0 ctx
             and  Psi0, G0 |- s : G
          *)
    let rec findDec = function
      | G, _, [], w, Sig -> Sig
      | G, n, D :: L, w, Sig ->
          let D' = I.decSub (D, w) in
          let b = I.targetFam V' in
          let Sig' =
            if b = a then (G, Whnf.normalize (V', I.id)) :: Sig else Sig
          in
          findDec
            ( G,
              n + 1,
              L,
              I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, n), I.Nil)), w),
              Sig' )
    in
    let rec mediateSub = function
      | I.Null -> (I.Null, I.Shift (I.ctxLength Psi0))
      | I.Decl (G, D) ->
          let G0, s' = mediateSub G in
          let D' = I.decSub (D, s') in
          (I.Decl (G0, D'), I.dot1 s')
    in
    let rec findDecs' = function
      | [], Sig -> Sig
      | cid :: cids', Sig ->
          (* G |- L ctx *)
          (* Psi0, G0 |- s'' : G *)
          (* Psi0, G0 |- D : dec *)
          (* Psi0, G0, D' |- s'' : G *)
          let (I.BlockDec (s, m, G, L)) = I.sgnLookup cid in
          let G0, s' = mediateSub G in
          let D' = Names.decName (G0, I.BDec (None, (cid, s'))) in
          let s'' = I.comp (s', I.shift) in
          let Sig' = findDec (I.Decl (G0, D'), 1, L, s'', Sig) in
          findDecs' (cids', Sig')
    in
    findDecs' (cids, [])
  (* staticSig Sig = Sig'

       Invariant:
       If   |- Psi0 ctx
       then Sig' = (c1:V1) ... (cn:Vn)
       and  . |- Vi : type.
    *)

  let rec staticSig = function
    | Psi0, [] -> []
    | Psi0, I.ConDec (name, _, _, _, V, I.Type) :: Sig ->
        (I.Null, Whnf.normalize (V, I.Shift (I.ctxLength Psi0)))
        :: staticSig (Psi0, Sig)

  let rec name = function
    | [ a ] -> I.conDecName (I.sgnLookup a)
    | a :: L -> I.conDecName (I.sgnLookup a) ^ "/" ^ name L
  (* convertPrg L = P'

       Invariant:
       If   L is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in L into functional form
    *)

  let rec convertPrg (L, projs) =
    let name, F0 = createIH L in
    let D0 = T.PDec (Some name, F0, None, None) in
    let Psi0 = I.Decl (I.Null, D0) in
    let Prec = fun p -> T.Rec (D0, p) in
    let rec convertWorlds = function
      | [ a ] ->
          (* W describes the world of a *)
          let W = WorldSyn.lookup a in
          W
      | a :: L' ->
          (* W describes the world of a *)
          let W = WorldSyn.lookup a in
          let W' = convertWorlds L' in
          if T.eqWorlds (W, W') then W'
          else raise (Error "Type families different in different worlds")
    in
    let W = convertWorlds L in
    let W', wmap = transformWorlds (L, W) in
    let rec convertOnePrg (a, F) =
      (* Psi0 |- {x1:V1} ... {xn:Vn} type *)
      (* |- mS : {x1:V1} ... {xn:Vn} > type *)
      (* Sig in LF(reg)   *)
      (* init' F = P'

               Invariant:
               If   F = All x1:A1. ... All xn:An. F'
               and  f' does not start with a universal quantifier
               then P' P'' = Lam x1:A1. ... Lam xn:An P''
                    for_sml any P''
            *)
      (* Psi0, x1:V1, ..., xn:Vn |- C :: F *)
      let name = nameOf a in
      let V = typeOf a in
      let mS = modeSpine a in
      let Sig = Worldify.worldify a in
      let dynSig = dynamicSig (Psi0, a, W) in
      let statSig = staticSig (Psi0, Sig) in
      let _ =
        map
          (fun (I.ConDec (_, _, _, _, U, V)) -> TypeCheck.check (U, I.Uni V))
          Sig
      in
      let _ = validSig (Psi0, statSig) in
      let _ = validSig (Psi0, dynSig) in
      let C0 = traverse (Psi0, L, dynSig, wmap, projs) in
      let rec init = function
        | T.All ((D, _), F') ->
            let F'', P' = init F' in
            (F'', fun p -> T.Lam (D, P' p))
        | F' -> (F', fun p -> p)
      in
      let F', Pinit = init F in
      let C = traverse (Psi0, L, statSig, wmap, projs) in
      Pinit
        (T.Case
           ((* F', *)
              T.Cases
              (C0 @ C)))
    in
    let rec convertPrg' = function
      | [], _ -> raise (Error "Cannot convert Empty program")
      | [ a ], F -> convertOnePrg (a, F)
      | a :: L', T.And (F1, F2) ->
          T.PairPrg (convertOnePrg (a, F1), convertPrg' (L', F2))
    in
    let P = Prec (convertPrg' (L, F0)) in
    P

  let rec installFor [ cid ] =
    let F = convertFor [ cid ] in
    let name = I.conDecName (I.sgnLookup cid) in
    let _ = T.lemmaAdd (T.ForDec (name, F)) in
    ()

  let rec depthConj = function T.And (F1, F2) -> 1 + depthConj F2 | F -> 1

  let rec createProjection = function
    | Psi, depth, F, Pattern ->
        createProjection
          ( I.Decl (Psi, T.PDec (None, F1, None, None)),
            depth + 1,
            T.forSub (F2, T.Shift 1),
            T.PairPrg (T.Var (depth + 2), Pattern) )
    | Psi, depth, F, Pattern ->
        let Psi' = I.Decl (Psi, T.PDec (None, F, None, None)) in
        let depth' = depth + 1 in
        fun k ->
          let (T.PDec (_, F', _, _)) = T.ctxDec (Psi', k) in
          ( T.Case
              (T.Cases
                 [ (Psi', T.Dot (T.Prg Pattern, T.Shift depth'), T.Var k) ]),
            F' )

  let rec installProjection = function
    | [], _, F, Proj -> []
    | cid :: cids, n, F, Proj ->
        let P', F' = Proj n in
        let P = T.Lam (T.PDec (None, F, None, None), P') in
        let F'' = T.All ((T.PDec (None, F, None, None), T.Explicit), F') in
        let name = I.conDecName (I.sgnLookup cid) in
        let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F'')) in
        let lemma = T.lemmaAdd (T.ValDec ("#" ^ name, P, F'')) in
        lemma :: installProjection (cids, n - 1, F, Proj)

  let rec installSelection = function
    | [ cid ], [ lemma ], F1, main ->
        let P = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil)) in
        let name = I.conDecName (I.sgnLookup cid) in
        let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F1)) in
        let lemma' = T.lemmaAdd (T.ValDec (name, P, F1)) in
        [ lemma' ]
    | cid :: cids, lemma :: lemmas, T.And (F1, F2), main ->
        let P = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil)) in
        let name = I.conDecName (I.sgnLookup cid) in
        let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F1)) in
        let lemma' = T.lemmaAdd (T.ValDec (name, P, F1)) in
        lemma' :: installSelection (cids, lemmas, F2, main)

  let rec installPrg = function
    | [ cid ] ->
        let F = convertFor [ cid ] in
        let P = convertPrg ([ cid ], None) in
        let name = I.conDecName (I.sgnLookup cid) in
        let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) in
        let _ =
          if !Global.chatter >= 4 then
            print "[Redundancy Checker (factoring) ..."
          else ()
        in
        let factP = Redundant.convert P in
        let _ = if !Global.chatter >= 4 then print "done]\n" else () in
        let lemma = T.lemmaAdd (T.ValDec (name, factP, F)) in
        (lemma, [], [])
    | cids ->
        let F = convertFor cids in
        let _ = TomegaTypeCheck.checkFor (I.Null, F) in
        let Proj = createProjection (I.Null, 0, F, T.Var 1) in
        let projs = installProjection (cids, depthConj F, F, Proj) in
        let P = convertPrg (cids, Some projs) in
        let s = name cids in
        let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) in
        let _ =
          if !Global.chatter >= 4 then
            print "[Redundancy Checker (factoring) ..."
          else ()
        in
        let factP = Redundant.convert P in
        let _ = if !Global.chatter >= 4 then print "done]\n" else () in
        let lemma = T.lemmaAdd (T.ValDec (s, factP, F)) in
        let sels = installSelection (cids, projs, F, lemma) in
        (lemma, projs, sels)

  let rec mkResult = function
    | 0 -> T.Unit
    | n -> T.PairExp (I.Root (I.BVar n, I.Nil), mkResult (n - 1))

  let rec convertGoal (G, V) =
    let a = I.targetFam V in
    let W = WorldSyn.lookup a in
    let W', wmap = transformWorlds ([ a ], W) in
    let (Some (_, (P', Q'))) =
      traversePos ([], wmap, None)
        ( (I.Null, G, I.Null),
          V,
          Some
            ( I.Shift (I.ctxLength G),
              fun P -> ((I.Null, T.id, P), mkResult (I.ctxLength G)) ) )
    in
    let _, _, P'' = P' Q' in
    P''

  let convertFor = convertFor
  let convertPrg = fun L -> convertPrg (L, None)
  let installFor = installFor
  let installPrg = installPrg
  let traverse = traverse
  let convertGoal = convertGoal
end

(* functor FunSyn *)
