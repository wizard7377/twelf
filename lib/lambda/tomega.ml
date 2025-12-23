(* Internal syntax for_sml Delphin *)

(* Author: Carsten Schuermann *)

module type TOMEGA = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (* make abstract *)
  type label = int
  type lemma = int
  type worlds = Worlds of IntSyn.cid list
  type quantifier = Implicit | Explicit

  type tC =
    | Abs of IntSyn.dec * tC
    | Conj of tC * tC
    | Base of (IntSyn.exp * IntSyn.sub) * (IntSyn.exp * IntSyn.sub) Order.order

  type for_sml =
    | World of worlds * for_sml
    | All of (dec * quantifier) * for_sml
    | Ex of (IntSyn.dec * quantifier) * for_sml
    | True
    | And of for_sml * for_sml
    | FClo of for_sml * sub
    | FVar of (dec IntSyn.ctx * for_sml option ref)

  and dec =
    | UDec of IntSyn.dec
    | PDec of string option * for_sml * tC option * tC option

  and prg =
    | Box of worlds * prg
    | Lam of dec * prg
    | New of prg
    | Choose of prg
    | PairExp of IntSyn.exp * prg
    | PairBlock of IntSyn.block * prg
    | PairPrg of prg * prg
    | Unit
    | Redex of prg * spine
    | Rec of dec * prg
    | Case of cases
    | PClo of prg * sub
    | Let of dec * prg * prg
    | EVar of
        dec IntSyn.ctx
        * prg option ref
        * for_sml
        * tC option
        * tC option
        * IntSyn.exp
    | Const of lemma
    | Var of int
    | LetPairExp of IntSyn.dec * dec * prg * prg
    | LetUnit of prg * prg

  and spine =
    | Nil
    | AppExp of IntSyn.exp * spine
    | AppBlock of IntSyn.block * spine
    | AppPrg of prg * spine
    | SClo of spine * sub

  and sub = Shift of int | Dot of front * sub

  and front =
    | Idx of int
    | Prg of prg
    | Exp of IntSyn.exp
    | Block of IntSyn.block
    | Undef

  and cases = Cases of dec IntSyn.ctx * sub * prg list

  (* C ::= (Psi' |> s |-> P)    *)
  type conDec = ForDec of string * for_sml | ValDec of string * prg * for_sml

  (*      | f == P              *)
  exception NoMatch

  val coerceSub : sub -> IntSyn.sub
  val embedSub : IntSyn.sub -> sub
  val coerceCtx : dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx
  val strengthenCtx : dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx * sub * sub
  val embedCtx : IntSyn.dec IntSyn.ctx -> dec IntSyn.ctx
  val weakenSub : dec IntSyn.ctx -> sub
  val invertSub : sub -> sub
  val id : sub
  val shift : sub
  val dot1 : sub -> sub
  val dotEta : front * sub -> sub
  val comp : sub * sub -> sub
  val varSub : int * sub -> front
  val decSub : dec * sub -> dec
  val forSub : for_sml * sub -> for_sml
  val whnfFor : for_sml * sub -> for_sml * sub
  val normalizePrg : prg * sub -> prg
  val normalizeSub : sub -> sub
  val derefPrg : prg -> prg
  val lemmaLookup : lemma -> conDec
  val lemmaName : string -> lemma
  val lemmaAdd : conDec -> lemma
  val lemmaSize : unit -> int
  val lemmaDef : lemma -> prg
  val lemmaFor : lemma -> for_sml
  val eqWorlds : worlds * worlds -> bool
  val convFor : (for_sml * sub) * (for_sml * sub) -> bool
  val newEVar : dec IntSyn.ctx * for_sml -> prg
  val newEVarTC : dec IntSyn.ctx * for_sml * tC option * tC option -> prg

  (* Below are added by Yu Liao *)
  val ctxDec : dec IntSyn.ctx * int -> dec
  val revCoerceSub : IntSyn.sub -> sub
  val revCoerceCtx : IntSyn.dec IntSyn.ctx -> dec IntSyn.ctx

  (* Added references by ABP *)
  val coerceFront : front -> IntSyn.front
  val revCoerceFront : IntSyn.front -> front
  val deblockify : IntSyn.dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx * sub

  (* Stuff that has to do with termination conditions *)
  val tCSub : tC * IntSyn.sub -> tC
  val normalizeTC : tC -> tC
  val convTC : tC * tC -> bool
  val transformTC : IntSyn.dec IntSyn.ctx * for_sml * int Order.order list -> tC
end

(* Signature TOMEGA *)
(* Internal syntax for_sml functional proof term calculus *)

(* Author: Carsten Schuermann *)

(* Modified: Yu Liao, Adam Poswolsky *)

module Tomega (Whnf : Whnf.WHNF) (Conv : Conv.CONV) : TOMEGA = struct
  exception Error of string

  type label = int
  type lemma = int
  type worlds = Worlds of IntSyn.cid list
  type quantifier = Implicit | Explicit

  type tC =
    | Abs of IntSyn.dec * tC
    | Conj of tC * tC
    | Base of (IntSyn.exp * IntSyn.sub) * (IntSyn.exp * IntSyn.sub) Order.order

  type for_sml =
    | World of worlds * for_sml
    | All of (dec * quantifier) * for_sml
    | Ex of (IntSyn.dec * quantifier) * for_sml
    | True
    | And of for_sml * for_sml
    | FClo of for_sml * sub
    | FVar of (dec IntSyn.ctx * for_sml option ref)

  and dec =
    | UDec of IntSyn.dec
    | PDec of string option * for_sml * tC option * tC option

  and prg =
    | Box of worlds * prg
    | Lam of dec * prg
    | New of prg
    | Choose of prg
    | PairExp of IntSyn.exp * prg
    | PairBlock of IntSyn.block * prg
    | PairPrg of prg * prg
    | Unit
    | Redex of prg * spine
    | Rec of dec * prg
    | Case of cases
    | PClo of prg * sub
    | Let of dec * prg * prg
    | EVar of
        dec IntSyn.ctx
        * prg option ref
        * for_sml
        * tC option
        * tC option
        * IntSyn.exp
    | Const of lemma
    | Var of int
    | LetPairExp of IntSyn.dec * dec * prg * prg
    | LetUnit of prg * prg

  and spine =
    | Nil
    | AppExp of IntSyn.exp * spine
    | AppBlock of IntSyn.block * spine
    | AppPrg of prg * spine
    | SClo of spine * sub

  and sub = Shift of int | Dot of front * sub

  and front =
    | Idx of int
    | Prg of prg
    | Exp of IntSyn.exp
    | Block of IntSyn.block
    | Undef

  and cases = Cases of dec IntSyn.ctx * sub * prg list
  (* C ::= (Psi' |> s |-> P)    *)

  type conDec = ForDec of string * for_sml | ValDec of string * prg * for_sml
  (*      | f == P              *)

  exception NoMatch

  module I = IntSyn
  module O = Order

  let maxLemma = Global.maxCid

  let lemmaArray =
    (Array.array (maxLemma + 1, ForDec ("", True)) : conDec Array.array)

  let nextLemma = ref 0
  let rec lemmaLookup lemma = Array.sub (lemmaArray, lemma)

  let rec lemmaAdd lemmaDec =
    let lemma = !nextLemma in
    if lemma > maxLemma then
      raise
        (Error
           ("Global signature size " ^ Int.toString (maxLemma + 1) ^ " exceeded"))
    else (
      Array.update (lemmaArray, lemma, lemmaDec);
      nextLemma := lemma + 1;
      lemma)

  let rec lemmaSize () = !nextLemma
  let rec lemmaDef lemma = match lemmaLookup lemma with ValDec (_, P, _) -> P

  let rec lemmaFor lemma =
    match lemmaLookup lemma with ForDec (_, F) -> F | ValDec (_, _, F) -> F

  let rec lemmaName s = lemmaName' !nextLemma s

  and lemmaName' = function
    | -1, s -> raise (Error "Function name not found")
    | n, s -> (
        match lemmaLookup n with
        | ForDec (s', F) -> if s = s' then n else lemmaName' (n - 1) s
        | ValDec (s', P, F) -> if s = s' then n else lemmaName' (n - 1) s)
  (* not very efficient, improve !!! *)

  (* coerceFront F = F'

       Invariant:
       If    Psi |- F front
       and   G = mu G. G \in Psi
       then  G   |- F' front
    *)

  let rec coerceFront = function
    | Idx k -> I.Idx k
    | Prg P -> I.Undef
    | Exp M -> I.Exp M
    | Block B -> I.Block B
    | Undef -> I.Undef
  (* --Yu Liao Why cases: Block, Undef aren't defined *)

  (* embedFront F = F'

       Invariant:
       If    Psi |- F front
       and   G = mu G. G \in Psi
       then  G   |- F' front
    *)

  let rec embedFront = function
    | I.Idx k -> Idx k
    | I.Exp U -> Exp U
    | I.Block B -> Block B
    | I.Undef -> Undef
  (* coerceSub t = s

       Invariant:
       If    Psi |- t : Psi'
       then  G   |- s : G'
       where G = mu G. G \in Psi
       and   G' = mu G. G \in Psi'
    *)

  let rec coerceSub = function
    | Shift n -> I.Shift n
    | Dot (Ft, t) -> I.Dot (coerceFront Ft, coerceSub t)

  let rec embedSub = function
    | I.Shift n -> Shift n
    | I.Dot (Ft, s) -> Dot (embedFront Ft, embedSub s)
  (* Definition:
       |- Psi ctx[block] holds iff Psi = _x_1 : (L1, t1), ... _x_n : (Ln, tn)
    *)

  let rec revCoerceFront = function
    | I.Idx k -> Idx k
    | I.Exp M -> Exp M
    | I.Block b -> Block b
    | I.Undef -> Undef
  (* revCoerceSub t = s
    coerce substitution in LF level t ==> s in Tomega level *)

  let rec revCoerceSub = function
    | I.Shift n -> Shift n
    | I.Dot (Ft, t) -> Dot (revCoerceFront Ft, revCoerceSub t)
  (* Invariant Yu? *)

  let rec revCoerceCtx = function
    | I.Null -> I.Null
    | I.Decl (Psi, D) -> I.Decl (revCoerceCtx Psi, UDec D)

  let id = Shift 0
  (* dotEta (Ft, s) = s'

       Invariant:
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)

  let rec dotEta = function
    | Ft, s -> Dot (Ft, s)
    | Ft, s ->
        let Ft' = try Idx (Whnf.etaContract U) with Eta -> Ft in
        Dot (Ft', s)
    | Ft, s -> Dot (Ft, s)
  (* embedCtx G = Psi

       Invariant:
       If   G is an LF ctx
       then Psi is G, embedded into Tomega
    *)

  let rec embedCtx = function
    | I.Null -> I.Null
    | I.Decl (G, D) -> I.Decl (embedCtx G, UDec D)
  (* orderSub (O, s) = O'

         Invariant:
         If   G' |- O order    and    G |- s : G'
         then G |- O' order
         and  G |- O' == O[s] order
      *)

  let rec orderSub = function
    | O.Arg ((U, s1), (V, s2)), s ->
        O.Arg ((U, I.comp (s1, s)), (V, I.comp (s2, s)))
    | O.Lex Os, s -> O.Lex (map (fun O -> orderSub (O, s)) Os)
    | O.Simul Os, s -> O.Simul (map (fun O -> orderSub (O, s)) Os)

  let rec TCSub = function
    | Base O, s -> Base (orderSub (O, s))
    | Conj (TC1, TC2), s -> Conj (TCSub (TC1, s), TCSub (TC2, s))
    | Abs (D, TC), s -> Abs (I.decSub (D, s), TCSub (TC, I.dot1 s))

  let rec TCSubOpt = function
    | None, s -> None
    | Some TC, s -> Some (TCSub (TC, s))
  (* normalizeTC (O) = O'

         Invariant:
         If   G |- O TC
         then G |- O' TC
         and  G |- O = O' TC
         and  each sub term of O' is in normal form.
      *)

  let rec normalizeTC' = function
    | O.Arg (Us, Vs) ->
        O.Arg ((Whnf.normalize Us, I.id), (Whnf.normalize Vs, I.id))
    | O.Lex Os -> O.Lex (map normalizeTC' Os)
    | O.Simul Os -> O.Simul (map normalizeTC' Os)

  let rec normalizeTC = function
    | Base O -> Base (normalizeTC' O)
    | Conj (TC1, TC2) -> Conj (normalizeTC TC1, normalizeTC TC2)
    | Abs (D, TC) -> Abs (Whnf.normalizeDec (D, I.id), normalizeTC TC)

  let rec normalizeTCOpt = function
    | None -> None
    | Some TC -> Some (normalizeTC TC)
  (* convTC (O1, O2) = B'

         Invariant:
         If   G |- O1 TC
         and  G |- O2 TC
         then B' holds iff G |- O1 == O2 TC
      *)

  let rec convTC' = function
    | O.Arg (Us1, _), O.Arg (Us2, _) -> Conv.conv (Us1, Us2)
    | O.Lex Os1, O.Lex Os2 -> convTCs (Os1, Os2)
    | O.Simul Os1, O.Simul Os2 -> convTCs (Os1, Os2)

  and convTCs = function
    | [], [] -> true
    | O1 :: L1, O2 :: L2 -> convTC' (O1, O2) && convTCs (L1, L2)

  let rec convTC = function
    | Base O, Base O' -> convTC' (O, O')
    | Conj (TC1, TC2), Conj (TC1', TC2') ->
        convTC (TC1, TC1') && convTC (TC2, TC2')
    | Abs (D, TC), Abs (D', TC') ->
        Conv.convDec ((D, I.id), (D', I.id)) && convTC (TC, TC')
    | _ -> false

  let rec convTCOpt = function
    | None, None -> true
    | Some TC1, Some TC2 -> convTC (TC1, TC2)
    | _ -> false

  let rec transformTC' = function
    | G, O.Arg k ->
        let k' = I.ctxLength G - k + 1 in
        let (I.Dec (_, V)) = I.ctxDec (G, k') in
        O.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
    | G, O.Lex Os -> O.Lex (map (fun O -> transformTC' (G, O)) Os)
    | G, O.Simul Os -> O.Simul (map (fun O -> transformTC' (G, O)) Os)

  let rec transformTC = function
    | G, All ((UDec D, _), F), Os -> Abs (D, transformTC (I.Decl (G, D), F, Os))
    | G, And (F1, F2), O :: Os ->
        Conj (transformTC (G, F1, [ O ]), transformTC (G, F2, Os))
    | G, Ex _, [ O ] -> Base (transformTC' (G, O))
  (* bvarSub (n, t) = Ft'

       Invariant:
       If    Psi |- t : Psi'    Psi' |- n :: F
       then  Ft' = Ftn          if  t = Ft1 .. Ftn .. ^k
         or  Ft' = ^(n+k)       if  t = Ft1 .. Ftm ^k   and m<n
       and   Psi |- Ft' :: F [t]
    *)

  let rec varSub = function
    | 1, Dot (Ft, t) -> Ft
    | n, Dot (Ft, t) -> varSub (n - 1, t)
    | n, Shift k -> Idx (n + k)

  and frontSub = function
    | Idx n, t -> varSub (n, t)
    | Exp U, t -> Exp (I.EClo (U, coerceSub t))
    | Prg P, t -> Prg (PClo (P, t))
    | Block B, t -> Block (I.blockSub (B, coerceSub t))

  and comp = function
    | Shift 0, t -> t
    | t, Shift 0 -> t
    | Shift n, Dot (Ft, t) -> comp (Shift (n - 1), t)
    | Shift n, Shift m -> Shift (n + m)
    | Dot (Ft, t), t' -> Dot (frontSub (Ft, t'), comp (t, t'))
  (* dot1 (t) = t'

       Invariant:
       If   G |- t : G'
       then t' = 1. (t o ^)
       and  for_sml all V t.t.  G' |- V : L
            G, V[t] |- t' : G', V

       If t patsub then t' patsub
    *)

  let rec dot1 = function t -> t | t -> Dot (Idx 1, comp (t, Shift 1))
  let id = Shift 0
  let shift = Shift 1
  (* weakenSub (Psi) = w

       Invariant:
       If   Psi is a context
       then G is embed Psi
       and  Psi |- w : G
    *)

  let rec weakenSub = function
    | I.Null -> id
    | I.Decl (Psi, D) -> dot1 (weakenSub Psi)
    | I.Decl (Psi, D) -> comp (weakenSub Psi, shift)
  (* forSub (F, t) = F'

       Invariant:
       If    Psi |- F for_sml
       and   Psi' |- t : Psi
       then  Psi' |- F' = F[t] for_sml
    *)

  let rec forSub = function
    | All ((D, Q), F), t -> All ((decSub (D, t), Q), forSub (F, dot1 t))
    | Ex ((D, Q), F), t ->
        Ex ((I.decSub (D, coerceSub t), Q), forSub (F, dot1 t))
    | And (F1, F2), t -> And (forSub (F1, t), forSub (F2, t))
    | FClo (F, t1), t2 -> forSub (F, comp (t1, t2))
    | World (W, F), t -> World (W, forSub (F, t))
    | True, _ -> True

  and decSub = function
    | PDec (x, F, TC1, None), t ->
        let s = coerceSub t in
        PDec (x, forSub (F, t), TCSubOpt (TC1, s), None)
    | UDec D, t -> UDec (I.decSub (D, coerceSub t))
  (* invertSub s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)

  let rec invertSub s =
    (* returns NONE if not found *)
    (* Suggested by ABP
         * If you do not want this, remove the getFrontIndex and other
          | lookup (n, Dot (Ft, s'), p) =
              (case getFrontIndex(Ft) of
                 NONE => lookup (n+1, s', p)
               | SOME k => if (k=p) then SOME n else lookup (n+1, s', p))
        *)
    let rec getFrontIndex = function
      | Idx k -> Some k
      | Prg P -> getPrgIndex P
      | Exp U -> getExpIndex U
      | Block B -> getBlockIndex B
      | Undef -> None
    and getPrgIndex = function
      | Redex (Var k, Nil) -> Some k
      | Redex (P, Nil) -> getPrgIndex P
      | PClo (P, t) -> (
          match getPrgIndex P with
          | None -> None
          | Some i -> getFrontIndex (varSub (i, t)))
      | _ -> None
    and getExpIndex = function
      | I.Root (I.BVar k, I.Nil) -> Some k
      | I.Redex (U, I.Nil) -> getExpIndex U
      | I.EClo (U, t) -> (
          match getExpIndex U with
          | None -> None
          | Some i -> getFrontIndex (revCoerceFront (I.bvarSub (i, t))))
      | U -> ( try Some (Whnf.etaContract U) with Whnf.Eta -> None)
      | _ -> None
    and getBlockIndex = function I.Bidx k -> Some k | _ -> None in
    let rec lookup = function
      | n, Shift _, p -> None
      | n, Dot (Undef, s'), p -> lookup (n + 1, s', p)
      | n, Dot (Idx k, s'), p -> if k = p then Some n else lookup (n + 1, s', p)
    in
    let rec invertSub'' = function
      | 0, si -> si
      | p, si -> (
          match lookup (1, s, p) with
          | Some k -> invertSub'' (p - 1, Dot (Idx k, si))
          | None -> invertSub'' (p - 1, Dot (Undef, si)))
    in
    let rec invertSub' = function
      | n, Shift p -> invertSub'' (p, Shift n)
      | n, Dot (_, s') -> invertSub' (n + 1, s')
    in
    invertSub' (0, s)
  (* coerceCtx (Psi) = G

       Invariant:
       If   |- Psi ctx[block]
       then |- G lf-ctx[block]
       and  |- Psi == G
    *)

  let rec coerceCtx = function
    | I.Null -> I.Null
    | I.Decl (Psi, UDec D) -> I.Decl (coerceCtx Psi, D)
    | I.Decl (Psi, PDec (x, _, _, _)) -> I.Decl (coerceCtx Psi, I.NDec x)
  (* coerceCtx (Psi) = (G, s)

       Invariant:
       If   |- Psi ctx[block]
       then |- G lf-ctx[block]
       and  |- Psi == G
       and  G |- s : Psi
    *)

  let rec strengthenCtx Psi =
    let w = weakenSub Psi in
    let s = invertSub w in
    (coerceCtx Psi, w, s)
  (* convFor ((F1, t1), (F2, t2)) = B

       Invariant:
       If   G |- t1 : G1
       and  G1 |- F1 : formula
       and  G |- t2 : G2
       and  G2 |- F2 : formula
       and  (F1, F2 do not contain abstraction over contextblocks )
       then B holds iff G |- F1[s1] = F2[s2] formula
    *)

  let rec convFor = function
    | (True, _), (True, _) -> true
    | (All ((D1, _), F1), t1), (All ((D2, _), F2), t2) ->
        convDec ((D1, t1), (D2, t2)) && convFor ((F1, dot1 t1), (F2, dot1 t2))
    | (Ex ((D1, _), F1), t1), (Ex ((D2, _), F2), t2) ->
        Conv.convDec ((D1, coerceSub t1), (D2, coerceSub t2))
        && convFor ((F1, dot1 t1), (F2, dot1 t2))
    | (And (F1, F1'), t1), (And (F2, F2'), t2) ->
        convFor ((F1, t1), (F2, t2)) && convFor ((F1', t1), (F2', t2))
    | _ -> false

  and convDec = function
    | (UDec D1, t1), (UDec D2, t2) ->
        Conv.convDec ((D1, coerceSub t1), (D2, coerceSub t2))
    | (PDec (_, F1, TC1, TC1'), t1), (PDec (_, F2, TC2, TC2'), t2) ->
        convFor ((F1, t1), (F2, t2));
        convTCOpt (TC1, TC1');
        convTCOpt (TC2, TC2')
  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)

  let rec newEVar (Psi, F) =
    EVar (Psi, ref None, F, None, None, I.newEVar (coerceCtx Psi, I.Uni I.Type))

  let rec newEVarTC (Psi, F, TC, TC') =
    EVar (Psi, ref None, F, TC, TC', I.newEVar (coerceCtx Psi, I.Uni I.Type))

  let rec exists = function
    | x, [] -> false
    | x, y :: W2 -> x = y || exists (x, W2)

  let rec subset = function
    | [], _ -> true
    | x :: W1, W2 -> exists (x, W2) && subset (W1, W2)

  let rec eqWorlds (Worlds W1, Worlds W2) = subset (W1, W2) && subset (W2, W1)
  (* ctxDec (G, k) = x:V
     Invariant:
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)

  let rec ctxDec (G, k) =
    (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
    (* ctxDec' (Null, k')  should not occur by invariant *)
    let rec ctxDec' = function
      | I.Decl (G', UDec (I.Dec (x, V'))), 1 ->
          UDec (I.Dec (x, I.EClo (V', I.Shift k)))
      | I.Decl (G', UDec (I.BDec (l, (c, s)))), 1 ->
          UDec (I.BDec (l, (c, I.comp (s, I.Shift k))))
      | I.Decl (G', PDec (x, F, TC1, TC2)), 1 ->
          PDec
            ( x,
              forSub (F, Shift k),
              TCSubOpt (TC1, I.Shift k),
              TCSubOpt (TC2, I.Shift k) )
      | I.Decl (G', _), k' -> ctxDec' (G', k' - 1)
    in
    ctxDec' (G, k)
  (* mkInst (n) = iota

        Invariant:
        iota = n.n-1....1
     *)

  let rec mkInst = function
    | 0 -> []
    | n -> I.Root (I.BVar n, I.Nil) :: mkInst (n - 1)
  (* deblockify G = (G', t')

       Invariant:
       If   |- G ctx
       then G' |- t' : G
    *)

  let rec deblockify = function
    | I.Null -> (I.Null, id)
    | I.Decl (G, I.BDec (x, (c, s))) ->
        (* G' |- t' : G *)
        (* G'' = G', V1 ... Vn *)
        (* G'' |- t'' : G *)
        (* I = (n, n-1 ... 1)  *)
        (* G'' |- t''' : G, x:(c,s) *)
        let G', t' = deblockify G in
        let _, L = I.constBlock c in
        let n = List.length L in
        let G'' = append (G', (L, I.comp (s, coerceSub t'))) in
        let t'' = comp (t', Shift n) in
        let I = I.Inst (mkInst n) in
        let t''' = Dot (Block I, t'') in
        (G'', t''')

  and append = function
    | G', ([], s) -> G'
    | G', (D :: L, s) -> append (I.Decl (G', I.decSub (D, s)), (L, I.dot1 s))
  (* whnfFor (F, t) = (F', t')

       Invariant:
       If    Psi |- F for_sml
       and   Psi' |- t : Psi
       then  Psi' |- t' : Psi''
       and   Psi'' |- F' :for_sml
       and   Psi' |- F'[t'] = F[t] for_sml
    *)

  let rec whnfFor = function
    | Ft -> Ft
    | Ft -> Ft
    | Ft -> Ft
    | FClo (F, t1), t2 -> whnfFor (F, comp (t1, t2))
    | Ft -> Ft
    | Ft -> Ft
  (* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- V :: F
       and  Psi' |- V value
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for_sml
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)

  let rec normalizePrg = function
    | Var n, t -> (
        match varSub (n, t) with
        | Prg P -> P
        | Idx _ -> raise Domain
        | Exp _ -> raise Domain
        | Block _ -> raise Domain
        | Undef -> raise Domain)
    | PairExp (U, P'), t ->
        PairExp (Whnf.normalize (U, coerceSub t), normalizePrg (P', t))
    | PairBlock (B, P'), t ->
        PairBlock (I.blockSub (B, coerceSub t), normalizePrg (P', t))
    | PairPrg (P1, P2), t -> PairPrg (normalizePrg (P1, t), normalizePrg (P2, t))
    | Unit, _ -> Unit
    | EVar (_, { contents = Some P }, _, _, _, _), t -> PClo (P, t)
    | P, t -> PClo (P, t)
    | Lam (D, P), t -> Lam (normalizeDec (D, t), normalizePrg (P, dot1 t))
    | Rec (D, P), t -> Rec (normalizeDec (D, t), normalizePrg (P, dot1 t))
    | PClo (P, t), t' -> normalizePrg (P, comp (t, t'))

  and normalizeSpine = function
    | Nil, t -> Nil
    | AppExp (U, S), t ->
        AppExp (Whnf.normalize (U, coerceSub t), normalizeSpine (S, t))
    | AppPrg (P, S), t -> AppPrg (normalizePrg (P, t), normalizeSpine (S, t))
    | AppBlock (B, S), t ->
        AppBlock (I.blockSub (B, coerceSub t), normalizeSpine (S, t))
    | SClo (S, t1), t2 -> normalizeSpine (S, comp (t1, t2))

  and normalizeDec = function
    | PDec (name, F, TC1, None), t ->
        PDec
          ( name,
            forSub (F, t),
            normalizeTCOpt (TCSubOpt (TC1, coerceSub t)),
            None )
    | UDec D, t -> UDec (Whnf.normalizeDec (D, coerceSub t))

  let rec normalizeSub = function
    | s -> s
    | Dot (Prg P, s) -> Dot (Prg (normalizePrg (P, id)), normalizeSub s)
    | Dot (Exp E, s) -> Dot (Exp (Whnf.normalize (E, I.id)), normalizeSub s)
    | Dot (Block k, s) -> Dot (Block k, normalizeSub s)
    | Dot (Idx k, s) -> Dot (Idx k, normalizeSub s)
  (* derefPrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- V :: F
       and  Psi' |- V value
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for_sml
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)

  let rec derefPrg = function
    | Var n -> Var n
    | PairExp (U, P') -> PairExp (U, derefPrg P')
    | PairBlock (B, P') -> PairBlock (B, derefPrg P')
    | PairPrg (P1, P2) -> PairPrg (derefPrg P1, derefPrg P2)
    | Unit -> Unit
    | EVar (_, { contents = Some P }, _, _, _, _) -> P
    | P -> P
    | Lam (D, P) -> Lam (derefDec D, derefPrg P)
    | Rec (D, P) -> Rec (derefDec D, derefPrg P)
    | Redex (P, S) -> Redex (derefPrg P, derefSpine S)
    | Case (Cases Cs) ->
        Case
          (Cases
             (flattenCases (map (fun (Psi, s, P) -> (Psi, s, derefPrg P)) Cs)))
    | Let (D, P1, P2) -> Let (derefDec D, derefPrg P1, derefPrg P2)
    | LetPairExp (D1, D2, P1, P2) ->
        LetPairExp (D1, derefDec D2, derefPrg P1, derefPrg P2)
    | LetUnit (P1, P2) -> LetUnit (derefPrg P1, derefPrg P2)

  and flattenCases = function
    | (Psi, s, Case (Cases L)) :: Cs ->
        map (fun (Psi', s', P') -> (Psi', comp (s, s'), P')) (flattenCases L)
        @ flattenCases Cs
    | (Psi, s, P) :: Cs -> (Psi, s, P) :: flattenCases Cs
    | [] -> []

  and derefSpine = function
    | Nil -> Nil
    | AppExp (U, S) -> AppExp (U, derefSpine S)
    | AppPrg (P, S) -> AppPrg (derefPrg P, derefSpine S)
    | AppBlock (B, S) -> AppBlock (B, derefSpine S)

  and derefDec = function
    | PDec (name, F, TC1, TC2) -> PDec (name, F, TC1, TC2)
    | UDec D -> UDec D

  let lemmaLookup = lemmaLookup
  let lemmaAdd = lemmaAdd
  let lemmaSize = lemmaSize
  let lemmaDef = lemmaDef
  let lemmaName = lemmaName
  let lemmaFor = lemmaFor
  let coerceSub = coerceSub
  let coerceCtx = coerceCtx
  let strengthenCtx = strengthenCtx
  let embedCtx = embedCtx
  let id = id
  let shift = shift
  let comp = comp
  let dot1 = dot1
  let varSub = varSub
  let decSub = decSub
  let weakenSub = weakenSub
  let invertSub = invertSub
  let ctxDec = ctxDec
  let forSub = forSub
  let whnfFor = whnfFor
  let normalizePrg = normalizePrg
  let normalizeSub = normalizeSub
  let derefPrg = derefPrg
  let id = id
  let dotEta = dotEta
  let convFor = convFor
  let newEVar = newEVar
  let newEVarTC = newEVarTC
  (* Below are added by Yu Liao *)

  let embedSub = embedSub
  let eqWorlds = eqWorlds
  let ctxDec = ctxDec
  let revCoerceSub = revCoerceSub
  let revCoerceCtx = revCoerceCtx
  (* Added referenced by ABP *)

  let coerceFront = coerceFront
  let revCoerceFront = revCoerceFront
  let deblockify = deblockify
  (* Stuff that has to do with termination conditions *)

  let TCSub = TCSub
  let normalizeTC = normalizeTC
  let convTC = convTC
  let transformTC = transformTC
end

(* functor FunSyn *)
