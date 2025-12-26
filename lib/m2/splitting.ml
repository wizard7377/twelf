open Basis ;; 
(* Splitting *)

(* Author: Carsten Schuermann *)

module type SPLITTING = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  type operator

  val expand : MetaSyn.state -> operator list
  val apply : operator -> MetaSyn.state list
  val var : operator -> int
  val menu : operator -> string
  val index : operator -> int
end

(* signature Split.SPLITTING *)
(* Splitting *)

(* Author: Carsten Schuermann *)

module Splitting
    (Global : Global.GLOBAL)
    (MetaSyn' : Metasyn.METASYN)
    (MetaAbstract : Meta_abstract.METAABSTRACT)
    (MetaPrint : Meta_print.METAPRINT)
    (ModeTable : Modetable.MODETABLE)
    (Whnf : Whnf.WHNF)
    (Index : Index.INDEX)
    (Print : Print.PRINT)
    (Unify : Unify.UNIFY) : Split.SPLITTING = struct
  module MetaSyn = MetaSyn'

  exception Error of string
  (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     "Active", and cases where there were
     leftover constraints after "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases.
  *)

  type 'a flag = Active of 'a | InActive
  type operator = (MetaSyn.state * int) * MetaSyn.state flag list

  module M = MetaSyn
  module I = IntSyn
  (* constCases (G, (V, s), I, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases from I
    *)

  let rec constCases = function
    | G, Vs, [], abstract, ops -> ops
    | G, Vs, I.Const c :: Sgn, abstract, ops ->
        let U, Vs' = M.createAtomConst (G, I.Const c) in
        constCases
          ( G,
            Vs,
            Sgn,
            abstract,
            Cs.CSManager.trail (fun () ->
                try
                  if Unify.unifiable (G, Vs, Vs') then
                    Active (abstract (I.conDecName (I.sgnLookup c) ^ "/", U))
                    :: ops
                  else ops
                with MetaAbstract.Error _ -> InActive :: ops) )
  (* paramCases (G, (V, s), k, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases introduced by parameters <= k in G
    *)

  let rec paramCases = function
    | G, Vs, 0, abstract, ops -> ops
    | G, Vs, k, abstract, ops ->
        let U, Vs' = M.createAtomBVar (G, k) in
        paramCases
          ( G,
            Vs,
            k - 1,
            abstract,
            Cs.CSManager.trail (fun () ->
                try
                  if Unify.unifiable (G, Vs, Vs') then
                    Active (abstract (Int.toString k ^ "/", U)) :: ops
                  else ops
                with MetaAbstract.Error _ -> InActive :: ops) )
  (* lowerSplitDest (G, (V, s'), abstract) = C'

       Invariant:
       If   G0, G |- s' : G1  G1 |- V: type
       and  G is the context of local parameters
       and  abstract abstraction function
       then C' is a list of all cases unifying with V[s']
            (it contains constant and parameter cases)
    *)

  let rec lowerSplitDest = function
    | G, (V, s'), abstract ->
        constCases
          ( G,
            (V, s'),
            Index.lookup c,
            abstract,
            paramCases (G, (V, s'), I.ctxLength G, abstract, []) )
    | G, (I.Pi ((D, P), V), s'), abstract ->
        let D' = I.decSub (D, s') in
        lowerSplitDest
          ( I.Decl (G, D'),
            (V, I.dot1 s'),
            fun name U -> abstract (name, I.Lam (D', U)) )
  (* split ((G, M), (x:D, s), abstract) = C'

       Invariant :
       If   |- G ctx
       and  G |- M mtx
       and  G |- s : G1   and  G1 |- D : L
       and  abstract abstraction function
       then C' = (C1, ... Cn) are resulting cases from splitting D[s]
    *)

  let rec split (M.Prefix (G, M, B), (D, s), abstract) =
    lowerSplitDest
      ( I.Null,
        (V, s),
        fun name' U' ->
          abstract (name', M.Prefix (G, M, B), I.Dot (I.Exp U', s)) )
  (* rename to add N prefix? *)

  (* occursIn (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)

  let rec occursInExp = function
    | k, I.Uni _ -> false
    | k, I.Pi (DP, V) -> occursInDecP (k, DP) || occursInExp (k + 1, V)
    | k, I.Root (C, S) -> occursInCon (k, C) || occursInSpine (k, S)
    | k, I.Lam (D, V) -> occursInDec (k, D) || occursInExp (k + 1, V)
    | k, I.FgnExp csfe ->
        I.FgnExpStd.fold csfe
          (fun U B -> B || occursInExp (k, Whnf.normalize (U, I.id)))
          false

  and occursInCon = function
    | k, I.BVar k' -> k = k'
    | k, I.Const _ -> false
    | k, I.Def _ -> false
    | k, I.Skonst _ -> false

  and occursInSpine = function
    | _, I.Nil -> false
    | k, I.App (U, S) -> occursInExp (k, U) || occursInSpine (k, S)

  and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
  and occursInDecP (k, (D, _)) = occursInDec (k, D)

  let rec isIndexInit k = false
  let rec isIndexSucc (D, isIndex) k = occursInDec (k, D) || isIndex (k + 1)
  let rec isIndexFail (D, isIndex) k = isIndex (k + 1)
  (* checkExp (M, U) = B

       Invariant:
       If   G |- M
       and  G |- U : V
       and  U in nf
       then B holds iff U does not contain any Bot variables
    *)

  let rec checkVar = function
    | I.Decl (M, M.Top), 1 -> true
    | I.Decl (M, M.Bot), 1 -> false
    | I.Decl (M, _), k -> checkVar (M, k - 1)

  let rec checkExp = function
    | M, I.Uni _ -> true
    | M, I.Pi ((D, P), V) -> checkDec (M, D) && checkExp (I.Decl (M, M.Top), V)
    | M, I.Lam (D, V) -> checkDec (M, D) && checkExp (I.Decl (M, M.Top), V)
    | M, I.Root (I.BVar k, S) -> checkVar (M, k) && checkSpine (M, S)
    | M, I.Root (_, S) -> checkSpine (M, S)

  and checkSpine = function
    | M, I.Nil -> true
    | M, I.App (U, S) -> checkExp (M, U) && checkSpine (M, S)

  and checkDec (M, I.Dec (_, V)) = checkExp (M, V)
  (* copied from meta-abstract *)

  (* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)

  let rec modeEq = function
    | ModeSyn.Marg (ModeSyn.Plus, _), M.Top -> true
    | ModeSyn.Marg (ModeSyn.Minus, _), M.Bot -> true
    | _ -> false
  (*
       The inherit functions below copy the splitting depth attribute
       between successive states, using a simultaneous traversal
       in mode dependency order.

       Invariant:
       (G,M,B) |- V type
       G = G0, G1, G2
       |G2| = k       (length of local context)
       d = |G1, G2|   (last BVar seen)
       let n < |G|
       if   n>d then n is an index of a variable already seen in mdo
       if   n=d then n is an index of a variable now seen for_sml the first
                     time
       if   n<=k then n is a local parameter
       it is impossible for_sml     k < n < d
    *)

  (* invariants on inheritXXX functions? -fp *)

  let rec inheritBelow = function
    | b', k', I.Lam (D', U'), Bdd' ->
        inheritBelow (b', k' + 1, U', inheritBelowDec (b', k', D', Bdd'))
    | b', k', I.Pi ((D', _), V'), Bdd' ->
        inheritBelow (b', k' + 1, V', inheritBelowDec (b', k', D', Bdd'))
    | b', k', I.Root (I.BVar n', S'), (B', d, d') ->
        if n' = k' + d' && n' > k' (* necessary for_sml d' = 0 *) then
          inheritBelowSpine (b', k', S', (I.Decl (B', b'), d, d' - 1))
        else inheritBelowSpine (b', k', S', (B', d, d'))
    | b', k', I.Root (C, S'), Bdd' -> inheritBelowSpine (b', k', S', Bdd')

  and inheritBelowSpine = function
    | b', k', I.Nil, Bdd' -> Bdd'
    | b', k', I.App (U', S'), Bdd' ->
        inheritBelowSpine (b', k', S', inheritBelow (b', k', U', Bdd'))

  and inheritBelowDec (b', k', I.Dec (x, V'), Bdd') =
    inheritBelow (b', k', V', Bdd')
  (* skip *)

  let rec skip = function
    | k, I.Lam (D, U), Bdd' -> skip (k + 1, U, skipDec (k, D, Bdd'))
    | k, I.Pi ((D, _), V), Bdd' -> skip (k + 1, V, skipDec (k, D, Bdd'))
    | k, I.Root (I.BVar n, S), (B', d, d') ->
        if n = k + d && n > k (* necessary for_sml d = 0 *) then
          skipSpine (k, S, (B', d - 1, d'))
        else skipSpine (k, S, (B', d, d'))
    | k, I.Root (C, S), Bdd' -> skipSpine (k, S, Bdd')

  and skipSpine = function
    | k, I.Nil, Bdd' -> Bdd'
    | k, I.App (U, S), Bdd' -> skipSpine (k, S, skip (k, U, Bdd'))

  and skipDec (k, I.Dec (x, V), Bdd') = skip (k, V, Bdd')
  (* Uni impossible *)

  let rec inheritExp = function
    | B, k, I.Lam (D, U), k', I.Lam (D', U'), Bdd' ->
        inheritExp (B, k + 1, U, k' + 1, U', inheritDec (B, k, D, k', D', Bdd'))
    | B, k, I.Pi ((D, _), V), k', I.Pi ((D', _), V'), Bdd' ->
        inheritExp (B, k + 1, V, k' + 1, V', inheritDec (B, k, D, k', D', Bdd'))
    | B, k, V, k', V', (B', d, d') ->
        if n = k + d && n > k (* new original variable *) then
          (* inheritBelow (I.ctxLookup (B, n-k) - 1, k', V', (B', d-1, d')) *)
          skipSpine
            ( k,
              S,
              inheritNewRoot
                (B, I.ctxLookup (B, n - k), k, V, k', V', (B', d, d')) )
        else if n > k + d (* already seen original variable *)
        (* then (B', d, d') *)
        (* previous line avoids redundancy,
                  but may violate invariant outside pattern fragment *)
        then
          skipSpine
            ( k,
              S,
              inheritBelow (I.ctxLookup (B, n - k) - 1, k', V', (B', d, d')) )
        else (* must correspond *)
          (* C' = BVar (n) *)
          let (I.Root (C', S')) = V' in
          inheritSpine (B, k, S, k', S', (B', d, d'))
    | B, k, I.Root (C, S), k', I.Root (C', S'), Bdd' ->
        inheritSpine (B, k, S, k', S', Bdd')

  and inheritNewRoot = function
    | B, b, k, I.Root (I.BVar n, S), k', V', (B', d, d') ->
        if
          n' = k' + d'
          && n' > k' (* n' also new --- same variable: do not decrease *)
        then inheritBelow (b, k', V', (B', d - 1, d'))
        else inheritBelow (b - 1, k', V', (B', d - 1, d'))
    | B, b, k, V, k', V', (B', d, d') ->
        inheritBelow (b - 1, k', V', (B', d - 1, d'))

  and inheritSpine = function
    | B, k, I.Nil, k', I.Nil, Bdd' -> Bdd'
    | B, k, I.App (U, S), k', I.App (U', S'), Bdd' ->
        inheritSpine (B, k, S, k', S', inheritExp (B, k, U, k', U', Bdd'))

  and inheritDec (B, k, I.Dec (_, V), k', I.Dec (_, V'), Bdd') =
    inheritExp (B, k, V, k', V', Bdd')

  let rec inheritDTop = function
    | ( B,
        k,
        I.Pi ((I.Dec (_, V1), I.No), V2),
        k',
        I.Pi ((I.Dec (_, V1'), I.No), V2'),
        Bdd' ) ->
        inheritG
          (B, k, V1, k', V1', inheritDTop (B, k + 1, V2, k' + 1, V2', Bdd'))
    | B, k, V, k', V', Bdd' ->
        let mS = valOf (ModeTable.modeLookup cid) in
        inheritSpineMode (M.Top, mS, B, k, S, k', S', Bdd')

  and inheritDBot = function
    | ( B,
        k,
        I.Pi ((I.Dec (_, V1), I.No), V2),
        k',
        I.Pi ((I.Dec (_, V1'), I.No), V2'),
        Bdd' ) ->
        inheritDBot (B, k + 1, V2, k' + 1, V2', Bdd')
    | B, k, I.Root (I.Const cid, S), k', I.Root (I.Const cid', S'), Bdd' ->
        let mS = valOf (ModeTable.modeLookup cid) in
        inheritSpineMode (M.Bot, mS, B, k, S, k', S', Bdd')

  and inheritG (B, k, I.Root (I.Const cid, S), k', V', Bdd') =
    let mS = valOf (ModeTable.modeLookup cid) in
    (* mode dependency in Goal: first M.Top, then M.Bot *)
    inheritSpineMode
      ( M.Bot,
        mS,
        B,
        k,
        S,
        k',
        S',
        inheritSpineMode (M.Top, mS, B, k, S, k', S', Bdd') )

  and inheritSpineMode = function
    | mode, ModeSyn.Mnil, B, k, I.Nil, k', I.Nil, Bdd' -> Bdd'
    | mode, ModeSyn.Mapp (m, mS), B, k, I.App (U, S), k', I.App (U', S'), Bdd'
      ->
        if modeEq (m, mode) then
          inheritSpineMode
            (mode, mS, B, k, S, k', S', inheritExp (B, k, U, k', U', Bdd'))
        else inheritSpineMode (mode, mS, B, k, S, k', S', Bdd')

  let rec inheritSplitDepth S S' =
    (* S' *)
    (* current first occurrence depth in V *)
    (* current first occurrence depth in V' *)
    (* mode dependency in Clause: first M.Top then M.Bot *)
    (* check proper traversal *)
    let d = I.ctxLength G in
    let d' = I.ctxLength G' in
    let V = Whnf.normalize (V, I.id) in
    let V' = Whnf.normalize (V', I.id) in
    let B'', 0, 0 =
      inheritDBot (B, 0, V, 0, V', inheritDTop (B, 0, V, 0, V', (I.Null, d, d')))
    in
    M.State (name', M.Prefix (G', M', B''), V')
  (* abstractInit (M.State (name, M.Prefix (G, M, B), V)) = F'

       State is the state before splitting, to inherit splitting depths.
       Invariant:
       If   G |- V : L
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   following holds: S' = F' (name', G', M', s')
                                    S' is a new state
    *)

  let rec abstractInit (M.State (name, GM, V)) (name', M.Prefix (G', M', B'), s')
      =
    inheritSplitDepth
      ( M.State (name, GM, V),
        MetaAbstract.abstract
          (M.State (name ^ name', M.Prefix (G', M', B'), I.EClo (V, s'))) )
  (* abstractInit (x:D, mode, F) = F'

       Invariant:
       If   G |- D : L
       and  forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   S' = F (name', G', M', s')
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            then   following holds: S' = F (name', (G', D[s]) , (M', mode) , 1 . s' o ^)
                                    is a new state
    *)

  let rec abstractCont ((D, mode, b), abstract)
      (name', M.Prefix (G', M', B'), s') =
    abstract
      ( name',
        M.Prefix
          (I.Decl (G', I.decSub (D, s')), I.Decl (M', mode), I.Decl (B', b)),
        I.dot1 s' )

  let rec makeAddressInit S k = (S, k)
  let rec makeAddressCont makeAddress k = makeAddress (k + 1)
  (* expand' (M.Prefix (G, M), isIndex, abstract, makeAddress) = (M.Prefix (G', M'), s', ops')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract, dynamic abstraction function
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then |- G' ctx
       and  G' |- M' mtx
       and  G' is a subcontext of G where all Top variables have been replaced
            by EVars'
       and  G' |- s' : G
       and  ops' is a list of all possiblie splitting operators
    *)

  let rec expand' = function
    | M.Prefix (I.Null, I.Null, I.Null), isIndex, abstract, makeAddress ->
        (M.Prefix (I.Null, I.Null, I.Null), I.id, [])
    | ( M.Prefix (I.Decl (G, D), I.Decl (M, mode), I.Decl (B, b)),
        isIndex,
        abstract,
        makeAddress ) ->
        let M.Prefix (G', M', B'), s', ops =
          expand'
            ( M.Prefix (G, M, B),
              isIndexSucc (D, isIndex),
              abstractCont ((D, mode, b), abstract),
              makeAddressCont makeAddress )
        in
        let (I.Dec (xOpt, V)) = D in
        let X = I.newEVar (G', I.EClo (V, s')) in
        let ops' =
          if
            b > 0 (* check if splitting bound > 0 *)
            && (not (isIndex 1))
            && checkDec (M, D)
          then
            (makeAddress 1, split (M.Prefix (G', M', B'), (D, s'), abstract))
            :: ops
          else ops
        in
        (M.Prefix (G', M', B'), I.Dot (I.Exp X, s'), ops')
    | ( M.Prefix (I.Decl (G, D), I.Decl (M, mode), I.Decl (B, b)),
        isIndex,
        abstract,
        makeAddress ) ->
        let M.Prefix (G', M', B'), s', ops =
          expand'
            ( M.Prefix (G, M, B),
              isIndexSucc (D, isIndex) (* -###- *),
              abstractCont ((D, mode, b), abstract),
              makeAddressCont makeAddress )
        in
        ( M.Prefix
            (I.Decl (G', I.decSub (D, s')), I.Decl (M', M.Bot), I.Decl (B', b))
          (* b = 0 *),
          I.dot1 s',
          ops )
  (* expand ((G, M), V) = ops'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : L
       then ops' is a list of all possiblie splitting operators
    *)

  let rec expand S =
    let _, _, ops =
      expand'
        (M.Prefix (G, M, B), isIndexInit, abstractInit S, makeAddressInit S)
    in
    ops
  (* index (Op) = k

       Invariant:
       If   Op = (_, S) then k = |S|
    *)

  let rec index _ Sl = List.length Sl
  (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl) then Sl' = Sl
    *)

  let rec apply _ Sl =
    map
      (function
        | Active S -> S
        | InActive -> raise (Error "Not applicable: leftover constraints"))
      Sl
  (* menu (Op) = s'

       Invariant:
       If   Op = ((G, D), Sl)
       and  G |- D : L
       then s' = string describing the operator
    *)

  let rec menu Op =
    let rec active = function
      | [], n -> n
      | InActive :: L, n -> active (L, n)
      | Active _ :: L, n -> active (L, n + 1)
    in
    let rec inactive = function
      | [], n -> n
      | InActive :: L, n -> inactive (L, n + 1)
      | Active _ :: L, n -> inactive (L, n)
    in
    let rec indexToString = function
      | 0 -> "zero cases"
      | 1 -> "1 case"
      | n -> Int.toString n ^ " cases"
    in
    let rec flagToString = function
      | _, 0 -> ""
      | n, m ->
          " [active: " ^ Int.toString n ^ " inactive: " ^ Int.toString m ^ "]"
    in
    "Splitting : "
    ^ Print.decToString (G, I.ctxDec (G, i))
    ^ " ("
    ^ indexToString (index Op)
    ^ flagToString (active (Sl, 0), inactive (Sl, 0))
    ^ ")"

  let rec var ((_, i), _) = i
  let expand = expand
  let apply = apply
  let var = var
  let index = index
  let menu = menu
  (* local *)
end

(* functor Splitting *)
