open Basis

(* Converter from relational representation to a functional
   representation of proof terms *)

(* Author: Carsten Schuermann *)

module type RELFUN = sig
  (*! structure FunSyn : Funsyn.FUNSYN !*)
  exception Error of string

  val convertFor : IntSyn.cid list -> FunSyn.for_sml
  val convertPro : IntSyn.cid list -> FunSyn.pro
end

(* Signature RELFUN *)
(* Converter from relational representation to a functional
   representation of proof terms *)

(* Author: Carsten Schuermann *)

module RelFun
    (Global : Global.GLOBAL)
    (ModeTable : Modetable.MODETABLE)
    (Names : Names.NAMES)
    (Unify : Unify.UNIFY)
    (Whnf : Whnf.WHNF)
    (Weaken : Weaken.Weaken.WEAKEN)
    (TypeCheck : Typecheck.TYPECHECK)
    (FunWeaken : Funweaken.FUNWEAKEN)
    (FunNames : Funnames.FUNNAMES) : RELFUN = struct
  (*! structure FunSyn = FunSyn' !*)

  exception Error of string

  module F = FunSyn
  module I = IntSyn
  module M = ModeSyn
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
    let rec convertFor' = function
      | I.Pi ((D, _), V), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n ->
          let F', F'' =
            convertFor' (V, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n - 1)
          in
          fun F -> (F.All (F.Prim (Weaken.strengthenDec (D, w1)), F' F), F'')
      | I.Pi ((D, _), V), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n ->
          let F', F'' =
            convertFor' (V, mS, I.comp (w1, I.shift), I.dot1 w2, n + 1)
          in
          (F', F.Ex (I.decSub (D, w2), F''))
      | I.Uni I.Type, M.Mnil, _, _, _ -> fun F -> (F, F.True)
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
  (* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)

  let rec convertFor = function
    | [] -> raise (Error "Empty theorem")
    | [ a ] -> convertOneFor a
    | a :: L -> F.And (convertOneFor a, convertFor L)
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
          (fun U B -> B || occursInExpN (k, Whnf.normalize (U, I.id)))
          false

  and occursInHead = function
    | k, I.BVar k' -> k = k'
    | k, I.Const _ -> false
    | k, I.Def _ -> false
    | k, I.FgnConst _ -> false

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

  let rec dot1inv w = Weaken.strengthenSub (I.comp (I.shift, w), I.shift)
  (* shiftinv (w) = w'

       Invariant:
       If   G, A |- w : G'
       and  1 does not occur in w
       then w  = w' o ^
    *)

  let rec shiftinv w = Weaken.strengthenSub (w, I.shift)
  let rec eqIdx = function I.Idx n, I.Idx k -> n = k | _ -> false

  let rec peel w =
    if eqIdx (I.bvarSub (1, w), I.Idx 1) then dot1inv w else shiftinv w

  let rec peeln = function 0, w -> w | n, w -> peeln (n - 1, peel w)
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
  (* strenghten (Psi, (a, S), w, m) = (Psi', w')

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  |- Psi2 ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1
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
    let mS =
      match ModeTable.modeLookup a with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS
    in
    let rec args = function
      | I.Nil, M.Mnil -> []
      | I.App (U, S'), M.Mapp (M.Marg (m', _), mS) -> (
          let L = args (S', mS) in
          match M.modeEqual (m, m') with true -> U :: L | false -> L)
    in
    let rec strengthenArgs = function
      | [], s -> []
      | U :: L, s -> Weaken.strengthenExp (U, s) :: strengthenArgs (L, s)
    in
    let rec occursInArgs = function
      | n, [] -> false
      | n, U :: L -> occursInExp (n, U) || occursInArgs (n, L)
    in
    let rec occursInPsi = function
      | n, ([], L) -> occursInArgs (n, L)
      | n, (F.Prim (I.Dec (_, V)) :: Psi1, L) ->
          occursInExp (n, V) || occursInPsi (n + 1, (Psi1, L))
      | n, (F.Block (F.CtxBlock (l, G)) :: Psi1, L) ->
          occursInG (n, G, fun n' -> occursInPsi (n', (Psi1, L)))
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
          if eqIdx (I.bvarSub (1, w1), I.Idx 1) then
            inBlock (G, (true, dot1inv w1))
          else inBlock (G, (bw, Weaken.strengthenSub (w1, I.shift)))
    in
    let rec blockSub = function
      | I.Null, w -> (I.Null, w)
      | I.Decl (G, I.Dec (name, V)), w ->
          let G', w' = blockSub (G, w) in
          let V' = Weaken.strengthenExp (V, w') in
          (I.Decl (G', I.Dec (name, V')), I.dot1 w')
    in
    let rec strengthen' = function
      | I.Null, Psi2, L, w1 (* =  I.id *) -> (I.Null, I.id)
      | I.Decl (Psi1, LD), Psi2, L, w1 ->
          let bw, w1' =
            if eqIdx (I.bvarSub (1, w1), I.Idx 1) then (true, dot1inv w1)
            else (false, Weaken.strengthenSub (w1, I.shift))
          in
          if bw || occursInPsi (1, (Psi2, L)) then
            let Psi1', w' = strengthen' (Psi1, LD :: Psi2, L, w1') in
            let V' = Weaken.strengthenExp (V, w') in
            (I.Decl (Psi1', F.Prim (I.Dec (name, V'))), I.dot1 w')
          else
            let w2 = I.shift in
            let Psi2', w2' = FunWeaken.strengthenPsi' (Psi2, w2) in
            let L' = strengthenArgs (L, w2') in
            let Psi1'', w' = strengthen' (Psi1, Psi2', L', w1') in
            (Psi1'', I.comp (w', I.shift))
      | I.Decl (Psi1, LD), Psi2, L, w1 ->
          let bw, w1' = inBlock (G, (false, w1)) in
          if bw || occursBlock (G, (Psi2, L)) then
            let Psi1', w' = strengthen' (Psi1, LD :: Psi2, L, w1') in
            let G'', w'' = blockSub (G, w') in
            (I.Decl (Psi1', F.Block (F.CtxBlock (name, G''))), w'')
          else
            let w2 = I.Shift (I.ctxLength G) in
            let Psi2', w2' = FunWeaken.strengthenPsi' (Psi2, w2) in
            let L' = strengthenArgs (L, w2') in
            strengthen' (Psi1, Psi2', L', w1')
    in
    strengthen' (Psi, [], args (S, mS), w)

  let rec recursion L =
    let F = convertFor L in
    let rec name = function
      | [ a ] -> I.conDecName (I.sgnLookup a)
      | a :: L -> I.conDecName (I.sgnLookup a) ^ "/" ^ name L
    in
    fun p -> F.Rec (F.MDec (Some (name L), F), p)
  (* abstract a = P'

       Invariant:
       If   a is a type family
       and  Sigma (a) = {x1:A1}..{xn:An} type
       then for_sml all P s.t.
            +x1:A1, .., +xn:An; . |- P in [[-x1:A1]] .. [[-xn:An]] true
            . ;. |- (P' P) in [[+x1:A1]] .. [[+xn:An]] [[-x1:A1]] .. [[-xn:An]] true
    *)

  let rec abstract a =
    (* abstract' ((V, mS), w) = P'

           Invariant:
           If  Sigma (a) = {x1:A1} .. {xn:An} type
           and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
           and  Gamma= x1:A1, .. x(j-1):A(j-1)
           and  Gamma |- w : Gamma+
           then P' is a Lam abstraction
        *)
    let mS =
      match ModeTable.modeLookup a with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS
    in
    let V =
      match I.sgnLookup a with
      | I.ConDec (name, _, _, _, V, I.Kind) -> V
      | _ -> raise (Error "Type Constant declaration expected")
    in
    let rec abstract' = function
      | (_, M.Mnil), w -> fun p -> p
      | (I.Pi ((D, _), V2), M.Mapp (M.Marg (M.Plus, _), mS)), w ->
          let D' = Weaken.strengthenDec (D, w) in
          let P = abstract' ((V2, mS), I.dot1 w) in
          fun p -> F.Lam (F.Prim D', P p)
      | (I.Pi (_, V2), M.Mapp (M.Marg (M.Minus, _), mS)), w ->
          abstract' ((V2, mS), I.comp (w, I.shift))
    in
    abstract' ((V, mS), I.id)
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

  let rec transformInit (Psi, (a, S), w1) =
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
    let mS =
      match ModeTable.modeLookup a with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS
    in
    let V =
      match I.sgnLookup a with
      | I.ConDec (name, _, _, _, V, I.Kind) -> V
      | _ -> raise (Error "Type Constant declaration expected")
    in
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
          let V1' = Weaken.strengthenExp (V1, w) in
          let w' = I.dot1 w in
          let U' = Weaken.strengthenExp (U, w1) in
          let s' = Whnf.dotEta (I.Exp U', s) in
          transformInit' ((S, mS), V2, (w', s'))
    in
    transformInit' ((S, mS), V, (I.id, I.Shift (F.lfctxLength Psi)))
  (* transformDec (c'', (Psi+-, G0), d, (a, S), w1, w2, t) = (d', w', s', t', Ds)

       Invariant:
       If   |- Psi ctx
       and  Psi |- G0 ctx
       and  d = |Delta|
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi, G0 |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
       and  Psi |- w2 : Psi+-
       and  Psi+- |- t0 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi |- s' : Gamma+
       and  x1:A1 .. xn:An |- w': Gamma+    (w weakening substitution)
       and  Psi+- |- t' : Psi+, -x(k1):{G0} A(k1), ... -x(km):{G0} A(km)
       and  d' = |Delta'|
    *)

  let rec transformDec (Ts, (Psi, G0), d, (a, S), w1, w2, t0) =
    (* raiseExp G U a = U'

           Invariant:
           If   |- Psi ctx         (for_sml some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for_sml some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
        *)
    (* raiseType G U a = U'

           Invariant:
           If   |- Psi ctx         (for_sml some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for_sml some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
           and  Psi, G, x:{{G}} V |- x G : V
        *)
    (* exchangeSub (G0) = s'

           Invariant:
           For some Psi, some G, some V:
           Psi, V, G0 |- s' : Psi, G0, V
        *)
    (* transformDec' (d, (S, mS), V, (z1, z2), (w, t)) = (d', w', t', (Ds+, Ds-))

           Invariant:
           If   Psi, G0 |- S : V > type
           and  S doesn't contain Skolem constants
           and  d = |Delta|
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
           and  Psi |- w2 : Psi+-
           and  Psi+- |- t : Psi+, -x1:{{G0}} A1... -xj:{{G0}} Aj
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1) |- z1: Psi+
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1), G0 |- z2: x1:A1...x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+- |- s' : +x1:A1 .. +xn:An
           and  Psi+- |- t' : Psi+, -x1:{{G0}} A1... -xn:{{G0}} An
           and  d' = |Delta'|
        *)
    (* head Ts (w, t, (d, Dplus, Dminus)) = (d', w', t', P')

             Invariant:
             If   a not in Ts  then d'= d+1,  P' makes a lemma call
             If   Ts = [a]     then d'= d     P' used directly the ih.
             If   Ts = a1 .. ai ... and ai = a
             then d' = d+i   and P' select ih, and then decomposes is, using
                  (i-1) Rights and 1 Left
          *)
    let mS =
      match ModeTable.modeLookup a with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS
    in
    let V =
      match I.sgnLookup a with
      | I.ConDec (name, _, _, _, V, I.Kind) -> V
      | _ -> raise (Error "Type Constant declaration expected")
    in
    let rec raiseExp G U a =
      (* raiseExp G = (w', k)

               Invariant:
               If   |-  Psi ctx
               and  Psi |- G ctx
               and  Psi |- G' ctx   which ARE subordinate to a
               then Psi, G |- w : Psi, G'
               and  k is a continuation calculuting the right exprssion:
                    for_sml all U, s.t. Psi, G |- U : V
                    Psi |- [[G']] U : {{G'}} V
            *)
      let rec raiseExp' = function
        | I.Null -> (I.id, fun x -> x)
        | I.Decl (G, D) ->
            let w, k = raiseExp' G in
            if Subordinate.belowEq (I.targetFam V, a) then
              (I.dot1 w, fun x -> k (I.Lam (Weaken.strengthenDec (D, w), x)))
            else (I.comp (w, I.shift), k)
      in
      let w, k = raiseExp' G in
      k (Weaken.strengthenExp (U, w))
    in
    let rec raiseType G U a =
      (* raiseType G n = (w', k, S')

              Invariant:
              If   |-  Psi ctx
              and  Psi |- G, Gv ctx
              and  Psi |- G' ctx   which ARE subordinate to a
              and  n = |Gv| + 1
              then Psi, G |- w : Psi, G'
              and  k is a continuation calculating the right exprssion:
                   for_sml all U, s.t. Psi, G |- U : V
                   Psi |- [[G']] U : {{G'}} V
              and  k' is a continuation calculating the corresponding spine:
                   for_sml all S, s.t. Psi, G, G0,|- ... refine
            *)
      let rec raiseType' = function
        | I.Null, n -> (I.id, fun x -> (x, fun S -> S))
        | I.Decl (G, D), n ->
            let w, k, k' = raiseType' (G, n + 1) in
            if Subordinate.belowEq (I.targetFam V, a) then
              ( I.dot1 w,
                fun x ->
                  ( k (I.Pi ((Weaken.strengthenDec (D, w), I.Maybe), x)),
                    fun S -> I.App (I.Root (I.BVar n, I.Nil), S) ) )
            else (I.comp (w, I.shift), k, k')
      in
      let w, k, k' = raiseType' (G, 2) in
      (k (Weaken.strengthenExp (U, w)), I.Root (I.BVar 1, k' I.Nil))
    in
    let rec exchangeSub G0 =
      let g0 = I.ctxLength G0 in
      let rec exchangeSub' = function
        | 0, s -> s
        | k, s -> exchangeSub' (k - 1, I.Dot (I.Idx k, s))
      in
      I.Dot (I.Idx (g0 + 1), exchangeSub' (g0, I.Shift (g0 + 1)))
    in
    let rec transformDec' = function
      | d, (I.Nil, M.Mnil), I.Uni I.Type, (z1, z2), (w, t) ->
          (w, t, (d, fun k Ds -> (Ds k, fun _ -> F.Empty)))
      | ( d,
          (I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS)),
          I.Pi ((I.Dec (_, V1), DP), V2),
          (z1, z2),
          (w, t) ) ->
          let g = I.ctxLength G0 in
          let w1' = peeln (g, w1) in
          let G1, _ = Weaken.strengthenCtx (G0, w1') in
          let G2, _ = ctxSub (G1, z1) in
          let V1'', Ur = raiseType (G2, I.EClo (V1, z2), I.targetFam V1) in
          let w' =
            match DP with I.Maybe -> I.dot1 w | I.No -> I.comp (w, I.shift)
          in
          let U0 = raiseExp (G0, U, I.targetFam V1'') in
          let U' = Weaken.strengthenExp (U0, w2) in
          let t' = Whnf.dotEta (I.Exp U', t) in
          let z1' = I.comp (z1, I.shift) in
          let xc = exchangeSub G0 in
          let z2n = I.comp (z2, I.comp (I.shift, xc)) in
          let Ur' = I.EClo (Ur, xc) in
          let z2' = Whnf.dotEta (I.Exp Ur', z2n) in
          let w'', t'', (d', Dplus, Dminus) =
            transformDec' (d + 1, (S, mS), V2, (z1', z2'), (w', t'))
          in
          (w'', t'', (d', Dplus, fun k -> F.Split (k, Dminus 1)))
      | ( d,
          (I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS)),
          I.Pi ((I.Dec (name, V1), _), V2),
          (z1, z2),
          (w, t) ) ->
          let V1' = Weaken.strengthenExp (V1, w) in
          let w' = I.dot1 w in
          let U' = Weaken.strengthenExp (U, w1) in
          let t' = t in
          let z1' = F.dot1n (G0, z1) in
          let z2' = I.Dot (I.Exp (I.EClo (U', z1')), z2) in
          let w'', t'', (d', Dplus, Dminus) =
            transformDec' (d + 1, (S, mS), V2, (z1, z2'), (w', t'))
          in
          (w'', t'', (d', fun k Ds -> (F.App ((k, U'), Dplus (1, Ds)), Dminus)))
    in
    let w'', t'', (d', Dplus, Dminus) =
      transformDec'
        ( d,
          (S, mS),
          V,
          (I.id, I.Shift (domain (Psi, t0) + I.ctxLength G0)),
          (I.id, t0) )
    in
    let rec varHead Ts (w'', t'', (d', Dplus, Dminus)) =
      let rec head' = function
        | [ a' ], d1, k1 -> (d1, k1)
        | a' :: Ts', d1, k1 ->
            if a = a' then (d1 + 1, fun xx -> F.Left (xx, k1 1))
            else
              let d2, k2 = head' (Ts', d1 + 1, k1) in
              (d2, fun xx -> F.Right (xx, k2 1))
      in
      let d2, k2 = head' (Ts, d', fun xx -> Dplus (xx, Dminus)) in
      (d2, w'', t'', k2 d)
    in
    let rec lemmaHead (w'', t'', (d', Dplus, Dminus)) =
      let name = I.conDecName (I.sgnLookup a) in
      let l =
        match FunNames.nameLookup name with
        | None -> raise (Error ("Lemma " ^ name ^ " not defined"))
        | Some lemma -> lemma
      in
      (d' + 1, w'', t'', F.Lemma (l, Dplus (1, Dminus)))
    in
    if List.exists (fun x -> x = a) Ts then
      varHead Ts (w'', t'', (d', Dplus, Dminus))
    else lemmaHead (w'', t'', (d', Dplus, Dminus))
  (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)

  let rec transformConc ((a, S), w) =
    let mS =
      match ModeTable.modeLookup a with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS
    in
    let rec transformConc' = function
      | I.Nil, M.Mnil -> F.Unit
      | I.App (U, S'), M.Mapp (M.Marg (M.Plus, _), mS') ->
          transformConc' (S', mS')
      | I.App (U, S'), M.Mapp (M.Marg (M.Minus, _), mS') ->
          F.Inx (Weaken.strengthenExp (U, w), transformConc' (S', mS'))
    in
    transformConc' (S, mS)
  (* traverse Ts c = L'

       Invariant:
       If   Ts is a list of type families
       and  c is a type family which entries are currently traversed
       then L' is a list of cases
    *)

  let rec traverse Ts c =
    (* traverseNeg (c'', Psi, (V, v), L) = ([w', d', PQ'], L')    [] means optional

           Invariant:
           If   Psi0 |- V : type
           and  Psi0 |- v : Psi
           and  V[v^-1] does not contain Skolem constants
           and  c'' is the name of the object constant currently considered
           and  L is a list of cases
           then L' list of cases and CL' extends CL
           and  Psi |- w' : Psi'   (Psi' is the context of all variables considered so far)
           and  d' is the length of Delta
           and  PQ'  is a pair, generating the proof term
        *)
    let rec traverseNeg = function
      | c'', Psi, (I.Pi ((D, I.Maybe), V2), v), L -> (
          match
            traverseNeg
              ( c'',
                I.Decl (Psi, F.Prim (Weaken.strengthenDec (D, v)))
                (*                                   (Names.decName (F.makectx Psi, Weaken.strengthenDec (D, v)))),
*),
                (V2, I.dot1 v),
                L )
          with
          | Some (w', d', PQ'), L' -> (Some (peel w', d', PQ'), L')
          | None, L' -> (None, L'))
      | c'', Psi, (I.Pi ((D, I.No), V2), v), L -> (
          match traverseNeg (c'', Psi, (V2, I.comp (v, I.shift)), L) with
          | Some (w', d', PQ'), L' ->
              traversePos
                ( c'',
                  Psi,
                  I.Null,
                  (Weaken.strengthenExp (V1, v), I.id),
                  Some (w', d', PQ'),
                  L' )
          | None, L' ->
              traversePos
                ( c'',
                  Psi,
                  I.Null,
                  (Weaken.strengthenExp (V1, v), I.id),
                  None,
                  L' ))
      | c'', Psi, (V, v), L ->
          if c = c' then
            (* Clause head found *)
            let S' = Weaken.strengthenSpine (S, v) in
            let Psi', w' =
              strengthen (Psi, (c', S'), I.Shift (F.lfctxLength Psi), M.Plus)
            in
            let w'', s'' = transformInit (Psi', (c', S'), w') in
            ( Some
                ( w',
                  1,
                  fun p ->
                    ((Psi', s'', p), fun wf -> transformConc ((c', S'), wf)) ),
              L )
          else (None, L)
    and traversePos = function
      | c'', Psi, G, (I.Pi ((D, I.Maybe), V2), v), Some (w, d, PQ), L -> (
          match
            traversePos
              ( c'',
                Psi,
                I.Decl (G, Weaken.strengthenDec (D, v)),
                (V2, I.dot1 v),
                Some (I.dot1 w, d, PQ),
                L )
          with
          | Some (w', d', PQ'), L' -> (Some (w', d', PQ'), L'))
      | c'', Psi, G, (I.Pi ((D, I.No), V2), v), Some (w, d, PQ), L -> (
          match
            traversePos
              (c'', Psi, G, (V2, I.comp (v, I.shift)), Some (w, d, PQ), L)
          with
          | Some (w', d', PQ'), L' -> (
              match
                traverseNeg
                  ( c'',
                    I.Decl (Psi, F.Block (F.CtxBlock (None, G))),
                    (V1, v),
                    L' )
              with
              | Some (w'', d'', (P'', Q'')), L'' ->
                  (Some (w', d', PQ'), P'' (Q'' w'') :: L'')
              | None, L'' -> (Some (w', d', PQ'), L'')))
      | c'', Psi, I.Null, (V, v), Some (w1, d, (P, Q)), L ->
          (* Lemma calls (no context block) *)
          (* provide typeCheckCtx from typecheck *)
          let (I.Root (I.Const a', S)) =
            Whnf.normalize (Weaken.strengthenExp (V, v), I.id)
          in
          let Psi', w2 = strengthen (Psi, (a', S), w1, M.Minus) in
          let _ =
            if !Global.doubleCheck then
              TypeCheck.typeCheck (F.makectx Psi', (I.Uni I.Type, I.Uni I.Kind))
            else ()
          in
          let w3 = Weaken.strengthenSub (w1, w2) in
          let d4, w4, t4, Ds =
            transformDec (Ts, (Psi', I.Null), d, (a', S), w1, w2, w3)
          in
          ( Some
              ( w2,
                d4,
                fun p -> (P (F.Let (Ds, F.Case (F.Opts [ (Psi', t4, p) ]))), Q)
              ),
            L )
      | c'', Psi, G, (V, v), Some (w1, d, (P, Q)), L ->
          (* Lemma calls (under a context block) *)
          (* provide typeCheckCtx from typecheck *)
          (* change w1 to w1' and w2 to w2' below *)
          let (I.Root (I.Const a', S)) = Weaken.strengthenExp (V, v) in
          let dummy, w2 =
            strengthen
              ( I.Decl (Psi, F.Block (F.CtxBlock (None, G))),
                (a', S),
                w1,
                M.Minus )
          in
          let _ =
            if !Global.doubleCheck then
              TypeCheck.typeCheck (F.makectx dummy, (I.Uni I.Type, I.Uni I.Kind))
            else ()
          in
          let g = I.ctxLength G in
          let w1' = peeln (g, w1) in
          let w2' = peeln (g, w2) in
          let G1, _ = Weaken.strengthenCtx (G, w1') in
          let w3 = Weaken.strengthenSub (w1', w2') in
          let d4, w4, t4, Ds =
            transformDec (Ts, (Psi', G), d, (a', S), w1, w2', w3)
          in
          ( Some
              ( w2',
                d4,
                fun p ->
                  ( P
                      (F.Let
                         ( F.New (F.CtxBlock (None, G1), Ds),
                           F.Case (F.Opts [ (Psi', t4, p) ]) )),
                    Q ) ),
            L )
      | c'', Psi, G, (I.Pi ((D, I.Maybe), V2), v), None, L ->
          traversePos
            ( c'',
              Psi,
              I.Decl (G, Weaken.strengthenDec (D, v)),
              (V2, I.dot1 v),
              None,
              L )
      | c'', Psi, G, (I.Pi ((D, I.No), V2), v), None, L -> (
          match
            traversePos (c'', Psi, G, (V2, I.comp (v, I.shift)), None, L)
          with
          | None, L' -> (
              match
                traverseNeg
                  ( c'',
                    I.Decl (Psi, F.Block (F.CtxBlock (None, G))),
                    (V1, v),
                    L' )
              with
              | Some (w'', d'', (P'', Q'')), L'' -> (None, P'' (Q'' w'') :: L'')
              | None, L'' -> (None, L'')))
      | c'', Psi, G, (V, v), None, L -> (None, L)
    in
    let rec traverseSig' c'' L =
      if c'' = 1 (I.sgnSize ()) then L
      else
        match I.sgnLookup c'' with
        | I.ConDec (name, _, _, _, V, I.Type) -> (
            match traverseNeg (c'', I.Null, (V, I.id), L) with
            | Some (wf, d', (P', Q')), L' ->
                traverseSig' (c'' + 1, P' (Q' wf) :: L')
            | None, L' -> traverseSig' (c'' + 1, L'))
        | _ -> traverseSig' (c'' + 1, L)
    in
    traverseSig' (0, [])
  (* convertPro Ts = P'

       Invariant:
       If   Ts is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in Ts into functional form
    *)

  let rec convertPro Ts =
    let rec convertOnePro a =
      let V =
        match I.sgnLookup a with
        | I.ConDec (name, _, _, _, V, I.Kind) -> V
        | _ -> raise (Error "Type Constant declaration expected")
      in
      let mS =
        match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
      in
      let P = abstract a in
      P (F.Case (F.Opts (traverse Ts a)))
    in
    let rec convertPro' = function
      | [] -> raise (Error "Cannot convert Empty program")
      | [ a ] -> convertOnePro a
      | a :: Ts' -> F.Pair (convertOnePro a, convertPro' Ts')
    in
    let R = recursion Ts in
    R (convertPro' Ts)

  let convertFor = convertFor
  let convertPro = convertPro
  let traverse = traverse
end

(* functor FunSyn *)
