(* Abstraction *)


(* Author: Frank Pfenning, Carsten Schuermann *)


(* Modified: Roberto Virga, Brigitte Pientka *)


module AbstractTabled (Whnf : WHNF) (Unify : UNIFY) (Constraints : CONSTRAINTS) (Subordinate : SUBORDINATE) (Print : PRINT) (Conv : CONV) : ABSTRACTTABLED = struct (*! structure IntSyn = IntSyn' !*)

(*! structure TableParam = TableParam !*)

exception Error of string
module I = IntSyn
module C = CompSyn
type duplicates = AV of (I.exp * int) | FGN of int
type seenIn = TypeLabel | Body
type existVars = EV of I.exp
let rec lengthSub = function (I.Shift n) -> 0 | (I.Dot (E, s)) -> 1 + lengthSub s
(*
       We write {{K}} for_sml the context of K, where EVars have
       been translated to declarations and their occurrences to BVars.
       For each occurrence of EVar in U, we generate a distinct BVar together with
       a residual constraint. This enforces that the final abstraction of U is
       linear. However, we do not linearize the context G.

       We write {{U}}_K, {{S}}_K for_sml the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars in U are collected in K.
       In particular, . ||- U means U contains no EVars.  Similarly,
       for_sml spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

let rec compose' = function (IntSyn.Null, G) -> G | (IntSyn.Decl (G', D), G) -> IntSyn.Decl (compose' (G', G), D)
let rec isId = function (I.Shift (n)) -> (n = 0) | (s) -> isId' (s, 0) | (s) -> isId' (s, 0) | (I.Dot (I.Exp _, s)) -> false
and isId' = function (I.Shift (n), k) -> (n = k) | (I.Dot (I.Idx (i), s), k) -> ( let k' = k + 1 in  (i = k') && isId' (s, k') ) | (I.Dot (I.Undef, s), k) -> isId' (s, k + 1)
let rec equalCtx = function (I.Null, s, I.Null, s') -> true | (I.Decl (G, D), s, I.Decl (G', D'), s') -> Conv.convDec ((D, s), (D', s')) && (equalCtx (G, I.dot1 s, G', I.dot1 s')) | (I.Decl (G, D), s, I.Null, s') -> false | (I.Null, s, I.Decl (G', D'), s') -> false
(* eqEVar X Y = B
     where B iff X and Y represent same variable
     *)

let rec eqEVarW = function ((I.EVar (r1, _, _, _)), (EV (I.EVar (r2, _, _, _)))) -> (r1 = r2) | (_, _) -> false
let rec eqEVar X1 (EV (X2))  = (* Sun Dec  1 14:04:17 2002 -bp  may raise exception
       if strengthening is applied,i.e. the substitution is not always id! *)
 ( let (X1', s) = Whnf.whnf (X1, I.id) in let (X2', s) = Whnf.whnf (X2, I.id) in  eqEVarW X1' (EV (X2')) )
(* a few helper functions to manage K *)

(* member P K = B option *)

let rec member' P K  = ( let rec exists' = function (I.Null) -> None | (I.Decl (K', (l, EV (Y)))) -> if P (EV (Y)) then Some (l) else exists' (K') in  exists' K )
(* member P K = B option *)

let rec member P K  = ( let rec exists' = function (I.Null) -> None | (I.Decl (K', (i, Y))) -> if P (Y) then Some (i) else exists' (K') in  exists' K )
let rec update' P K  = ( let rec update' = function (I.Null) -> I.Null | (I.Decl (K', ((label, Y)))) -> if (P Y) then I.Decl (K', (Body, Y)) else I.Decl (update' (K'), (label, Y)) in  update' K )
(* member P K = B option *)

let rec update P K  = ( let rec update' = function (I.Null) -> I.Null | (I.Decl (K', ((label, i), Y))) -> if (P Y) then I.Decl (K', ((Body, i), Y)) else I.Decl (update' (K'), ((label, i), Y)) in  update' K )
let rec or_ = function (I.Maybe, _) -> I.Maybe | (_, I.Maybe) -> I.Maybe | (I.Meta, _) -> I.Meta | (_, I.Meta) -> I.Meta | (I.No, I.No) -> I.No
(* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place an argument to a Skonst
             DP = Meta    iff k occurs in U and arguments to Skonsts
    *)

let rec occursInExp = function (k, I.Uni _) -> I.No | (k, I.Pi (DP, V)) -> or_ (occursInDecP (k, DP), occursInExp (k + 1, V)) | (k, I.Root (H, S)) -> occursInHead (k, H, occursInSpine (k, S)) | (k, I.Lam (D, V)) -> or_ (occursInDec (k, D), occursInExp (k + 1, V)) | (k, I.FgnExp csfe) -> I.FgnExpStd.fold csfe (fun (U, DP) -> or_ (DP, (occursInExp (k, Whnf.normalize (U, I.id))))) I.No
and occursInHead = function (k, I.BVar (k'), DP) -> if (k = k') then I.Maybe else DP | (k, I.Const _, DP) -> DP | (k, I.Def _, DP) -> DP | (k, I.FgnConst _, DP) -> DP | (k, I.Skonst _, I.No) -> I.No | (k, I.Skonst _, I.Meta) -> I.Meta | (k, I.Skonst _, I.Maybe) -> I.Meta
and occursInSpine = function (_, I.Nil) -> I.No | (k, I.App (U, S)) -> or_ (occursInExp (k, U), occursInSpine (k, S))
and occursInDec (k, I.Dec (_, V))  = occursInExp (k, V)
and occursInDecP (k, (D, _))  = occursInDec (k, D)
(* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)

(* optimize to have fewer traversals? -cs *)

(* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)

let rec piDepend = function (DPV) -> I.Pi DPV | (DPV) -> I.Pi DPV | ((D, I.Maybe), V) -> I.Pi ((D, occursInExp (1, V)), V)
(* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)

let rec raiseType = function (I.Null, V) -> V | (I.Decl (G, D), V) -> raiseType (G, I.Pi ((D, I.Maybe), V))
let rec reverseCtx = function (I.Null, G) -> G | (I.Decl (G, D), G') -> reverseCtx (G, I.Decl (G', D))
let rec ctxToEVarSub = function (IntSyn.Null, s) -> s | (IntSyn.Decl (G, IntSyn.Dec (_, A)), s) -> ( let s' = ctxToEVarSub (G, s) in let X = IntSyn.newEVar (IntSyn.Null, I.EClo (A, s')) in  IntSyn.Dot (IntSyn.Exp (X), s') )
(* collectExpW ((Gs, ss), Gl, (U, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- U : V      (U,s) in whnf
                Gs |- ss : G  (Gs is the strengthened context and ss is the strengthening substitution)

       No circularities in U
             (enforced by extended occurs-check for_sml FVars in Unify)
       and   K' = K, K''
             where K' contains all EVars in (U,s)
       and  DupVars' = DupVars, DupVars''
            where DupVars' contains all duplicates in (U,s)

      if flag = true
        then duplicates of EVars are collected in DupVars
        otherwise no duplicates are collected

      note : 1) we only need to collect duplicate occurrences of EVars
                if we need to linearize the term the EVars occur in.

             2) we do not linearize fgnExp
    *)

(* Possible optimization: Calculate also the normal form of the term *)

let rec collectExpW = function (Gss, Gl, (I.Uni L, s), K, DupVars, flag, d) -> (K, DupVars) | (Gss, Gl, (I.Pi ((D, _), V), s), K, DupVars, flag, d) -> ( let (K', _) = collectDec (Gss, (D, s), (K, DupVars), d, false) in  (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *)
collectExp (Gss, I.Decl (Gl, I.decSub (D, s)), (V, I.dot1 s), K', DupVars, flag, d) ) | (Gss, Gl, (I.Root (_, S), s), K, DupVars, flag, d) -> collectSpine (Gss, Gl, (S, s), K, DupVars, flag, d) | (Gss, Gl, (I.Lam (D, U), s), K, DupVars, flag, d) -> ( let (K', _) = collectDec (Gss, (D, s), (K, DupVars), d, false) in  collectExp (Gss, I.Decl (Gl, I.decSub (D, s)), (U, I.dot1 s), K', DupVars, flag, d + 1) ) | (Gss, Gl, (X, s), K, DupVars, flag, d) -> collectEVar (Gss, Gl, (X, s), K, DupVars, flag, d) | (Gss, Gl, (I.FgnExp csfe, s), K, DupVars, flag, d) -> I.FgnExpStd.fold csfe (fun (U, KD') -> ( let (K', Dup) = KD' in  collectExp (Gss, Gl, (U, s), K', Dup, false, d) )) (K, I.Decl (DupVars, FGN (d)))
and collectExp (Gss, Gl, Us, K, DupVars, flag, d)  = collectExpW (Gss, Gl, Whnf.whnf Us, K, DupVars, flag, d)
and collectSpine = function (Gss, Gl, (I.Nil, _), K, DupVars, flag, d) -> (K, DupVars) | (Gss, Gl, (I.SClo (S, s'), s), K, DupVars, flag, d) -> collectSpine (Gss, Gl, (S, I.comp (s', s)), K, DupVars, flag, d) | (Gss, Gl, (I.App (U, S), s), K, DupVars, flag, d) -> ( let (K', DupVars') = collectExp (Gss, Gl, (U, s), K, DupVars, flag, d) in  collectSpine (Gss, Gl, (S, s), K', DupVars', flag, d) )
and collectEVarFapStr (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)  = match member' (eqEVar X) K with Some (label) -> (* we have seen X before *)
(if flag then collectSub (Gss, Gl, s, K, I.Decl (DupVars, AV (X, d)), flag, d)(* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar X) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *)
(* since X has occurred before, we do not traverse its type V' *)
 else collectSub (Gss, Gl, s, K, DupVars, flag, d)) | None -> ( (*          val V' = raiseType (GX, V) (* inefficient! *)*)
let label = if flag then Body else TypeLabel in let (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d) in  collectSub (Gss, Gl, I.comp (w, s), I.Decl (K', (label, EV (X'))), DupVars', flag, d) )
and collectEVarNFapStr (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)  = match member' (eqEVar X) K with Some (label) -> (* we have seen X before, i.e. it was already strengthened *)
(if flag then collectSub (Gss, Gl, s, K, I.Decl (DupVars, AV (X, d)), flag, d)(* -bp this is a possible optimization for_sml the variant case
                   case label of
                   Body => (print "Collect DupVar\n"; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print "TypeLabel\n"
                      val K' = update' (eqEVar X) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*)
 else collectSub (Gss, Gl, s, K, DupVars, flag, d)) | None -> ( (* val V' = raiseType (GX, V) (* inefficient! *)*)
let label = if flag then Body else TypeLabel in let (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d) in  if flag then collectSub (Gss, Gl, I.comp (w, s), I.Decl (K', (label, EV (X'))), I.Decl (DupVars', AV (X', d)), flag, d) else collectSub (Gss, Gl, I.comp (w, s), I.Decl (K', (label, EV (X'))), DupVars', flag, d) )
and collectEVarStr (Gss, Gl, (X, s), K, DupVars, flag, d)  = ( (* ? *)
let w = Subordinate.weaken (GX, I.targetFam V) in let iw = Whnf.invert w in let GX' = Whnf.strengthen (iw, GX) in let X' = I.newEVar (GX', I.EClo (V, iw)) in let _ = Unify.instantiateEVar (r, I.EClo (X', w), []) in let V' = raiseType (GX', I.EClo (V, iw)) in  if isId (I.comp (w, I.comp (ss, s)))(* equalCtx (Gs, I.id, GX', s) *)
 then (* fully applied *)
collectEVarFapStr (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d) else (* not fully applied *)
collectEVarNFapStr (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d) )
and collectEVarFap (Gss, Gl, (X, s), K, DupVars, flag, d)  = match (member (eqEVar X) K) with Some (label) -> (* we have seen X before *)
(if flag then collectSub (Gss, Gl, s, K, I.Decl (DupVars, AV (X, d)), flag, d)(*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *)
(* since X has occurred before, we do not traverse its type V' *)
 else collectSub (Gss, Gl, s, K, DupVars, flag, d)) | None -> ( (* val _ = checkEmpty !cnstrs *)
(* inefficient! *)
let label = if flag then Body else TypeLabel in let V' = raiseType (GX, V) in let (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d) in  collectSub (Gss, Gl, s, I.Decl (K', (label, EV (X))), DupVars', flag, d) )
and collectEVarNFap (Gss, Gl, (X, s), K, DupVars, flag, d)  = match member' (eqEVar X) K with Some (label) -> (if flag then collectSub (Gss, Gl, s, K, I.Decl (DupVars, AV (X, d)), flag, d)(* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *)
 else collectSub (Gss, Gl, s, K, DupVars, flag, d)) | None -> ( (* inefficient! *)
let label = if flag then Body else TypeLabel in let V' = raiseType (GX, V) in let (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d) in  if flag then collectSub (Gss, Gl, s, I.Decl (K', (label, EV (X))), I.Decl (DupVars, AV (X, d)), flag, d) else collectSub (Gss, Gl, s, I.Decl (K', (label, EV (X))), DupVars, flag, d) )
and collectEVar (Gss, Gl, (X, s), K, DupVars, flag, d)  = if (! TableParam.strengthen) then collectEVarStr (Gss, Gl, (X, s), K, DupVars, flag, d) else if isId (s)(* equalCtx (compose'(Gl, G), s, GX, s)  *)
 then (* X is fully applied *)
collectEVarFap (Gss, Gl, (X, s), K, DupVars, flag, d) else (* X is not fully applied *)
collectEVarNFap (Gss, Gl, (X, s), K, DupVars, flag, d)
and collectDec (Gss, (I.Dec (_, V), s), (K, DupVars), d, flag)  = ( (*      val (K',DupVars') =  collectExp (Gss, I.Null, (V, s), K, I.Null, false, d)*)
let (K', DupVars') = collectExp (Gss, I.Null, (V, s), K, DupVars, flag, d) in  (K', DupVars') )
and collectSub = function (Gss, Gl, I.Shift _, K, DupVars, flag, d) -> (K, DupVars) | (Gss, Gl, I.Dot (I.Idx _, s), K, DupVars, flag, d) -> collectSub (Gss, Gl, s, K, DupVars, flag, d) | (Gss, Gl, I.Dot (I.Exp (X), s), K, DupVars, flag, d) -> ( (* inefficient? *)
let U' = Whnf.normalize (U, I.id) in let (K', DupVars') = collectExp (Gss, Gl, (U', I.id), K, DupVars, flag, d) in  collectSub (Gss, Gl, s, K', DupVars', flag, d) ) | (Gss, Gl, I.Dot (I.Exp (U), s), K, DupVars, flag, d) -> ( let (K', DupVars') = collectExp (Gss, Gl, (U', I.id), K, DupVars, flag, d) in  collectSub (Gss, Gl, s, K', DupVars', flag, d) ) | (Gss, Gl, I.Dot (I.Exp (I.EClo (U', s')), s), K, DupVars, flag, d) -> ( (* inefficient? *)
let U = Whnf.normalize (U', s') in let (K', DupVars') = collectExp (Gss, Gl, (U, I.id), K, DupVars, flag, d) in  collectSub (Gss, Gl, s, K', DupVars', flag, d) ) | (Gss, Gl, I.Dot (I.Exp (U), s), K, DupVars, flag, d) -> ( let (K', DupVars') = collectExp (Gss, Gl, (U, I.id), K, DupVars, flag, d) in  collectSub (Gss, Gl, s, K', DupVars', flag, d) ) | (Gss, Gl, I.Dot (I.Undef, s), K, DupVars, flag, d) -> collectSub (Gss, Gl, s, K, DupVars, flag, d)
(* collectCtx (Gss, G0, G, K) = (K', DupVars)
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars in G
    *)

let rec collectCtx = function (Gss, C.DProg (I.Null, I.Null), (K, DupVars), d) -> (K, DupVars) | (Gss, C.DProg (I.Decl (G, D), I.Decl (dPool, C.Parameter)), (K, DupVars), d) -> ( let (K', DupVars') = collectCtx (Gss, C.DProg (G, dPool), (K, DupVars), d - 1) in  collectDec (Gss, (D, I.id), (K', DupVars'), d - 1, false) ) | (Gss, C.DProg (I.Decl (G, D), I.Decl (dPool, C.Dec (r, s, Ha))), (K, DupVars), d) -> ( let (K', DupVars') = collectCtx (Gss, C.DProg (G, dPool), (K, DupVars), d - 1) in  collectDec (Gss, (D, I.id), (K', DupVars'), d - 1, false) )
(* abstractExpW (epos, apos, Vars, Gl, total, depth, (U, s), eqn) = (epos', apos', Vars', U', eqn')
      (abstraction and linearization of existential variables in (U,s))

       U' = {{U[s]}}_(K, Dup)

       Invariant:
       If     G, Gl |- U[s] : V and  U[s] is in whnf
       and   |Gl| = depth
             |Dup, K| = total

       and epos = (total(K) + l) - #replaced expressions in U    (generate no additional constraints)
       and apos = (total(Dup) + + total(K) + l) - #replaced expressions in U
                  (generate additional constraints (avars))

       and Vars'  = Vars, Vars''
           where Vars contains pairs ((label, i), EV X) of all EVars (EV X),
           where label refers to where we have seen the existential variable (typeLabel or body) and
           i corresponds to the bvar-index assigned to X in U[s]

       and   K ~ Vars (we can obtain K from Vars by dropping the first component of
             each pair (_, EV X) in Vars' )

       then   {{Dup}}, {{K}}  ||- U
       and {{Dup}} {{K}} , G, Gl |-  U' : V'
       and eqn' = eqn, eqn'' where eqn'' are residual equations relating between elements
           in {{K}} and {{Dup}}

       and . ||- Pi G. U'  and   U' is in nf

       if flag then linearize U else allow duplicates.

    *)

let rec abstractExpW = function (flag, Gs, posEA, Vars, Gl, total, depth, (U, s), eqn) -> (posEA, Vars, U, eqn) | (flag, Gs, posEA, Vars, Gl, total, depth, (I.Pi ((D, P), V), s), eqn) -> ( let (posEA', Vars', D, _) = abstractDec (Gs, posEA, Vars, Gl, total, depth, (D, s), None) in let (posEA'', Vars'', V', eqn2) = abstractExp (flag, Gs, posEA', Vars', Gl, total, depth + 1, (V, I.dot1 s), eqn) in  (posEA'', Vars'', piDepend ((D, P), V'), eqn2) ) | (flag, Gs, posEA, Vars, Gl, total, depth, (I.Root (H, S), s), eqn) -> ( let (posEA', Vars', S, eqn') = abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) in  (posEA', Vars', I.Root (H, S), eqn') ) | (flag, Gs, posEA, Vars, Gl, total, depth, (I.Lam (D, U), s), eqn) -> ( let (posEA', Vars', D', _) = abstractDec (Gs, posEA, Vars, Gl, total, depth, (D, s), None) in let (posEA'', Vars'', U', eqn2) = abstractExp (flag, Gs, posEA', Vars', I.Decl (Gl, D'), total, depth + 1, (U, I.dot1 s), eqn) in  (posEA'', Vars'', I.Lam (D', U'), eqn2) ) | (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn) -> if isId (I.comp (ss, s)) then (* X is fully applied *)
abstractEVarFap (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn) else (* s =/= id, i.e. X is not fully applied *)
abstractEVarNFap (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn)
and abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, Us, eqn)  = abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, Whnf.whnf Us, eqn)
and abstractEVarFap (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn)  = match (member (eqEVar X) Vars) with Some (label, i) -> (* we have seen X before *)
if flag then (* enforce linearization *)
match label with Body -> ( let BV = I.BVar (apos + depth) in let BV' = I.BVar (i + depth) in let BV1 = I.BVar (apos + depth) in let (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn) in  (posEA', Vars', I.Root (BV, I.Nil), TableParam.Unify (Gl, I.Root (BV', S), I.Root (BV1, I.Nil), eqn1)) ) | TypeLabel -> ( let Vars' = update (eqEVar X) Vars in let (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn) in  (posEA', Vars'', I.Root (I.BVar (i + depth), S), eqn1) ) else (* do not enforce linearization -- used for_sml type labels *)
( let (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil, eqn) in  (posEA', Vars', I.Root (I.BVar (i + depth), S), eqn1) ) | None -> (* we see X for_sml the first time *)
( let label = if flag then Body else TypeLabel in let BV = I.BVar (epos + depth) in let pos = (epos - 1, apos) in let (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, pos, I.Decl (Vars, ((label, epos), EV X)), Gl, total, depth, s, I.Nil, eqn) in  (posEA', Vars', I.Root (BV, S), eqn1) )
and abstractEVarNFap (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn)  = match (member (eqEVar X) Vars) with Some (label, i) -> (* we have seen X before *)
if flag then (* enforce linearization *)
( let BV = I.BVar (apos + depth) in let BV' = I.BVar (i + depth) in let BV1 = I.BVar (apos + depth) in let (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn) in  (posEA', Vars', I.Root (BV, I.Nil), TableParam.Unify (Gl, I.Root (BV', S), I.Root (BV1, I.Nil), eqn1)) )(* (case label of
               Body =>
                 let
                  val _ = print "abstractEVarNFap -- flag true; we have seen X before\n"
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar X) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *)
 else (* do not enforce linearization -- used for_sml type labels *)
( let (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil, eqn) in  (posEA', Vars', I.Root (I.BVar (i + depth), S), eqn1) ) | None -> (* we have not seen X before *)
if flag then (* enforce linearization since X is not fully applied *)
( let label = if flag then Body else TypeLabel in let BV = I.BVar (apos + depth) in let BV' = I.BVar (epos + depth) in let BV1 = I.BVar (apos + depth) in let (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos - 1, apos - 1), I.Decl (Vars, ((label, epos), EV X)), Gl, total, depth, s, I.Nil, eqn) in  (posEA', Vars', I.Root (BV, I.Nil), TableParam.Unify (Gl, I.Root (BV', S), I.Root (BV1, I.Nil), eqn1)) ) else (* do not enforce linearization -- used for_sml type labels *)
( let (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos - 1, apos), I.Decl (Vars, ((TypeLabel, epos), EV X)), Gl, total, depth, s, I.Nil, eqn) in  (posEA', Vars', I.Root (I.BVar (epos + depth), S), eqn1) )
and abstractSub = function (flag, Gs, posEA, Vars, Gl, total, depth, I.Shift (k), S, eqn) -> if k < depth then abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), S, eqn) else (* k = depth *)
(posEA, Vars, S, eqn) | (flag, Gs, posEA, Vars, Gl, total, depth, I.Dot (I.Idx (k), s), S, eqn) -> abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, I.App (I.Root (I.BVar (k), I.Nil), S), eqn) | (flag, Gs, posEA, Vars, Gl, total, depth, I.Dot (I.Exp (U), s), S, eqn) -> ( let (posEA', Vars', U', eqn') = abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, (U, I.id), eqn) in  abstractSub (flag, Gs, posEA', Vars', Gl, total, depth, s, I.App (U', S), eqn') )
and abstractSpine = function (flag, Gs, posEA, Vars, Gl, total, depth, (I.Nil, _), eqn) -> (posEA, Vars, I.Nil, eqn) | (flag, Gs, posEA, Vars, Gl, total, depth, (I.SClo (S, s'), s), eqn) -> abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, I.comp (s', s)), eqn) | (flag, Gs, posEA, Vars, Gl, total, depth, (I.App (U, S), s), eqn) -> ( let (posEA', Vars', U', eqn') = abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, (U, s), eqn) in let (posEA'', Vars'', S', eqn'') = abstractSpine (flag, Gs, posEA', Vars', Gl, total, depth, (S, s), eqn') in  (posEA'', Vars'', I.App (U', S'), eqn'') )
and abstractSub' = function (flag, Gs, epos, Vars, total, I.Shift (k)) -> if k < 0 then raise (Error ("Substitution out of range\n")) else (epos, Vars, I.Shift (k + total)) | (flag, Gs, epos, Vars, total, I.Dot (I.Idx (k), s)) -> ( let (epos', Vars', s') = abstractSub' (flag, Gs, epos, Vars, total, s) in  (epos', Vars', I.Dot (I.Idx (k), s')) ) | (flag, Gs, epos, Vars, total, I.Dot (I.Exp (U), s)) -> ( let ((ep, _), Vars', U', _) = abstractExp (false, Gs, (epos, 0), Vars, I.Null, total, 0, (U, I.id), TableParam.Trivial) in let (epos'', Vars'', s') = abstractSub' (flag, Gs, ep, Vars', total, s) in  (epos'', Vars'', I.Dot (I.Exp (U'), s')) )
and abstractDec = function (Gs, posEA, Vars, Gl, total, depth, (I.Dec (x, V), s), None) -> ( (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
let (posEA', Vars', V', eqn) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial) in  (posEA', Vars', I.Dec (x, V'), eqn) ) | (Gs, posEA, Vars, Gl, total, depth, (I.Dec (x, V), s), Some (eqn)) -> ( (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
let (posEA', Vars', V', eqn') = abstractExp (true, Gs, posEA, Vars, Gl, total, depth, (V, s), eqn) in  (posEA', Vars', I.Dec (x, V'), eqn') )
(* abstractCtx (Gs, epos, K, total, depth, C.DProg(G,dPool)) = (epos', K', G')
       where G' = {{G}}_K

       Invariants:
       If K ||- G
       and |G| = depth
       then {{K}} |- G' ctx
       and . ||- G'
       and epos = current epos

       note: we will linearize all dynamic assumptions in G.
    *)

let rec abstractCtx' = function (Gs, epos, Vars, total, depth, C.DProg (I.Null, I.Null), G', eqn) -> (epos, Vars, G', eqn) | (Gs, epos, Vars, total, depth, C.DProg (I.Decl (G, D), I.Decl (dPool, C.Parameter)), G', eqn) -> ( let d = IntSyn.ctxLength (G) in let ((epos', _), Vars', D', _) = abstractDec (Gs, (epos, total), Vars, I.Null, total, depth - 1, (D, I.id), None) in  abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg (G, dPool), I.Decl (G', D'), eqn) ) | (Gs, epos, Vars, total, depth, C.DProg (I.Decl (G, D), I.Decl (dPool, _)), G', eqn) -> ( let d = IntSyn.ctxLength (G) in let ((epos', _), Vars', D', _) = abstractDec (Gs, (epos, total), Vars, I.Null, total, depth - 1, (D, I.id), None) in  abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg (G, dPool), I.Decl (G', D'), eqn) )
(*        let
          val d = IntSyn.ctxLength (G)
          val ((epos', _), Vars', D', eqn') = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), SOME(eqn))
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn')
        end
*)

let rec abstractCtx (Gs, epos, Vars, total, depth, dProg)  = abstractCtx' (Gs, epos, Vars, total, depth, dProg, I.Null, TableParam.Trivial)
(* makeEVarCtx (Gs, Kall, D, K, eqn) = G'  *)

let rec makeEVarCtx = function (Gs, Vars, DEVars, I.Null, total) -> DEVars | (Gs, Vars, DEVars, I.Decl (K', (_, EV (E))), total) -> ( let V' = raiseType (GX, VX) in let (_, Vars', V'', _) = abstractExp (false, Gs, (0, 0), Vars, I.Null, 0, (total - 1), (V', I.id), TableParam.Trivial) in let DEVars' = makeEVarCtx (Gs, Vars', DEVars, K', total - 1) in let DEVars'' = I.Decl (DEVars', I.Dec (None, V'')) in  DEVars'' )
let rec makeAVarCtx (Vars, DupVars)  = ( let rec avarCtx = function (Vars, I.Null, k) -> I.Null | (Vars, I.Decl (K', AV (E, d)), k) -> I.Decl (avarCtx (Vars, K', k + 1), I.ADec (Some ("AVar " ^ Int.toString k ^ "--" ^ Int.toString d), d)) | (Vars, I.Decl (K', AV (E, d)), k) -> I.Decl (avarCtx (Vars, K', k + 1), I.ADec (Some ("AVar " ^ Int.toString k ^ "--" ^ Int.toString d), d)) in  avarCtx (Vars, DupVars, 0) )
(* add case for_sml foreign expressions ? *)

(* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)

let rec lowerEVar' = function (X, G, (I.Pi ((D', _), V'), s')) -> ( let D'' = I.decSub (D', s') in let (X', U) = lowerEVar' (X, I.Decl (G, D''), Whnf.whnf (V', I.dot1 s')) in  (X', I.Lam (D'', U)) ) | (X, G, Vs') -> ( let X' = X in  (X', X') )
and lowerEVar1 = function (X, I.EVar (r, G, _, _), (V, s)) -> ( let (X', U) = lowerEVar' (X, G, (V, s)) in  I.EVar (ref (Some (U)), I.Null, V, ref []) ) | (_, X, _) -> X
and lowerEVar = function (E, X) -> lowerEVar1 (E, X, Whnf.whnf (V, I.id)) | (E, I.EVar _) -> raise (Error "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified")
(* evarsToSub (K, s') = s
      Invariant:
      if K = EV Xn ... EV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)

let rec evarsToSub = function (I.Null, s) -> s | (I.Decl (K', (_, EV (E))), s) -> ( (* redundant ? *)
let V' = raiseType (GX, VX) in let X = lowerEVar1 (E, I.EVar (I, I.Null, V', cnstr), Whnf.whnf (V', I.id)) in let s' = evarsToSub (K', s) in  I.Dot (I.Exp (X), s') )
(* evarsToSub (K, s') = s
      Invariant:
      if K = AV Xn ... AV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)

let rec avarsToSub = function (I.Null, s) -> s | (I.Decl (Vars', (AV (E, d))), s) -> ( let s' = avarsToSub (Vars', s) in let X' = I.newAVar () in  I.Dot (I.Exp (I.EClo (X', I.Shift (~ d))), s') )
(* abstractEVarCtx (G, p, s) = (G', D', U', s')

     if G |- p[s] and s contains free variables X_n .... X_1
     then
       D' |- Pi  G' . U'
       where D' is the abstraction over the free vars X_n .... X_1

       and s' is a substitution the free variables
            X_n .... X_1, s.t.

       . |- s' : D'

       . |- (Pi G' .U' )[s']  is equivalent to . |- Pi G . p[s]

       Note: G' and U' are possibly strengthened
   *)

let rec abstractEVarCtx (dp, p, s)  = ( (* K ||- G i.e. K contains all EVars in G *)
(* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and G and
                                         DupVars' contains all duplicate EVars p[s] *)
(* {{G}}_Vars' , i.e. abstract over the existential variables in G*)
(* abstract over existential variables in p[s] and linearize the expression *)
(* note: depth will become negative during makeEVarCtx *)
let (Gs, ss, d) = (if (! TableParam.strengthen) then ( let w' = Subordinate.weaken (G, I.targetFam p) in let iw = Whnf.invert w' in let G' = Whnf.strengthen (iw, G) in let d' = I.ctxLength (G') in  (G', iw, d') ) else (G, I.id, I.ctxLength (G))) in let (K, DupVars) = collectCtx ((Gs, ss), dp, (I.Null, I.Null), d) in let (K', DupVars') = collectExp ((Gs, ss), I.Null, (p, s), K, DupVars, true, d) in let epos = I.ctxLength (K') in let apos = I.ctxLength (DupVars') in let total = epos + apos in let (epos', Vars', G', eqn) = abstractCtx ((Gs, ss), epos, I.Null, total, d, dp) in let (posEA''(* = 0 *)
, Vars'', U', eqn') = abstractExp (true, (Gs, ss), (epos', total), Vars', I.Null, total, d, (p, s), eqn) in let DAVars = makeAVarCtx (Vars'', DupVars') in let DEVars = makeEVarCtx ((Gs, ss), Vars'', I.Null, Vars'', 0(* depth *)
) in let s' = avarsToSub (DupVars', I.id) in let s'' = evarsToSub (Vars'', s') in let G'' = reverseCtx (G', I.Null) in  if (! TableParam.strengthen) then ( let w' = Subordinate.weaken (G'', I.targetFam U') in let iw = Whnf.invert w' in let Gs' = Whnf.strengthen (iw, G'') in  (Gs', DAVars, DEVars, U', eqn', s'') ) else (G'', DAVars, DEVars, U', eqn', s'') )
let abstractEVarCtx = abstractEVarCtx
(* abstractAnswSub s = (D', s')

   if  |- s : Delta' and s may contain free variables and
     D |- Pi G. U  and  |- s : D and  |- (Pi G . U)[s]
    then

    D' |- s' : D   where D' contains all the
    free variables from s
   *)

let abstractAnswSub = (fun s -> ( (* no linearization for_sml answer substitution *)
let (K, _) = collectSub ((I.Null, I.id), I.Null, s, I.Null, I.Null, false, 0) in let epos = I.ctxLength K in let (_(*0 *)
, Vars, s') = abstractSub' (false, (I.Null, I.id), epos, I.Null, epos(* total *)
, s) in let DEVars = makeEVarCtx ((I.Null, I.id), Vars, I.Null, Vars, 0) in let s1' = ctxToEVarSub (DEVars, I.id) in  (DEVars, s') ))
let raiseType = (fun (G, U) -> raiseType (G, U))
 end


(* functor AbstractTabled *)

