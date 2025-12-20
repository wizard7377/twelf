(* State for_sml Proof Search *)


(* Author: Carsten Schuermann *)


module StateSyn (Whnf : WHNF) (Conv : CONV) : STATESYN = struct (*! structure IntSyn = IntSyn' !*)

(*! structure FunSyn = FunSyn' !*)

type order = Arg of (IntSyn.exp * IntSyn.sub) * (IntSyn.exp * IntSyn.sub) | Lex of order list | Simul of order list | All of IntSyn.dec * order | And of order * order
(*     | O1 ^ O2              *)

type info = Splits of int | RL | RLdone
type tag = Parameter of FunSyn.label option | Lemma of info | None
type state = State of int(* Part of theorem                   *)
 * (IntSyn.dctx(* Context of Hypothesis in general not named *)
 * tag IntSyn.ctx)(* Status information *)
 * (FunSyn.for_sml * order)(* Induction hypothesis, order       *)
 * int(* length of meta context            *)
 * order(* Current Order *)
 * int * FunSyn.for_sml list(* History of residual lemmas *)
 * FunSyn.for_sml
(* Formula *)

module F = FunSyn
module I = IntSyn
(* orderSub (O, s) = O'

       Invariant:
       If   G' |- O order    and    G |- s : G'
       then G |- O' order
       and  G |- O' == O[s] order
    *)

let rec orderSub = function (Arg ((U, s1), (V, s2)), s) -> Arg ((U, I.comp (s1, s)), (V, I.comp (s2, s))) | (Lex Os, s) -> Lex (map (fun O -> orderSub (O, s)) Os) | (Simul Os, s) -> Simul (map (fun O -> orderSub (O, s)) Os)
(* by invariant: no case for_sml All and And *)

(* normalizeOrder (O) = O'

       Invariant:
       If   G |- O order
       then G |- O' order
       and  G |- O = O' order
       and  each sub term of O' is in normal form.
    *)

let rec normalizeOrder = function (Arg (Us, Vs)) -> Arg ((Whnf.normalize Us, I.id), (Whnf.normalize Vs, I.id)) | (Lex Os) -> Lex (map normalizeOrder Os) | (Simul Os) -> Simul (map normalizeOrder Os)
(* by invariant: no case for_sml All and And *)

(* convOrder (O1, O2) = B'

       Invariant:
       If   G |- O1 order
       and  G |- O2 order
       then B' holds iff G |- O1 == O2 order
    *)

let rec convOrder = function (Arg (Us1, _), Arg (Us2, _)) -> Conv.conv (Us1, Us2) | (Lex Os1, Lex Os2) -> convOrders (Os1, Os2) | (Simul Os1, Simul Os2) -> convOrders (Os1, Os2)
and convOrders = function ([], []) -> true | (O1 :: L1, O2 :: L2) -> convOrder (O1, O2) && convOrders (L1, L2)
(* by invariant: no case for_sml All and And *)

(* decrease T = T'

       Invariant:
       T is either an Assumption or Induction tag
       T' = T - 1
    *)

let rec decreaseInfo = function (Splits k) -> Splits (k - 1) | RL -> RL | RLdone -> RLdone
let rec decrease = function (Lemma (Sp)) -> Lemma (decreaseInfo Sp) | None -> None
let rec splitDepth (Splits k)  = k
(* normalizeTag (T, s) = T'

       Invariant:
       If   G |- T : tag
            G' |- s : G
       then G' |- T' = T[s] tag
    *)

let rec normalizeTag = function (T, _) -> T | (Lemma (K), s) -> Lemma (K)
let orderSub = orderSub
let decrease = decrease
let splitDepth = splitDepth
let normalizeOrder = normalizeOrder
let convOrder = convOrder
let normalizeTag = normalizeTag
(* local *)

 end


(* signature STATESYN *)

