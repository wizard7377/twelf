(* State for Proof Search *)
(* Author: Carsten Schuermann *)

module StateSyn ((*! module IntSyn' : INTSYN !*)
                  (*! module FunSyn' : FUNSYN !*)
                  (*! sharing FunSyn'.IntSyn = IntSyn' !*)
                  module Whnf : WHNF
                  (*! sharing Whnf.IntSyn = IntSyn' !*)
                  module Conv : CONV): STATESYN =
                  (*! sharing Conv.IntSyn = IntSyn' !*)
struct
  (*! module IntSyn = IntSyn' !*)
  (*! module FunSyn = FunSyn' !*)

  type order =                      (* Orders                     *)
    Arg of (IntSyn.Exp * IntSyn.Sub) *
           (IntSyn.Exp * IntSyn.Sub)    (* O ::= U[s] : V[s]          *)
  | Lex of order list                   (*     | (O1 .. On)           *)
  | Simul of order list                 (*     | {O1 .. On}           *)
  | All of IntSyn.Dec * order           (*     | {{D}} O              *)
  | And of order * order                (*     | O1 ^ O2              *)


  type info =
    Splits of int
  | RL
  | RLdone

  type tag =
    Parameter of FunSyn.label option
  | Lemma of Info
  | None

  type state =                      (* S = <n, (G, B), (IH, OH), d, O, H, F> *)
    State of int                        (* Part of theorem                   *)
           * (IntSyn.dctx       (* Context of Hypothesis in general not named *)
           * Tag IntSyn.Ctx) (* Status information *)
           * (FunSyn.For * Order)       (* Induction hypothesis, order       *)
           * int                        (* length of meta context            *)
           * Order                      (* Current Order *)
           * (int * FunSyn.For) list    (* History of residual lemmas *)
           * FunSyn.For                 (* Formula *)

  local
    module F = FunSyn
    module I = IntSyn

    (* orderSub (O, s) = O'

       Invariant:
       If   G' |- O order    and    G |- s : G'
       then G |- O' order
       and  G |- O' == O[s] order
    *)
    fun orderSub (Arg ((U, s1), (V, s2)), s) =
          Arg ((U,  I.comp (s1, s)), (V, I.comp (s2, s)))
      | orderSub (Lex Os, s) = Lex (map (fun O -> orderSub (O, s)) Os)
      | orderSub (Simul Os, s) = Simul (map (fun O -> orderSub (O, s)) Os)
      (* by invariant: no case for All and And *)


    (* normalizeOrder (O) = O'

       Invariant:
       If   G |- O order
       then G |- O' order
       and  G |- O = O' order
       and  each sub term of O' is in normal form.
    *)
    fun normalizeOrder (Arg (Us, Vs)) =
          Arg ((Whnf.normalize Us, I.id), (Whnf.normalize Vs, I.id))
      | normalizeOrder (Lex Os) = Lex (map normalizeOrder Os)
      | normalizeOrder (Simul Os) = Simul (map normalizeOrder Os)
      (* by invariant: no case for All and And *)


    (* convOrder (O1, O2) = B'

       Invariant:
       If   G |- O1 order
       and  G |- O2 order
       then B' holds iff G |- O1 == O2 order
    *)
    fun convOrder (Arg (Us1, _), Arg (Us2, _ )) = Conv.conv (Us1, Us2)
      | convOrder (Lex Os1, Lex Os2) = convOrders (Os1, Os2)
      | convOrder (Simul Os1, Simul Os2) = convOrders (Os1, Os2)
    and convOrders (nil, nil) = true
      | convOrders (O1 :: L1, O2 :: L2) =
          convOrder (O1, O2) andalso convOrders (L1, L2)
      (* by invariant: no case for All and And *)

    (* decrease T = T'

       Invariant:
       T is either an Assumption or Induction tag
       T' = T - 1
    *)
    fun decreaseInfo (Splits k) = Splits (k-1)
      | decreaseInfo RL = RL
      | decreaseInfo RLdone = RLdone

    fun (* decrease (Assumption k) = Assumption (k-1)
      | *) decrease (Lemma (Sp)) = Lemma (decreaseInfo Sp)
      | decrease None = None


    fun splitDepth (Splits k) = k

    (* normalizeTag (T, s) = T'

       Invariant:
       If   G |- T : tag
            G' |- s : G
       then G' |- T' = T[s] tag
    *)

    fun normalizeTag (T as Parameter _, _) = T
      | normalizeTag (Lemma (K), s) = Lemma (K)

  in
    let orderSub = orderSub
    let decrease = decrease
    let splitDepth = splitDepth
    let normalizeOrder = normalizeOrder
    let convOrder = convOrder
    let normalizeTag = normalizeTag
  end (* local *)
end;; (* module type STATESYN *)