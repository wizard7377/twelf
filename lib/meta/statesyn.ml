(* State for Proof Search *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) StateSyn ((*! structure IntSyn' : INTSYN !*)
                  (*! structure FunSyn' : FUNSYN !*)
                  (*! sharing FunSyn'.IntSyn = IntSyn' !*)
                  structure Whnf : WHNF
                  (*! sharing Whnf.IntSyn = IntSyn' !*)
                  structure Conv : CONV
                  (*! sharing Conv.IntSyn = IntSyn' !*)
                    )
  : STATESYN =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure FunSyn = FunSyn' !*)

  datatype order =                      (* Orders                     *)
    Arg of (IntSyn.exp * IntSyn.sub) *
           (IntSyn.exp * IntSyn.sub)    (* O ::= U[s] : V[s]          *)
  | Lex of order list                   (*     | (O1 .. On)           *)
  | Simul of order list                 (*     | {O1 .. On}           *)
  | All of IntSyn.dec * order           (*     | {{D}} O              *)
  | And of order * order                (*     | O1 ^ O2              *)


  datatype info =
    Splits of int
  | RL
  | RLdone

  datatype tag =
    Parameter of FunSyn.label option
  | Lemma of info
  | None

  datatype state =                      (* S = <n, (G, B), (IH, OH), d, O, H, F> *)
    State of int                        (* Part of theorem                   *)
           * (IntSyn.dctx       (* Context of Hypothesis in general not named *)
           * tag IntSyn.ctx) (* Status information *)
           * (FunSyn.for * order)       (* Induction hypothesis, order       *)
           * int                        (* length of meta context            *)
           * order                      (* Current Order *)
           * (int * FunSyn.for) list    (* History of residual lemmas *)
           * FunSyn.for                 (* Formula *)

  local
    structure F = FunSyn
    structure I = IntSyn

    (* orderSub (O, s) = O'

       Invariant:
       If   G' |- O order    and    G |- s : G'
       then G |- O' order
       and  G |- O' == O[s] order
    *)
    fun (* GEN BEGIN FUN FIRST *) orderSub (Arg ((U, s1), (V, s2)), s) =
          Arg ((U,  I.comp (s1, s)), (V, I.comp (s2, s))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) orderSub (Lex Os, s) = Lex (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => orderSub (O, s) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) orderSub (Simul Os, s) = Simul (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => orderSub (O, s) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)
      (* by invariant: no case for All and And *)


    (* normalizeOrder (O) = O'

       Invariant:
       If   G |- O order
       then G |- O' order
       and  G |- O = O' order
       and  each sub term of O' is in normal form.
    *)
    fun (* GEN BEGIN FUN FIRST *) normalizeOrder (Arg (Us, Vs)) =
          Arg ((Whnf.normalize Us, I.id), (Whnf.normalize Vs, I.id)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) normalizeOrder (Lex Os) = Lex (map normalizeOrder Os) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizeOrder (Simul Os) = Simul (map normalizeOrder Os) (* GEN END FUN BRANCH *)
      (* by invariant: no case for All and And *)


    (* convOrder (O1, O2) = B'

       Invariant:
       If   G |- O1 order
       and  G |- O2 order
       then B' holds iff G |- O1 == O2 order
    *)
    fun (* GEN BEGIN FUN FIRST *) convOrder (Arg (Us1, _), Arg (Us2, _ )) = Conv.conv (Us1, Us2) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) convOrder (Lex Os1, Lex Os2) = convOrders (Os1, Os2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convOrder (Simul Os1, Simul Os2) = convOrders (Os1, Os2) (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) convOrders (nil, nil) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) convOrders (O1 :: L1, O2 :: L2) =
          convOrder (O1, O2) andalso convOrders (L1, L2) (* GEN END FUN BRANCH *)
      (* by invariant: no case for All and And *)

    (* decrease T = T'

       Invariant:
       T is either an Assumption or Induction tag
       T' = T - 1
    *)
    fun (* GEN BEGIN FUN FIRST *) decreaseInfo (Splits k) = Splits (k-1) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decreaseInfo RL = RL (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) decreaseInfo RLdone = RLdone (* GEN END FUN BRANCH *)

    fun (* decrease (Assumption k) = Assumption (k-1)
      | *) (* GEN BEGIN FUN FIRST *) decrease (Lemma (Sp)) = Lemma (decreaseInfo Sp) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decrease None = None (* GEN END FUN BRANCH *)


    fun splitDepth (Splits k) = k

    (* normalizeTag (T, s) = T'

       Invariant:
       If   G |- T : tag
            G' |- s : G
       then G' |- T' = T[s] tag
    *)

    fun (* GEN BEGIN FUN FIRST *) normalizeTag (T as Parameter _, _) = T (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) normalizeTag (Lemma (K), s) = Lemma (K) (* GEN END FUN BRANCH *)

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val orderSub = orderSub (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val decrease = decrease (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val splitDepth = splitDepth (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val normalizeOrder = normalizeOrder (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val convOrder = convOrder (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val normalizeTag = normalizeTag (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* signature STATESYN *)