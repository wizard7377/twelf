StateSyn  Whnf WHNF    Conv CONV     STATESYN  struct (*! structure IntSyn = IntSyn' !*)
(*! structure FunSyn = FunSyn' !*)
type Order(*     | O1 ^ O2              *)
type Infotype Tagtype State(* Formula *)
module module (* orderSub (O, s) = O'

       Invariant:
       If   G' |- O order    and    G |- s : G'
       then G |- O' order
       and  G |- O' == O[s] order
    *)
let rec orderSub(arg ((u,  , s1),  , (v,  , s2)),  , s) arg ((u,  , comp (s1,  , s)),  , (v,  , comp (s2,  , s))) orderSub(lex os,  , s) lex (map (fun o -> orderSub (o,  , s)) os) orderSub(simul os,  , s) simul (map (fun o -> orderSub (o,  , s)) os)(* by invariant: no case for All and And *)
(* normalizeOrder (O) = O'

       Invariant:
       If   G |- O order
       then G |- O' order
       and  G |- O = O' order
       and  each sub term of O' is in normal form.
    *)
let rec normalizeOrder(arg (us,  , vs)) arg ((normalize us,  , id),  , (normalize vs,  , id)) normalizeOrder(lex os) lex (map normalizeOrder os) normalizeOrder(simul os) simul (map normalizeOrder os)(* by invariant: no case for All and And *)
(* convOrder (O1, O2) = B'

       Invariant:
       If   G |- O1 order
       and  G |- O2 order
       then B' holds iff G |- O1 == O2 order
    *)
let rec convOrder(arg (us1,  , _),  , arg (us2,  , _)) conv (us1,  , us2) convOrder(lex os1,  , lex os2) convOrders (os1,  , os2) convOrder(simul os1,  , simul os2) convOrders (os1,  , os2) convOrders(nil,  , nil) true convOrders(o1 :: l1,  , o2 :: l2) convOrder (o1,  , o2) && convOrders (l1,  , l2)(* by invariant: no case for All and And *)
(* decrease T = T'

       Invariant:
       T is either an Assumption or Induction tag
       T' = T - 1
    *)
let rec decreaseInfo(splits k) splits (k - 1) decreaseInforL rL decreaseInforLdone rLdonelet rec (* decrease (Assumption k) = Assumption (k-1)
      | *)
decrease(lemma (sp)) lemma (decreaseInfo sp) decreasenone nonelet rec splitDepth(splits k) k(* normalizeTag (T, s) = T'

       Invariant:
       If   G |- T : tag
            G' |- s : G
       then G' |- T' = T[s] tag
    *)
let rec normalizeTag(t as parameter _,  , _) t normalizeTag(lemma (k),  , s) lemma (k)let  inlet  inlet  inlet  inlet  inlet  in(* local *)
end