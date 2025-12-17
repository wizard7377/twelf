STATESYN   Order arg (Exp * Sub) * (Exp * Sub)  lex Order List  simul Order List  all Dec * Order  and Order * Order    Info splits Int  rL  rLdone    Tag parameter Label Option  lemma Info  none    State state Int(* Part of theorem                   *)
 * (Dctx(* Context of Hypothesis, in general not named *)
 * Tag Ctx)(* Status information *)
 * (For * Order)(* Induction hypothesis, order       *)
 * Int(* length of meta context            *)
 * Order(* Current order *)
 *  Int * For  List(* History of residual lemmas *)
 * For    orderSub Order * Sub -> Order   decrease Tag -> Tag   splitDepth Info -> Int   normalizeOrder Order -> Order   convOrder Order * Order -> Bool   normalizeTag Tag * Sub -> Tag