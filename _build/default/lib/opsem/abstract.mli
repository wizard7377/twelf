(* Abstraction *)
(* Author: Brigitte Pientka *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature ABSTRACTTABLED =
sig

  (*! structure IntSyn : INTSYN !*)

  (*! structure TableParam : TABLEPARAM !*)
    
  exception Error of string


  val abstractEVarCtx : (CompSyn.d_prog * IntSyn.exp * IntSyn.sub) ->  
                        (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.exp * TableParam.res_eqn * IntSyn.sub)

  val abstractAnswSub :  IntSyn.sub -> IntSyn.dctx * IntSyn.sub  

  val raiseType : IntSyn.dctx * IntSyn.exp -> IntSyn.exp   

end (* GEN END SIGNATURE DECLARATION *);  (* signature ABSTRACTTABLED *)
