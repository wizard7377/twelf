(* Abstraction *)
(* Author: Brigitte Pientka *)

module type ABSTRACTTABLED =
sig

  (*! module IntSyn : INTSYN !*)

  (*! module TableParam : TABLEPARAM !*)
    
  exception Error of string


  val abstractEVarCtx : (CompSyn.DProg * IntSyn.exp * IntSyn.Sub) ->  
                        (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.exp * TableParam.ResEqn * IntSyn.Sub)

  val abstractAnswSub :  IntSyn.Sub -> IntSyn.dctx * IntSyn.Sub  

  val raiseType : IntSyn.dctx * IntSyn.exp -> IntSyn.exp   

end;; (* module type ABSTRACTTABLED *)
