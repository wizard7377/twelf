(* Reasoning about orders *)
(* Author: Brigitte Pientka *)

module type CHECKING =
sig
  (*! module IntSyn : INTSYN !*)
  module Order : ORDER
  (*! module Paths : PATHS !*)
    
  (* If Q marks all parameters in a context G we write   G : Q  *)

  type quantifier =        (* Quantifier to mark parameters *)
    All                  (* Q ::= All                     *)
  | Exist                (*     | Exist                     *)
  | And of Paths.occ     (*     | And                     *)


  type 'a Predicate = 
    Less of 'a * 'a
  | Leq of 'a * 'a 
  | Eq of 'a * 'a 
  | Pi of IntSyn.Dec * 'a Predicate        
    

  type order = (IntSyn.eclo * IntSyn.eclo) Order.Order 

  (* reduction predicate context (unordered) *)
  type rctx = order Predicate list


  (* mixed-prefix context *)
  type qctx = Quantifier IntSyn.ctx

  val shiftRCtx : rctx -> (IntSyn.Sub -> IntSyn.Sub) -> rctx

  val shiftPred : order Predicate ->  (IntSyn.Sub -> IntSyn.Sub) 
                  -> order Predicate
   
  val deduce : IntSyn.dctx * qctx * rctx * order Predicate -> bool
 
end;; (* module type CHECKING *)
