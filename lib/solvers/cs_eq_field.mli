(* Gaussian-Elimination Equation Solver *)

(* Author: Roberto Virga *)

module type CS_EQ_FIELD = sig
  include CS
  module Field : FIELD

  (*! structure IntSyn : INTSYN !*)
  (* Foreign expressions *)
  type 'a mset = 'a list

  (* MultiSet                   *)
  type sum = Sum of Field.number * mon mset
  and mon = Mon of Field.number * IntSyn.exp * IntSyn.sub mset

  (* Mon ::= n * U1[s1] * ...   *)
  val fromExp : IntSyn.eclo -> sum
  val toExp : sum -> IntSyn.exp
  val normalize : sum -> sum
  val compatibleMon : mon * mon -> bool

  (* Internal expressions constructors *)
  val number : unit -> IntSyn.exp
  val unaryMinus : IntSyn.exp -> IntSyn.exp
  val plus : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val minus : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val times : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val constant : Field.number -> IntSyn.exp
end

(* signature CS_EQ_FIELD *)
