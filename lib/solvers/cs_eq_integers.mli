(* Gaussian-Elimination Equation Solver *)
(* Author: Roberto Virga *)

module type CS_EQ_INTEGERS =
sig
  include CS

  module Integers : INTEGERS
  (*! module IntSyn : INTSYN !*)

  (* Foreign expressions *)

  type 'a mset = 'a list                 (* MultiSet                   *)

  type sum =                         (* sum :                      *)
    sum of Integers.int * Mon mset       (* sum ::= m + M1 + ...       *)

  and Mon =                              (* Monomials:                 *)
    Mon of Integers.int * (IntSyn.exp * IntSyn.Sub) mset
                                         (* Mon ::= n * U1[s1] * ...   *)

  val fromExp   : IntSyn.eclo -> sum
  val toExp     : sum -> IntSyn.exp
  val normalize : sum -> sum

  val compatibleMon : Mon * Mon -> bool

  (* Internal expressions constructors *)

  val number     : unit -> IntSyn.exp

  val unaryMinus : IntSyn.exp -> IntSyn.exp
  val plus       : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val minus      : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val times      : IntSyn.exp * IntSyn.exp -> IntSyn.exp

  val constant   : Integers.int -> IntSyn.exp
end  (* module type CS_EQ_FIELD *)
