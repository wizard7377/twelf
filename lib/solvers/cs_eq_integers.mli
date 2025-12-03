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
    Mon of Integers.int * (IntSyn.Exp * IntSyn.Sub) mset
                                         (* Mon ::= n * U1[s1] * ...   *)

  val fromExp   : IntSyn.eclo -> sum
  val toExp     : sum -> IntSyn.Exp
  val normalize : sum -> sum

  val compatibleMon : Mon * Mon -> bool

  (* Internal expressions constructors *)

  val number     : unit -> IntSyn.Exp

  val unaryMinus : IntSyn.Exp -> IntSyn.Exp
  val plus       : IntSyn.Exp * IntSyn.Exp -> IntSyn.Exp
  val minus      : IntSyn.Exp * IntSyn.Exp -> IntSyn.Exp
  val times      : IntSyn.Exp * IntSyn.Exp -> IntSyn.Exp

  val constant   : Integers.int -> IntSyn.Exp
end  (* module type CS_EQ_FIELD *)
