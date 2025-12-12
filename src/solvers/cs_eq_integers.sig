(* Gaussian-Elimination Equation Solver *)
(* Author: Roberto Virga *)

signature CS_EQ_INTEGERS =
sig
  include CS

  structure Integers : INTEGERS
  (*! structure IntSyn : INTSYN !*)

  (* Foreign expressions *)

  type 'a mset = 'a list                 (* MultiSet                   *)

  datatype sum =                         (* Sum :                      *)
    Sum of Integers.int * mon mset       (* Sum ::= m + M1 + ...       *)

  and mon =                              (* Monomials:                 *)
    Mon of Integers.int * (IntSyn.exp * IntSyn.sub) mset
                                         (* Mon ::= n * U1[s1] * ...   *)

  val fromExp   : IntSyn.eclo -> sum
  val toExp     : sum -> IntSyn.exp
  val normalize : sum -> sum

  val compatibleMon : mon * mon -> bool

  (* Internal expressions constructors *)

  val number     : unit -> IntSyn.exp

  val unaryMinus : IntSyn.exp -> IntSyn.exp
  val plus       : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val minus      : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val times      : IntSyn.exp * IntSyn.exp -> IntSyn.exp

  val constant   : Integers.int -> IntSyn.exp
end  (* signature CS_EQ_FIELD *)
