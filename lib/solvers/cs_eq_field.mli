(* Gaussian-Elimination Equation Solver *)
(* Author: Roberto Virga *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature CS_EQ_FIELD =
sig
  include CS

  structure Field : FIELD
  (*! structure IntSyn : INTSYN !*)

  (* Foreign expressions *)

  type 'a mset = 'a list                 (* MultiSet                   *)

  datatype sum =                         (* Sum :                      *)
    Sum of Field.number * mon mset       (* Sum ::= m + M1 + ...       *)

  and mon =                              (* Monomials:                 *)
    Mon of Field.number * (IntSyn.exp * IntSyn.sub) mset
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

  val constant   : Field.number -> IntSyn.exp
end (* GEN END SIGNATURE DECLARATION *)  (* signature CS_EQ_FIELD *)
