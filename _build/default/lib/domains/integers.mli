(* Integers *)
(* Author: Roberto Virga *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature INTEGERS =
sig
  include INTEGER

  val gcd : int * int -> int
  val lcm : int * int -> int
  val solve_gcd : int * int -> int * int
end (* GEN END SIGNATURE DECLARATION *);  (* signature INTEGERS *)

