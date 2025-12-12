(* Interface for error reporting  syntax *)
(* Author: Richard Fontana *)

(* compare to Paths *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature INTERFACE =
sig

  type pos
  val line : pos ref

  val init_line : unit -> unit
  val next_line : unit -> unit
  val error : string * pos * pos -> unit
    
  type arg
  val nothing : arg
end (* GEN END SIGNATURE DECLARATION *)  (* signature INTERFACE *)

