open Basis ;; 
(* Interface for_sml error reporting  syntax *)

(* Author: Richard Fontana *)

(* compare to Paths *)

module type INTERFACE = sig
  type pos

  val line : pos ref
  val init_line : unit -> unit
  val next_line : unit -> unit
  val error : string * pos * pos -> unit

  type arg

  val nothing : arg
end

(* signature INTERFACE *)
(* Interface for_sml error reporting  syntax *)

(* Author: Richard Fontana *)

(* compare to Paths *)

module Interface : INTERFACE = struct
  type pos = int

  let line = ref 0
  let rec init_line () = line := 1
  let rec next_line () = line := !line + 1

  let rec error (errmsg, (line : pos), _) =
    TextIO.output
      (TextIO.stdOut, "Line " ^ Int.toString line ^ ": " ^ errmsg ^ "\n")

  type arg = unit

  let nothing = ()
end

(* functor INTERFACE  *)
