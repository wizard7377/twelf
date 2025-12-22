(* Interface for_sml error reporting  syntax *)


(* Author: Richard Fontana *)


(* compare to Paths *)


module Interface : INTERFACE = struct type pos = int
let line = ref 0
let rec init_line ()  = (line := 1)
let rec next_line ()  = (line := ! line + 1)
let rec error (errmsg, line : pos, _)  = TextIO.output (TextIO.stdOut, "Line " ^ (Int.toString (line)) ^ ": " ^ errmsg ^ "\n")
type arg = unit
let nothing = ()
 end

(* functor INTERFACE  *)

