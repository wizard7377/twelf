(* Interface for error reporting  syntax *)
(* Author: Richard Fontana *)

(* compare to Paths *)

functor (* GEN BEGIN FUNCTOR DECL *) Interface  () : INTERFACE =
struct

  type pos = int
  val line = ref 0
  fun init_line () = (line := 1)
  fun next_line () = (line := !line + 1)

  fun error (errmsg, line:pos, _) =
    TextIO.output(TextIO.stdOut, "Line " ^ (Int.toString(line)) ^ ": "
                  ^ errmsg ^ "\n")

  type arg = unit

  val nothing = ()

end (* GEN END FUNCTOR DECL *)   (* functor INTERFACE  *)




