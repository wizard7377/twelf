(** CommandLine module - SML Basis Library COMMAND_LINE signature *)

module type COMMAND_LINE = sig
  val name : unit -> string
  val arguments : unit -> string list
end

module CommandLine : COMMAND_LINE = struct
  let name () =
    (* Get the program name (first element of Sys.argv) *)
    if Stdlib.Array.length Sys.argv > 0 then
      Stdlib.Array.get Sys.argv 0
    else
      ""

  let arguments () =
    (* Get command line arguments (all but the first element) *)
    if Stdlib.Array.length Sys.argv > 1 then
      Stdlib.Array.to_list (Stdlib.Array.sub Sys.argv 1 (Stdlib.Array.length Sys.argv - 1))
    else
      []
end
