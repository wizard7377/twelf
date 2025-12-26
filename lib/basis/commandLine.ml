(** CommandLine module - SML Basis Library COMMAND_LINE signature *)

module type COMMAND_LINE = sig
  val name : unit -> string
  val arguments : unit -> string list
end

module CommandLine : COMMAND_LINE = struct
  let name () =
    (* Get the program name (first element of Sys.argv) *)
    if Array.length Sys.argv > 0 then
      Sys.argv.(0)
    else
      ""

  let arguments () =
    (* Get command line arguments (all but the first element) *)
    if Array.length Sys.argv > 1 then
      Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1))
    else
      []
end
