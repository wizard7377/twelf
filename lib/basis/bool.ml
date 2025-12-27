(** Bool module - SML Basis Library BOOL signature *)
open StringCvt
module type BOOL = sig
  (* OCaml's bool is built-in: type bool = false | true *)

  val not : bool -> bool
  val toString : bool -> string
  val fromString : string -> bool option
  val scan : (char, 'a) StringCvt.reader -> (bool, 'a) StringCvt.reader
end

module Bool : BOOL = struct
  (* OCaml's built-in bool type: type bool = false | true *)

  let not b = if b then false else true

  let toString b = if b then "true" else "false"

  let fromString s =
    match s with
    | "true" -> Some true
    | "false" -> Some false
    | _ -> None

  (* Note: scan requires StringCvt module, will implement basic version *)
  let scan reader state =
    (* This is a placeholder until StringCvt is fully implemented *)
    (* The SML signature expects a reader function *)
    None
end
