(* Compatibility shim to cope with Standard Basis version skew *)

(* Author: Christopher Richards *)

module type COMPAT_TEXT_IO = sig
  val inputLine : TextIO.instream -> string option
end
(* Compatibility shim from Basis-current TextIO to Basis-97 TextIO *)

(* Author: Christopher Richards *)

module CompatTextIO97 : COMPAT_TEXT_IO = struct
  let rec inputLine instream =
    let line = TextIO.inputLine instream in
    match line with "" -> None | str -> Some str
end
