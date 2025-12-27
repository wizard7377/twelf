open StringCvt
(** Byte module - SML Basis Library BYTE signature *)

open Substring

module type BYTE = sig
  val byteToChar : int -> char
  val charToByte : char -> int
  val bytesToString : int list -> string
  val stringToBytes : string -> int list
  val unpackStringVec : int list -> string
  val unpackString : int array -> string
  val packString : int array * int * Substring.substring -> unit
end

module Byte : BYTE = struct
  let byteToChar w =
    if w < 0 || w > 255 then raise (Invalid_argument "Byte.byteToChar")
    else Stdlib.Char.chr w

  let charToByte c = Stdlib.Char.code c

  let bytesToString vec =
    (* vec is int list in our representation *)
    let buf = Buffer.create (Stdlib.List.length vec) in
    Stdlib.List.iter (fun b -> Buffer.add_char buf (Stdlib.Char.chr b)) vec;
    Buffer.contents buf

  let stringToBytes str =
    (* Returns int list *)
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (Stdlib.Char.code (Stdlib.String.get str i) :: acc)
    in
    loop (Stdlib.String.length str - 1) []

  let unpackStringVec vec = bytesToString vec

  let unpackString arr =
    (* arr is int array *)
    let buf = Buffer.create (Stdlib.Array.length arr) in
    Stdlib.Array.iter (fun b -> Buffer.add_char buf (Stdlib.Char.chr b)) arr;
    Buffer.contents buf

  let packString (arr, offset, ss) =
    (* Placeholder - requires full substring implementation *)
    ()
end
