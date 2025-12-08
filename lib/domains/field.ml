(* Field *)
(* Author: Roberto Virga *)

module type FIELD =
sig

  (* Name of the set *)
  let name : string

  (* Main type *)
  eqtype number

  (* Non-invertible element *)
  exception Div

  (* Constants *)
  let zero : number
  let one  : number

  (* Operators *)
  let ~ : number -> number
  let + : number * number -> number
  let - : number * number -> number
  let * : number * number -> number
  let inverse : number -> number  (* raises Div *)

  (* Conversions *)
  let fromInt    : int -> number
  let fromString : string -> number option
  let toString   : number -> string

end;; (* module type FIELD *)

