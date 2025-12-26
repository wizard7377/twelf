(** General module - SML Basis Library GENERAL signature *)

module type GENERAL = sig
  type unit = unit
  type exn = exn

  exception Bind
  exception Match
  exception Chr
  exception Div
  exception Domain
  exception Fail of string
  exception Overflow
  exception Size
  exception Span
  exception Subscript

  val exnName : exn -> string
  val exnMessage : exn -> string

  type order = Order.order

  val deref : 'a ref -> 'a
  val assign : 'a ref * 'a -> unit
  val o : ('a -> 'b) * ('c -> 'a) -> 'c -> 'b
  val before : 'a * unit -> 'a
  val ignore : 'a -> unit
end

module General : GENERAL = struct
  type unit = unit
  type exn = exn

  (* Standard SML exceptions *)
  exception Bind
  exception Match
  exception Chr
  exception Div
  exception Domain
  exception Fail of string
  exception Overflow
  exception Size
  exception Span
  exception Subscript

  let exnName exn =
    (* Get the name of an exception *)
    Printexc.to_string exn

  let exnMessage exn =
    (* Get the full message of an exception *)
    Printexc.to_string exn

  (* Order type from Order module *)
  type order = Order.order

  (* Reference operations *)
  let deref r = !r
  let assign (r, v) = r := v

  (* Function composition *)
  let o (f, g) x = f (g x)

  (* before: evaluate both expressions, return first *)
  let before (x, _) = x

  (* ignore: discard value *)
  let ignore _ = ()
end
