open Basis
(* Ordered Field *)

(* Author: Roberto Virga *)

open Basis

module type ORDERED_FIELD = sig
  include Field.FIELD

  (* Sign operations *)
  val sign : number -> int
  val abs : number -> number

  (* Comparisons predicates *)
  val ( > ) : number * number -> bool
  val ( < ) : number * number -> bool
  val ( >= ) : number * number -> bool
  val ( <= ) : number * number -> bool
  val compare : number * number -> order
end

(* signature Order.Order.ORDERED_FIELD *)
