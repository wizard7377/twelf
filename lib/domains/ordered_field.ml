(* Ordered Field *)
(* Author: Roberto Virga *)

module type ORDERED_FIELD =
sig

  include FIELD

  (* Sign operations *)
  let sign : number -> int
  let abs  : number -> number

  (* Comparisons predicates *)
  let > : number * number -> bool
  let < : number * number -> bool
  let >= : number * number -> bool
  let <= : number * number -> bool
  let compare : number * number -> order

end;  (* module type ORDERED_FIELD *)

