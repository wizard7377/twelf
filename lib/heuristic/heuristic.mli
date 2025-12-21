(* Heuristics : Version 1.3 *)

(* Author: Carsten Schuermann *)

module type HEURISTIC = sig
  type index =
    < sd : int ; ind : int option ; c : int ; m : int ; r : int ; p : int >

  (* Position (left to right) *)
  val compare : index * index -> order
  val indexToString : index -> string
end

(* signature HEURISTIC *)
