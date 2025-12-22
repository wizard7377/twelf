module type TIME_LIMIT = sig
  exception TimeOut

  val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
end
(* Default implementation of timeLimit *)

(* Ignores time limit *)

module TimeLimit : TIME_LIMIT = struct
  exception TimeOut

  let timeLimit = fun t -> fun f -> fun x -> f x
end
