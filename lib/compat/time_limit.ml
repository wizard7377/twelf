(* Default implementation of timeLimit *)

(* Ignores time limit *)

module TimeLimit : TIME_LIMIT = struct
  exception TimeOut

  let timeLimit = fun t -> fun f -> fun x -> f x
end
