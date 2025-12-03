(* Extensible operation on foreign matter *)
(* Author: Aleksey Kliger *)

module type FGN_OPN = sig
  type csid = int
  type rep = exn
  type arg
  type result

  type func = rep -> arg -> result

  let install : csid * func -> unit

  let apply : csid * rep -> arg -> result
end

