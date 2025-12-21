(* Extensible operation on foreign matter *)

(* Author: Aleksey Kliger *)

module FgnOpnTable (A : sig
  type t
end) (R : sig
  type t
end) : FGN_OPN with type arg = A.t with type result = R.t = struct
  type csid = int
  type rep = exn
  type arg = A.t
  type result = R.t
  type func = rep -> arg -> result
  type table = func array

  let rec initializeTable tbl =
    let exception CSfunNotInstalled of csid in
    let maxCSid =
      (*Global.maxCSid*)
      50
    in
    let rec unimplemented csid = fun _ -> raise (CSfunNotInstalled csid) in
    Array.tabulate (maxCSid + 1, unimplemented)

  let table : table = initializeTable ()
  let rec install (csid, f) = Array.update (table, csid, f)
  let rec apply (csid, rep) = Array.sub (table, csid) rep
end
