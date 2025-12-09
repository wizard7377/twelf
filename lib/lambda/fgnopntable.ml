(* Extensible operation on foreign matter *)
(* Author: Aleksey Kliger *)

module FgnOpnTable (type arg ; type result) :
        FGN_OPN with type arg = arg
                with type result = result = struct
  type csid = int
  type rep = exn
  type arg = arg
  type result = result
  type func = (rep -> arg -> result)

  type table = func array

  let rec initializeTable tbl = let
    exception CSfunNotInstalled of csid
    let maxCSid = (*Global.maxCSid*) 50
    let rec unimplemented csid = fun _ -> raise (CSfunNotInstalled csid)
  in
      Array.tabulate (maxCSid +1 , unimplemented)
  end

  let table : table = initializeTable ()

  let rec install (csid, f) = Array.update (table, csid, f)

  let rec apply (csid, rep) = Array.sub (table, csid) rep


end