(* Extensible operation on foreign matter *)
(* Author: Aleksey Kliger *)

functor (* GEN BEGIN FUNCTOR DECL *) FgnOpnTable (type arg ; type result) :>
        FGN_OPN where type arg = arg
                where type result = result = struct
  type csid = int
  type rep = exn
  type arg = arg
  type result = result
  type func = (rep -> arg -> result)

  type table = func array

  fun initializeTable tbl = let
    exception CSfunNotInstalled of csid
    (* GEN BEGIN TAG OUTSIDE LET *) val maxCSid = (*Global.maxCSid*) 50 (* GEN END TAG OUTSIDE LET *)
    fun unimplemented csid = (* GEN BEGIN FUNCTION EXPRESSION *) fn _ => raise (CSfunNotInstalled csid) (* GEN END FUNCTION EXPRESSION *)
  in
      Array.tabulate (maxCSid +1 , unimplemented)
  end

  (* GEN BEGIN TAG OUTSIDE LET *) val table : table = initializeTable () (* GEN END TAG OUTSIDE LET *)

  fun install (csid, f) = Array.update (table, csid, f)

  fun apply (csid, rep) = Array.sub (table, csid) rep


end (* GEN END FUNCTOR DECL *)