(* Origins of Declarations *)
(* Author: Frank Pfenning *)

functor (* GEN BEGIN FUNCTOR DECL *) Origins
  (structure Global : GLOBAL
   structure Table : TABLE where type key = string
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Paths' : PATHS !*)
     )
  : ORIGINS =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)

  local
    (* GEN BEGIN TAG OUTSIDE LET *) val linesInfoTable : Paths.lines_info Table.table = Table.new (31) (* GEN END TAG OUTSIDE LET *)
    fun reset () = Table.clear linesInfoTable
    fun install (string, linesInfo) = Table.insert linesInfoTable (string, linesInfo)
    fun lookup (string) = Table.lookup linesInfoTable string
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val installLinesInfo = install (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val linesInfoLookup = lookup (* GEN END TAG OUTSIDE LET *)
  end

  local
    (* GEN BEGIN TAG OUTSIDE LET *) val originArray = Array.array (Global.maxCid+1, ("", NONE))
        : (string * Paths.occ_con_dec option) Array.array (* GEN END TAG OUTSIDE LET *)
  in
    fun installOrigin (cid, fileNameOpt) = Array.update (originArray, cid, fileNameOpt)
    fun originLookup (cid) = Array.sub (originArray, cid)
  end

end (* GEN END FUNCTOR DECL *);  (* functor Origins *)
