(* Origins of Declarations *)
(* Author: Frank Pfenning *)

module Origins
  (Global : GLOBAL)
   (Table : TABLE where type key = string): ORIGINS =
   (*! module IntSyn' : INTSYN !*)
   (*! module Paths' : PATHS !*)
struct

  (*! module IntSyn = IntSyn' !*)
  (*! module Paths = Paths' !*)

  local
    let linesInfoTable : Paths.linesInfo Table.Table = Table.new (31)
    fun reset () = Table.clear linesInfoTable
    fun install (string, linesInfo) = Table.insert linesInfoTable (string, linesInfo)
    fun lookup (string) = Table.lookup linesInfoTable string
  in
    let reset = reset
    let installLinesInfo = install
    let linesInfoLookup = lookup
  end

  local
    let originArray = Array.array (Global.maxCid+1, ("", NONE))
        : (string * Paths.occConDec option) Array.array
  in
    fun installOrigin (cid, fileNameOpt) = Array.update (originArray, cid, fileNameOpt)
    fun originLookup (cid) = Array.sub (originArray, cid)
  end

end;; (* functor Origins *)
