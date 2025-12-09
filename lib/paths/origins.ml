(* Origins of Declarations *)
(* Author: Frank Pfenning *)

module Origins
  (Global : GLOBAL)
   (Table : TABLE with type key = string): ORIGINS =
   (*! module IntSyn' : INTSYN !*)
   (*! module Paths' : PATHS !*)
struct

  (*! module IntSyn = IntSyn' !*)
  (*! module Paths = Paths' !*)

  local
    let linesInfoTable : Paths.linesInfo Table.Table = Table.new (31)
    let rec reset () = Table.clear linesInfoTable
    let rec install (string, linesInfo) = Table.insert linesInfoTable (string, linesInfo)
    let rec lookup (string) = Table.lookup linesInfoTable string
  in
    let reset = reset
    let installLinesInfo = install
    let linesInfoLookup = lookup
  end

  local
    let originArray = Array.array (Global.maxCid+1, ("", NONE))
        : (string * Paths.occConDec option) Array.array
  in
    let rec installOrigin (cid, fileNameOpt) = Array.update (originArray, cid, fileNameOpt)
    let rec originLookup (cid) = Array.sub (originArray, cid)
  end

end;; (* functor Origins *)
