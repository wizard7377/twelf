(* Origins of Declarations *)
(* Author: Frank Pfenning *)

signature ORIGINS =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)

  val reset : unit -> unit
  val installLinesInfo : string * Paths.lines_info -> unit
  val linesInfoLookup : string -> Paths.lines_info option

  val installOrigin : IntSyn.cid * (string * Paths.occ_con_dec option) -> unit
  val originLookup : IntSyn.cid -> (string * Paths.occ_con_dec option)

end;  (* signature ORIGINS *)
