(* External Syntax for queries *)
(* Author: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature EXTQUERY =
sig

  structure ExtSyn : EXTSYN
  (*! structure Paths : PATHS !*)

  type query				(* query *)
  val query : string option * ExtSyn.term -> query (* ucid : tm | tm *)

  type define
  val define : string option * ExtSyn.term * ExtSyn.term option -> define

  type solve
  val solve : string option * ExtSyn.term * Paths.region -> solve (* id : tm | _ : tm *)

end (* GEN END SIGNATURE DECLARATION *) (* signature EXTQUERY *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature RECON_QUERY =
sig

  (*! structure IntSyn : INTSYN !*)
  include EXTQUERY

  exception Error of string

  val queryToQuery : query * Paths.location
                     -> IntSyn.exp * string option * (IntSyn.exp * string) list
                     (* (A, SOME("X"), [(Y1, "Y1"),...] *)
		     (* where A is query type, X the optional proof term variable name *)
		     (* Yi the EVars in the query and "Yi" their names *)

  val solveToSolve : define list * solve * Paths.location
                     -> IntSyn.exp * (IntSyn.exp -> (IntSyn.con_dec * Paths.occ_con_dec option) list)
  
end (* GEN END SIGNATURE DECLARATION *) (* signature RECON_QUERY *)
