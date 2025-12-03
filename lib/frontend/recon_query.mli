(* External Syntax for queries *)
(* Author: Frank Pfenning *)

module type EXTQUERY =
sig

  module ExtSyn : EXTSYN
  (*! module Paths : PATHS !*)

  type query				(* query *)
  val query : string option * ExtSyn.term -> query (* ucid : tm | tm *)

  type define
  val define : string option * ExtSyn.term * ExtSyn.term option -> define

  type solve
  val solve : string option * ExtSyn.term * Paths.region -> solve (* id : tm | _ : tm *)

end (* module type EXTQUERY *)

module type RECON_QUERY =
sig

  (*! module IntSyn : INTSYN !*)
  include EXTQUERY

  exception Error of string

  val queryToQuery : query * Paths.location
                     -> IntSyn.Exp * string option * (IntSyn.Exp * string) list
                     (* (A, SOME("X"), [(Y1, "Y1"),...] *)
		     (* where A is query type, X the optional proof term variable name *)
		     (* Yi the EVars in the query and "Yi" their names *)

  val solveToSolve : define list * solve * Paths.location
                     -> IntSyn.Exp * (IntSyn.Exp -> (IntSyn.ConDec * Paths.occConDec option) list)
  
end (* module type RECON_QUERY *)
