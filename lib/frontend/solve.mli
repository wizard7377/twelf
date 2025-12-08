(* Solve and query declarations, interactive top level *)
(* Author: Frank Pfenning *)

module type SOLVE =
sig

  (*! module IntSyn : INTSYN !*)
  (*! module Paths : PATHS !*)
  module ExtQuery : EXTQUERY

  exception AbortQuery of string

  val solve : ExtQuery.define list * ExtQuery.solve * Paths.location -> (IntSyn.ConDec * Paths.occConDec option) list

  val query : (int option * int option * ExtQuery.query) * Paths.location -> unit
					(* may raise AbortQuery(msg) *)

  val querytabled : (int option * int option * ExtQuery.query) * Paths.location -> unit
					(* may raise AbortQuery(msg) *)

  val qLoop  : unit -> bool		(* true means normal exit *)
  val qLoopT : unit -> bool		(* true means normal exit *)

end;; (* module type SOLVE *)
