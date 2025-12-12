(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature FQUERY =
sig
  structure ExtQuery : EXTQUERY

  exception AbortQuery of string

  val run : ExtQuery.query * Paths.location -> unit
					(* may raise AbortQuery(msg) *)

end (* GEN END SIGNATURE DECLARATION *);  (* signature SOLVE *)
