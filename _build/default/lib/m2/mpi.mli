(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MPI =
sig
  structure MetaSyn : METASYN

  exception Error of string 

  val init   : (int * string list) -> unit
  val select : int -> unit 
  val print  : unit -> unit
  val next   : unit -> unit
  val auto   : unit -> unit
  val solve  : unit -> unit
  val lemma  : string -> unit

  val reset  : unit -> unit
  val extract: unit -> MetaSyn.sgn
  val show   : unit -> unit
  val undo   : unit -> unit 
end (* GEN END SIGNATURE DECLARATION *);  (* signature MPI *)


