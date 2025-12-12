(* Syntax for elaborated modules *)
(* Author: Kevin Watkins *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MODSYN =
sig

  (*! structure IntSyn : INTSYN !*)
  structure Names : NAMES
  (*! structure Paths : PATHS !*)

  exception Error of string

  val abbrevify : IntSyn.cid * IntSyn.con_dec -> IntSyn.con_dec
  val strictify : IntSyn.con_dec -> IntSyn.con_dec

  type module

  (*
  type action = IntSyn.cid * (string * Paths.occConDec option) -> unit
  type transform = IntSyn.cid * IntSyn.ConDec -> IntSyn.ConDec
  *)

  val installStruct : IntSyn.str_dec * module * Names.namespace option
                        * (IntSyn.cid * (string * Paths.occ_con_dec option) -> unit) (* action *)
                        * bool -> unit
  val installSig : module * Names.namespace option
                   * (IntSyn.cid * (string * Paths.occ_con_dec option) -> unit) (* action *)
                   * bool -> unit
  val instantiateModule : module *
                          (Names.namespace -> (IntSyn.cid * IntSyn.con_dec -> IntSyn.con_dec))
			  (* Names.namespace -> transform *)
			  -> module

  (* Extract some entries of the current global signature table in order
     to create a self-contained module.
  *)
  val abstractModule : Names.namespace * IntSyn.mid option -> module

  val reset : unit -> unit
  val installSigDef : string * module -> unit (* Error if would shadow *)
  val lookupSigDef : string -> module option
  val sigDefSize : unit -> int
  val resetFrom : int -> unit

end (* GEN END SIGNATURE DECLARATION *)
