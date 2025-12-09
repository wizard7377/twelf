(* Syntax for elaborated modules *)
(* Author: Kevin Watkins *)

module type MODSYN =
sig

  (*! module IntSyn : INTSYN !*)
  module Names : NAMES
  (*! module Paths : PATHS !*)

  exception Error of string

  val abbrevify : IntSyn.cid * IntSyn.conDec -> IntSyn.conDec
  val strictify : IntSyn.conDec -> IntSyn.conDec

  type module

  (*
  type action = IntSyn.cid * (string * Paths.occConDec option) -> unit
  type transform = IntSyn.cid * IntSyn.conDec -> IntSyn.conDec
  *)

  val installStruct : IntSyn.StrDec * module * Names.namespace option
                        * (IntSyn.cid * (string * Paths.occConDec option) -> unit) (* action *)
                        * bool -> unit
  val installSig : module * Names.namespace option
                   * (IntSyn.cid * (string * Paths.occConDec option) -> unit) (* action *)
                   * bool -> unit
  val instantiateModule : module *
                          (Names.namespace -> (IntSyn.cid * IntSyn.conDec -> IntSyn.conDec))
			  (* Names.namespace -> transform *)
			  -> module

  (* Extract some entries of the current global module type table in order
     to create a self-contained module.
  *)
  val abstractModule : Names.namespace * IntSyn.mid option -> module

  val reset : unit -> unit
  val installSigDef : string * module -> unit (* Error if would shadow *)
  val lookupSigDef : string -> module option
  val sigDefSize : unit -> int
  val resetFrom : int -> unit

end
