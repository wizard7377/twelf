(* Compiler *)


(* Author: Iliano Cervesato *)


(* Modified: Jeff Polakow *)


(* Modified: Carsten Schuermann *)


(* Modified: Frank Pfenning *)


module type COMPILE = sig
(*! structure IntSyn: INTSYN !*)
(*! structure CompSyn: COMPSYN !*)
  exception Error of string
  optCompSyn.opt
  val optimize : opt ref
  val install : IntSyn.conDecForm -> IntSyn.cid -> unit
  val sProgReset : unit -> unit
  val compileCtx : bool -> (IntSyn.dec IntSyn.ctx) -> CompSyn.dProg
  val compileGoal : (IntSyn.dec IntSyn.ctx * IntSyn.exp) -> CompSyn.goal
(* for_sml the meta theorem prover  --cs *)
  val compilePsi : bool -> (Tomega.dec IntSyn.ctx) -> CompSyn.dProg

end


(* signature COMPILE *)

