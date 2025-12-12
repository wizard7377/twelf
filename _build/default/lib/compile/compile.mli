(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature COMPILE =
sig

  (*! structure IntSyn: INTSYN !*)
  (*! structure CompSyn: COMPSYN !*)


  exception Error of string

  datatype opt = datatype CompSyn.opt

  val optimize : opt ref

  val install : IntSyn.con_dec_form -> IntSyn.cid -> unit

  val sProgReset : unit -> unit


  val compileCtx: bool -> (IntSyn.dec IntSyn.ctx) -> CompSyn.d_prog  

  val compileGoal: (IntSyn.dec IntSyn.ctx * IntSyn.exp) -> CompSyn.goal

  (* for the meta theorem prover  --cs *)
  val compilePsi: bool -> (Tomega.dec IntSyn.ctx) -> CompSyn.d_prog
 

end (* GEN END SIGNATURE DECLARATION *); (* signature COMPILE *)
