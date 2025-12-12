(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature STATE =
sig
  exception Error of string

  datatype state =
    State of Tomega.worlds 
      * Tomegas.dec IntSyn.ctx * Tomega.prg * Tomega.for	
  | StateLF of IntSyn.exp

  datatype focus = 
    Focus of Tomega.prg * Tomega.worlds (* Focus (EVar, W) *)
  | FocusLF of IntSyn.exp	        (* focus EVar *)
 
  val init : Tomega.for * Tomega.worlds -> state
  val close : state -> bool  

  val collectT  : Tomega.prg -> Tomega.prg list
  val collectLF : Tomega.prg -> IntSyn.exp list
  val collectLFSub : Tomega.sub -> IntSyn.exp list
end (* GEN END SIGNATURE DECLARATION *)