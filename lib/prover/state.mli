(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

module type STATE =
sig
  exception Error of string

  type state =
    State of Tomega.Worlds 
      * Tomegas.Dec IntSyn.ctx * Tomega.Prg * Tomega.For	
  | StateLF of IntSyn.exp

  type focus = 
    Focus of Tomega.Prg * Tomega.Worlds (* Focus (EVar, W) *)
  | FocusLF of IntSyn.exp	        (* focus EVar *)
 
  val init : Tomega.For * Tomega.Worlds -> State
  val close : State -> bool  

  val collectT  : Tomega.Prg -> Tomega.Prg list
  val collectLF : Tomega.Prg -> IntSyn.exp list
  val collectLFSub : Tomega.Sub -> IntSyn.exp list
end