(* State definition for_sml Proof Search *)

(* Author: Carsten Schuermann *)

module type STATE = sig
  exception Error of string

  type state =
    | State of
        Tomega.worlds * Tomegas.dec IntSyn.ctx * Tomega.prg * Tomega.for_sml
    | StateLF of IntSyn.exp

  type focus = Focus of Tomega.prg * Tomega.worlds | FocusLF of IntSyn.exp

  (* focus EVar *)
  val init : Tomega.for_sml * Tomega.worlds -> state
  val close : state -> bool
  val collectT : Tomega.prg -> Tomega.prg list
  val collectLF : Tomega.prg -> IntSyn.exp list
  val collectLFSub : Tomega.sub -> IntSyn.exp list
end
