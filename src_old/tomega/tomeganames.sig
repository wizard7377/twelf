(* Naming *)
(* Author: Carsten Schuermann *)

signature TOMEGANAMES = 
  sig
    val decName : Tomega.dec IntSyn.ctx * Tomega.dec -> Tomega.dec
  end