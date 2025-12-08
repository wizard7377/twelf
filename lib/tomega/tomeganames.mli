(* Naming *)
(* Author: Carsten Schuermann *)

module type TOMEGANAMES = 
  sig
    val decName : Tomega.Dec IntSyn.ctx * Tomega.Dec -> Tomega.Dec
  end