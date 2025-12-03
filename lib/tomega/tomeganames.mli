(* Naming *)
(* Author: Carsten Schuermann *)

module type TOMEGANAMES = 
  sig
    val decName : Tomega.Dec IntSyn.Ctx * Tomega.Dec -> Tomega.Dec
  end