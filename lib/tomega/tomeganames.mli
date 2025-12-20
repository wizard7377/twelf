(* Naming *)


(* Author: Carsten Schuermann *)


module type TOMEGANAMES = sig
  val decName : Tomega.dec IntSyn.ctx * Tomega.dec -> Tomega.dec

end
