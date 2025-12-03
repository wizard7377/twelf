(* Strategy *)
(* Author: Carsten Schuermann *)

module type STRATEGY = 
sig
  module MetaSyn : METASYN

  val run : MetaSyn.State list -> MetaSyn.State list * MetaSyn.State list 
              (* open cases -> remaining cases * solved cases *)

end;  (* module type STRATEGY *)
