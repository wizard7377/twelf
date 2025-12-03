(* MTPStrategy : Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPSTRATEGY = 
sig
  module StateSyn : STATESYN

  val run : StateSyn.State list -> StateSyn.State list * StateSyn.State list 
              (* open cases -> remaining cases * solved cases *)
end;  (* module type MTPSTRATEGY *)
