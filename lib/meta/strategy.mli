(* MTPStrategy : Version 1.3 *)


(* Author: Carsten Schuermann *)


module type MTPSTRATEGY = sig
  module StateSyn : STATESYN
  val run : StateSyn.state list -> StateSyn.state list * StateSyn.state list
(* open cases -> remaining cases * solved cases *)

end


(* signature MTPSTRATEGY *)

