(* External Syntax of Mode Declarations *)
(* Author: Carsten Schuermann *)

module type EXTMODES =
sig
  module ExtSyn : EXTSYN 
  (*! module Paths : PATHS  !*)

  type mode

  val plus  : Paths.region -> mode
  val star  : Paths.region -> mode
  val minus : Paths.region -> mode
  val minus1 : Paths.region -> mode

  type modedec 

  module Short :
  sig
    type mterm
    type mspine

    val mnil  : Paths.region -> mspine
    val mapp  : (mode * string option) * mspine -> mspine 
    val mroot : string list * string * Paths.region * mspine -> mterm

    val toModedec : mterm -> modedec
  end

  module Full :
  sig
    type mterm

    val mroot : ExtSyn.term * Paths.region -> mterm
    val mpi : mode * ExtSyn.dec * mterm -> mterm

    val toModedec : mterm -> modedec
  end

end;; (* module type EXTMODES *)


module type RECON_MODE =
sig
  (*! module ModeSyn : MODESYN !*)
  include EXTMODES

  exception Error of string
  val modeToMode : modedec -> (IntSyn.cid * ModeSyn.ModeSpine) * Paths.region
end;; (* module type RECON_MODE *)
