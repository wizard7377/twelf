
module type TRANSLATE =
sig

  (** Translate a Twelf declaration to a Flewt declaration. *)
  val translate_condec : IntSyn.cid * IntSyn.conDec -> Syntax.dec

  (** Translate the currently loaded Twelf module type to Flewt *)
  val translate_signat : unit -> (Syntax.const * Syntax.dec) list

end

