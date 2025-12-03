
(** 
   A module type should only contain well-typed LF expressions.
   Thus, we check them before doing an insert.  To avoid copying
   the module type code, we instead use a phantom type.
   (See the paper "Phantom Types and Subtyping" by Fluet and Pucella)
*)
module type SIGNAT =
sig

  type ('phantom) sgn


  val empty : unit -> 'phantom sgn

  val insert : 'phantom sgn -> Syntax.const * Syntax.dec -> 'phantom sgn

  val lookup : 'phantom sgn -> Syntax.const -> Syntax.dec
  (** number of key/value pairs *)
  val size : 'phantom sgn -> int

end
