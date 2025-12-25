(**
   An equivalent to some of the Standard ML Basis Library modules.
   Included here for compatibilities sake.

   @author Asher Frost
*)

(** Order type *)
type order = Prelude.order

let less = Prelude.less
let equal = Prelude.equal
let greater = Prelude.greater

module Time = Time.Time
module Vector = Vector.Vector
module Integer = Integer.Integer
