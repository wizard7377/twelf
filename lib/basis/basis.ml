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
let rev = Prelude.rev
let print = Prelude.print
module Array = Array.Array
module Time = Time.Time
module Vector = Vector.Vector
module List = List.List
module Integer = Integer.Integer
module Char = Char.Char
module TextIO = TextIO.TextIO
               
