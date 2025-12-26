(**
   An equivalent to some of the Standard ML Basis Library modules.
   Included here for compatibilities sake.

   @author Asher Frost
*)


type order = Order.order
let print s = print_string s ;;
let rev lst = Stdlib.List.rev lst ;;

module Array = Array.Array
module Time = Time.Time
module Vector = Vector.Vector
module List = List.List
module Integer = Integer.Integer
module Char = Char.Char
module TextIO = TextIO.TextIO
module Word8 = Word.Word8
module Word32 = Word.Word32
module String = String.String