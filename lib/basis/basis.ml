(**
   An equivalent to some of the Standard ML Basis Library modules.
   Included here for compatibilities sake.

   @author Asher Frost
*)


type order = Order.order
let print s = print_string s ;;
let rev lst = Stdlib.List.rev lst ;;

(* Core modules *)
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

(* High-priority modules *)
module Option = Option.Option
module ListPair = ListPair.ListPair
module Bool = Bool.Bool
module StringCvt = StringCvt.StringCvt
module Substring = Substring.Substring
module General = General.General
module CommandLine = CommandLine.CommandLine

(* Array/Vector slices *)
module ArraySlice = ArraySlice.ArraySlice
module VectorSlice = VectorSlice.VectorSlice

(* Char modules *)
module CharArray = CharArray.CharArray
module CharArraySlice = CharArraySlice.CharArraySlice
module CharVector = CharVector.CharVector
module CharVectorSlice = CharVectorSlice.CharVectorSlice

(* Word8 modules *)
module Word8Array = Word8Array.Word8Array
module Word8Vector = Word8Vector.Word8Vector

(* Numeric modules *)
module Real = Real.Real
module Math = Math.Math
module LargeInt = LargeInt.LargeInt

(* Date/Time *)
module Date = Date.Date
module Timer = Timer.Timer

(* I/O *)
module IO = Io.IO
module Text = Text.Text
module Byte = Byte.Byte

(* OS *)
module OS_Path = OsPath.OSPath