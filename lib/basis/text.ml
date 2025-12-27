(** Text module - SML Basis Library TEXT signature *)

module type TEXT = sig
  module Char : Char.CHAR
  module String : String.STRING
  module Substring : Substring.SUBSTRING
  module CharVector : CharVector.MONO_VECTOR
  module CharArray : CharArray.MONO_ARRAY
  module CharVectorSlice : CharVectorSlice.MONO_VECTOR_SLICE
  module CharArraySlice : CharArraySlice.MONO_ARRAY_SLICE
end

module Text : TEXT = struct
  module Char = Char.Char
  module String = String.String
  module Substring = Substring.Substring
  module CharVector = CharVector.CharVector
  module CharArray = CharArray.CharArray
  module CharVectorSlice = CharVectorSlice.CharVectorSlice
  module CharArraySlice = CharArraySlice.CharArraySlice
end
