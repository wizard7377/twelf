(** The Basis Library - Standard ML Basis Library compatibility layer.

    This module provides an OCaml implementation of commonly-used Standard ML
    Basis Library modules, enabling compatibility with code ported from the
    original SML implementation of Twelf.

    The basis library wraps OCaml standard library functionality with SML-style
    interfaces, providing modules for arrays, vectors, lists, integers, characters,
    text I/O, and time operations.

    @author Asher Frost
*)

(** Core prelude definitions used throughout the basis library.

    This module provides fundamental types and functions that are used
    across the SML compatibility layer, including the ordering type and
    basic utility functions.
*)

(** Ordering type for comparison operations.

    Represents the result of comparing two values. This type is used
    throughout Twelf for consistent comparison semantics compatible
    with Standard ML. Has three constructors: [Less], [Equal], [Greater].
*)
type order = Order.order

(** Print a string to standard output.

    Provides SML-compatible printing functionality.

    @param s The string to print
*)
val print : string -> unit

(** Reverse a list.

    @param lst The list to reverse
    @return The reversed list
*)
val rev : 'a list -> 'a list


(** Mutable arrays with SML-style interface.
    Provides operations for creating, accessing, and modifying arrays. *)
module Array : Array.ARRAY

(** Time operations compatible with SML Time structure.
    Provides timing functionality with conversions between different time units. *)
module Time : Time.TIME

(** Immutable vectors (persistent arrays) with SML-style interface.
    Vectors are similar to arrays but immutable, backed by OCaml arrays. *)
module Vector : Vector.VECTOR

(** List operations compatible with SML List structure.
    Provides standard list manipulation functions following SML conventions. *)
module List : List.LIST

(** Integer operations compatible with SML Int structure.
    Provides arithmetic, comparison, and conversion operations for integers. *)
module Integer : Integer.INTEGER

(** Character operations compatible with SML Char structure.
    Provides character manipulation and classification functions. *)
module Char : Char.CHAR

(** Text I/O operations compatible with SML TextIO structure.
    Provides file and stream I/O operations for text. *)
module TextIO : TextIO.TEXTIO

module Word8 : (Word.WORD with type word = int)
module Word32 : (Word.WORD with type word = int)
module String : String.STRING

(** High-priority commonly used modules *)

(** Option type operations compatible with SML Option structure. *)
module Option : Option.OPTION

(** Operations on pairs of lists compatible with SML ListPair structure. *)
module ListPair : ListPair.LIST_PAIR

(** Boolean operations compatible with SML Bool structure. *)
module Bool : Bool.BOOL

(** String conversion utilities compatible with SML StringCvt structure. *)
module StringCvt : StringCvt.STRING_CVT

(** Substring operations compatible with SML Substring structure. *)
module Substring : Substring.SUBSTRING

(** General utilities and exceptions compatible with SML General structure. *)
module General : General.GENERAL

(** Command line argument access compatible with SML CommandLine structure. *)
module CommandLine : CommandLine.COMMAND_LINE

(** Array and Vector slices *)

(** Array slice operations compatible with SML ArraySlice structure. *)
module ArraySlice : ArraySlice.ARRAY_SLICE

(** Vector slice operations compatible with SML VectorSlice structure. *)
module VectorSlice : VectorSlice.VECTOR_SLICE

(** Character array and vector modules *)

(** Monomorphic char arrays compatible with SML CharArray structure. *)
module CharArray : CharArray.MONO_ARRAY

(** Monomorphic char array slices compatible with SML CharArraySlice structure. *)
module CharArraySlice : CharArraySlice.MONO_ARRAY_SLICE

(** Monomorphic char vectors compatible with SML CharVector structure. *)
module CharVector : CharVector.MONO_VECTOR

(** Monomorphic char vector slices compatible with SML CharVectorSlice structure. *)
module CharVectorSlice : CharVectorSlice.MONO_VECTOR_SLICE

(** Word8 array and vector modules *)

(** Monomorphic Word8 arrays. *)
module Word8Array : Word8Array.WORD8_ARRAY

(** Monomorphic Word8 vectors. *)
module Word8Vector : Word8Vector.WORD8_VECTOR

(** Numeric modules *)

(** Real (floating-point) operations compatible with SML Real structure. *)
module Real : Real.REAL

(** Mathematical functions compatible with SML Math structure. *)
module Math : Math.MATH

(** Large integer operations compatible with SML LargeInt structure. *)
module LargeInt : LargeInt.LARGE_INT

(** Date and Time modules *)

(** Date operations compatible with SML Date structure. *)
module Date : Date.DATE

(** Timer operations compatible with SML Timer structure. *)
module Timer : Timer.TIMER

(** I/O modules *)

(** I/O exceptions and types compatible with SML IO structure. *)
module IO : Io.IO

(** Text structure grouping char-related modules. *)
module Text : Text.TEXT

(** Byte conversions compatible with SML Byte structure. *)
module Byte : Byte.BYTE

(** OS modules *)

(** Path operations compatible with SML OS.Path structure. *)
module OS_Path : OsPath.OS_PATH