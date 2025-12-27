(** The Basis Library - Standard ML Basis Library compatibility layer.

    This module provides an OCaml implementation of commonly-used Standard ML
    Basis Library modules, enabling compatibility with code ported from the
    original SML implementation of Twelf.

    The basis library wraps OCaml standard library functionality with SML-style
    interfaces, providing modules for arrays, vectors, lists, integers,
    characters, text I/O, and time operations.

    @author Asher Frost *)

(** Core prelude definitions used throughout the basis library.

    This module provides fundamental types and functions that are used across
    the SML compatibility layer, including the ordering type and basic utility
    functions. *)

(** Ordering type for comparison operations.

    Represents the result of comparing two values. This type is used throughout
    Twelf for consistent comparison semantics compatible with Standard ML. Has
    three constructors: [Less], [Equal], [Greater]. *)
type order = Order.order = Less | Equal | Greater

val print : string -> unit
(** Print a string to standard output.

    Provides SML-compatible printing functionality.

    @param s The string to print *)

val rev : 'a list -> 'a list
(** Reverse a list.

    @param lst The list to reverse
    @return The reversed list *)

module Array : Array.ARRAY
(** Mutable arrays with SML-style interface. Provides operations for creating,
    accessing, and modifying arrays. *)

module Time : Time.TIME
(** Time operations compatible with SML Time structure. Provides timing
    functionality with conversions between different time units. *)

module Vector : Vector.VECTOR
(** Immutable vectors (persistent arrays) with SML-style interface. Vectors are
    similar to arrays but immutable, backed by OCaml arrays. *)

module List : List.LIST
(** List operations compatible with SML List structure. Provides standard list
    manipulation functions following SML conventions. *)

module Integer : Integer.INTEGER
(** Integer operations compatible with SML Int structure. Provides arithmetic,
    comparison, and conversion operations for integers. *)

module Char : Char.CHAR
(** Character operations compatible with SML Char structure. Provides character
    manipulation and classification functions. *)

(** Text I/O operations compatible with SML TextIO structure. Provides file and
    stream I/O operations for text. *)
(* module TextIO : TextIO.TEXTIO *)

module Word8 : Word.WORD with type word = int
module Word32 : Word.WORD with type word = int
module String : String.STRING

(** High-priority commonly used modules *)

module Option : Option.OPTION
(** Option type operations compatible with SML Option structure. *)

module ListPair : ListPair.LIST_PAIR
(** Operations on pairs of lists compatible with SML ListPair structure. *)

module Bool : Bool.BOOL
(** Boolean operations compatible with SML Bool structure. *)

module StringCvt : StringCvt.STRING_CVT
(** String conversion utilities compatible with SML StringCvt structure. *)

module Substring : Substring.SUBSTRING
(** Substring operations compatible with SML Substring structure. *)

module General : General.GENERAL
(** General utilities and exceptions compatible with SML General structure. *)

module CommandLine : CommandLine.COMMAND_LINE
(** Command line argument access compatible with SML CommandLine structure. *)

(** Array and Vector slices *)

module ArraySlice : ArraySlice.ARRAY_SLICE
(** Array slice operations compatible with SML ArraySlice structure. *)

module VectorSlice : VectorSlice.VECTOR_SLICE
(** Vector slice operations compatible with SML VectorSlice structure. *)

(** Character array and vector modules *)

module CharArray : CharArray.MONO_ARRAY
(** Monomorphic char arrays compatible with SML CharArray structure. *)

module CharArraySlice : CharArraySlice.MONO_ARRAY_SLICE
(** Monomorphic char array slices compatible with SML CharArraySlice structure.
*)

module CharVector : CharVector.MONO_VECTOR
(** Monomorphic char vectors compatible with SML CharVector structure. *)

module CharVectorSlice : CharVectorSlice.MONO_VECTOR_SLICE
(** Monomorphic char vector slices compatible with SML CharVectorSlice
    structure. *)

(** Word8 array and vector modules *)

module Word8Array : Word8Array.WORD8_ARRAY
(** Monomorphic Word8 arrays. *)

module Word8Vector : Word8Vector.WORD8_VECTOR
(** Monomorphic Word8 vectors. *)

(** Numeric modules *)

module Real : Real.REAL
(** Real (floating-point) operations compatible with SML Real structure. *)

module Math : Math.MATH
(** Mathematical functions compatible with SML Math structure. *)

module LargeInt : LargeInt.LARGE_INT
(** Large integer operations compatible with SML LargeInt structure. *)

(** Date and Time modules *)

module Date : Date.DATE
(** Date operations compatible with SML Date structure. *)

module Timer : Timer.TIMER
(** Timer operations compatible with SML Timer structure. *)

(** I/O modules *)

module IO : Io.IO
(** I/O exceptions and types compatible with SML IO structure. *)

module Text : Text.TEXT
(** Text structure grouping char-related modules. *)

module Byte : Byte.BYTE
(** Byte conversions compatible with SML Byte structure. *)

module TextIO : TextIO.TEXTIO
(** OS modules *)

module OS_Path : OsPath.OS_PATH
(** Path operations compatible with SML OS.Path structure. *)
