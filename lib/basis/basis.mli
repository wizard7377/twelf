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
