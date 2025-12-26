(** The Basis Library - Standard ML Basis Library compatibility layer.

    This module provides an OCaml implementation of commonly-used Standard ML
    Basis Library modules, enabling compatibility with code ported from the
    original SML implementation of Twelf.

    The basis library wraps OCaml standard library functionality with SML-style
    interfaces, providing modules for arrays, vectors, lists, integers, characters,
    text I/O, and time operations.

    @author Asher Frost
*)

(** Include core prelude definitions including the {!type:Prelude.order} type. *)
include (module type of Prelude)

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
