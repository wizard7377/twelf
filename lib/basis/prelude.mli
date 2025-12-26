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
type order

(** The [Less] ordering value.
    Indicates the first value is less than the second. *)
val less : order

(** The [Equal] ordering value.
    Indicates the two values are equal. *)
val equal : order

(** The [Greater] ordering value.
    Indicates the first value is greater than the second. *)
val greater : order

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

