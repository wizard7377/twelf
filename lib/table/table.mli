(* Hash Tables *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga *)

(* This provides a common interface to hash tables *)
(* red/black trees and similar data structures *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature TABLE =
sig
  type key (* parameter *)
  type 'a entry = key * 'a

  type 'a table
  val new : int -> 'a table		(* size hint for some implementations *)

  val insert : 'a table -> 'a entry -> unit
  (* insert entry, return shadowed entry if there is one *)
  val insertShadow : 'a table -> 'a entry -> ('a entry) option
  val lookup : 'a table -> key -> 'a option
  val delete : 'a table -> key -> unit
  val clear : 'a table -> unit

  (* Apply function to all entries in unpredictable order *)
  val app : ('a entry -> unit) -> 'a table -> unit

end (* GEN END SIGNATURE DECLARATION *);  (* signature TABLE *)
