module type TABLE = sig
  type key

  (* parameter *)
  type 'a entry = key * 'a
  type 'a table

  val new_ : int -> 'a table

  (* size hint for_sml some implementations *)
  val insert : 'a table -> 'a entry -> unit

  (* insert entry, return shadowed entry if there is one *)
  val insertShadow : 'a table -> 'a entry -> 'a entry option
  val lookup : 'a table -> key -> 'a option
  val delete : 'a table -> key -> unit
  val clear : 'a table -> unit

  (* Apply function to all entries in unpredictable order *)
  val app : ('a entry -> unit) -> 'a table -> unit
end
