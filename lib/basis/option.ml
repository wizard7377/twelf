(** Option module - SML Basis Library OPTION signature *)

module type OPTION = sig
  (* OCaml's option is built-in: type 'a option = None | Some of 'a *)

  exception Option

  val getOpt : 'a option -> 'a -> 'a
  val isSome : 'a option -> bool
  val valOf : 'a option -> 'a
  val filter : ('a -> bool) -> 'a -> 'a option
  val join : 'a option option -> 'a option
  val app : ('a -> unit) -> 'a option -> unit
  val map : ('a -> 'b) -> 'a option -> 'b option
  val mapPartial : ('a -> 'b option) -> 'a option -> 'b option
  val compose : ('a -> 'b) -> ('c -> 'a option) -> 'c -> 'b option
  val composePartial : ('a -> 'b option) -> ('c -> 'a option) -> 'c -> 'b option
end

module Option : OPTION = struct
  (* In OCaml, option is a built-in type: type 'a option = None | Some of 'a *)
  (* We use OCaml's built-in option type for SML compatibility *)

  exception Option

  let getOpt opt default =
    match opt with
    | None -> default
    | Some v -> v

  let isSome opt =
    match opt with
    | None -> false
    | Some _ -> true

  let valOf opt =
    match opt with
    | None -> raise Option
    | Some v -> v

  let filter pred x =
    if pred x then Some x else None

  let join opt =
    match opt with
    | None -> None
    | Some inner_opt -> inner_opt

  let app f opt =
    match opt with
    | None -> ()
    | Some v -> f v

  let map f opt =
    match opt with
    | None -> None
    | Some v -> Some (f v)

  let mapPartial f opt =
    match opt with
    | None -> None
    | Some v -> f v

  let compose f g x =
    match g x with
    | None -> None
    | Some v -> Some (f v)

  let composePartial f g x =
    match g x with
    | None -> None
    | Some v -> f v
end
