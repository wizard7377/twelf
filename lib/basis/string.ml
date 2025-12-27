open Order

module type STRING = sig
  type string = Stdlib.String.t
  type char = Stdlib.Char.t

  val maxSize : int
  val size : string -> int
  val sub : string * int -> char
  val extract : string * int * int option -> string
  val substring : string * int * int -> string
  val ( ^ ) : string * string -> string
  val concat : string list -> string
  val concatWith : string -> string list -> string
  val str : char -> string
  val implode : char list -> string
  val explode : string -> char list
  val map : (char -> char) -> string -> string
  val translate : (char -> string) -> string -> string
  val tokens : (char -> bool) -> string -> string list
  val fields : (char -> bool) -> string -> string list
  val isPrefix : string -> string -> bool
  val isSubstring : string -> string -> bool
  val isSuffix : string -> string -> bool
  val compare : string * string -> order
  val collate : (char * char -> order) -> string * string -> order
  val ( < ) : string * string -> bool
  val ( <= ) : string * string -> bool
  val ( > ) : string * string -> bool
  val ( >= ) : string * string -> bool
end

module String : STRING = struct
  type string = Stdlib.String.t
  type char = Stdlib.Char.t

  let maxSize : int = assert false (* TODO *)
  let size : string -> int = assert false (* TODO *)
  let sub : string * int -> char = assert false (* TODO *)
  let extract : string * int * int option -> string = assert false (* TODO *)
  let substring : string * int * int -> string = assert false (* TODO *)
  let ( ^ ) : string * string -> string = assert false (* TODO *)
  let concat : string list -> string = assert false (* TODO *)
  let concatWith : string -> string list -> string = assert false (* TODO *)
  let str : char -> string = assert false (* TODO *)
  let implode : char list -> string = assert false (* TODO *)
  let explode : string -> char list = assert false (* TODO *)
  let map : (char -> char) -> string -> string = assert false (* TODO *)
  let translate : (char -> string) -> string -> string = assert false (* TODO *)
  let tokens : (char -> bool) -> string -> string list = assert false (* TODO *)
  let fields : (char -> bool) -> string -> string list = assert false (* TODO *)
  let isPrefix : string -> string -> bool = assert false (* TODO *)
  let isSubstring : string -> string -> bool = assert false (* TODO *)
  let isSuffix : string -> string -> bool = assert false (* TODO *)
  let compare : string * string -> order = assert false (* TODO *)

  let collate : (char * char -> order) -> string * string -> order =
    assert false (* TODO *)

  let ( < ) : string * string -> bool = assert false (* TODO *)
  let ( <= ) : string * string -> bool = assert false (* TODO *)
  let ( > ) : string * string -> bool = assert false (* TODO *)
  let ( >= ) : string * string -> bool = assert false (* TODO *)
end
