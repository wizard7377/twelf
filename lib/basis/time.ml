
module type TIME = sig
  type t

  exception Time

  val time : unit -> t
  val zeroTime : t
  val fromReal : float -> t
  val toReal : t -> float
  val toSeconds : t -> int
  val toMilliseconds : t -> int
  val toMicroseconds : t -> int
  val toNanoseconds : t -> int
  val fromSeconds : int -> t
  val fromMilliseconds : int -> t
  val fromMicroseconds : int -> t
  val fromNanoseconds : int -> t
  val ( + ) : t * t -> t
  val ( - ) : t * t -> t
  val compare : t * t -> int
  val ( < ) : t * t -> bool
  val ( <= ) : t * t -> bool
  val ( > ) : t * t -> bool
  val ( >= ) : t * t -> bool
  val now : unit -> t
  val fmt : int -> t -> string
  val toString : t -> string
  val fromString : string -> t option
end

module Time : TIME = struct
  type t = float

  exception Time

  let time : unit -> t = assert false
  let zeroTime : t = assert false
  let fromReal : float -> t = assert false
  let toReal : t -> float = assert false
  let toSeconds : t -> int = assert false
  let toMilliseconds : t -> int = assert false
  let toMicroseconds : t -> int = assert false
  let toNanoseconds : t -> int = assert false
  let fromSeconds : int -> t = assert false
  let fromMilliseconds : int -> t = assert false
  let fromMicroseconds : int -> t = assert false
  let fromNanoseconds : int -> t = assert false
  let ( + ) : t * t -> t = assert false
  let ( - ) : t * t -> t = assert false
  let compare : t * t -> int = assert false
  let ( < ) : t * t -> bool = assert false
  let ( <= ) : t * t -> bool = assert false
  let ( > ) : t * t -> bool = assert false
  let ( >= ) : t * t -> bool = assert false
  let now : unit -> t = assert false
  let fmt : int -> t -> string = assert false
  let toString : t -> string = assert false
  let fromString : string -> t option = assert false
end
