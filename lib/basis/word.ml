type order = Less | Equal | Greater
module type WORD = sig 
  type word
  val wordSize : int

  val toInt  : word -> int
  val toIntX : word -> int
  val fromInt : int -> word

  val andb : word * word -> word
  val orb  : word * word -> word
  val xorb : word * word -> word
  val notb : word -> word
  val ( << ) : word * word -> word
  val ( >> ) : word * word -> word
  val ( ~>> ) : word * word -> word

  val ( + ) : word * word -> word
  val ( - ) : word * word -> word
  val ( * ) : word * word -> word
  val div : word * word -> word
  val ( mod ) : word * word -> word

  val compare : word * word -> order
  val ( < )  : word * word -> bool
  val ( <= ) : word * word -> bool
  val ( > )  : word * word -> bool
  val ( >= ) : word * word -> bool

  val ( ~- ) : word -> word
  val min : word * word -> word
  val max : word * word -> word
  val fromString : string -> word option 
end 

(* FIXME Get a word sized word type *)
module Word8 : (WORD with type word = int) = struct
  type word = int
  let wordSize : int = 8

  let toInt  : word -> int = assert false (* TODO *)
  let toIntX : word -> int = assert false (* TODO *)
  let fromInt : int -> word = assert false (* TODO *)
  let andb : word * word -> word = assert false (* TODO *)
  let orb  : word * word -> word = assert false (* TODO *)
  let xorb : word * word -> word = assert false (* TODO *)
  let notb : word -> word = assert false (* TODO *)
  let ( << ) : word * word -> word = assert false (* TODO *)
  let ( >> ) : word * word -> word = assert false (* TODO *)
  let ( ~>> ) : word * word -> word = assert false (* TODO *)

  let ( + ) : word * word -> word = assert false (* TODO *)
  let ( - ) : word * word -> word = assert false (* TODO *)
  let ( * ) : word * word -> word = assert false (* TODO *)
  let div : word * word -> word = assert false (* TODO *)
  let ( mod ) : word * word -> word = assert false (* TODO *)

  let compare : word * word -> order = assert false (* TODO *)
  let ( < )  : word * word -> bool = assert false (* TODO *)
  let ( <= ) : word * word -> bool = assert false (* TODO *)
  let ( > )  : word * word -> bool = assert false (* TODO *)
  let ( >= ) : word * word -> bool = assert false (* TODO *)
  let ( ~- ) : word -> word = assert false (* TODO *)
  let min : word * word -> word = assert false (* TODO *)
  let max : word * word -> word = assert false (* TODO *)
  let fromString : string -> word option = assert false (* TODO  *)
end

module Word32 : (WORD with type word = int) = struct
  type word = int
  let wordSize : int = 32

  let toInt  : word -> int = assert false (* TODO *)
  let toIntX : word -> int = assert false (* TODO *)
  let fromInt : int -> word = assert false (* TODO *)
  let andb : word * word -> word = assert false (* TODO *)
  let orb  : word * word -> word = assert false (* TODO *)
  let xorb : word * word -> word = assert false (* TODO *)
  let notb : word -> word = assert false (* TODO *)
  let ( << ) : word * word -> word = assert false (* TODO *)
  let ( >> ) : word * word -> word = assert false (* TODO *)
  let ( ~>> ) : word * word -> word = assert false (* TODO *)

  let ( + ) : word * word -> word = assert false (* TODO *)
  let ( - ) : word * word -> word = assert false (* TODO *)
  let ( * ) : word * word -> word = assert false (* TODO *)
  let div : word * word -> word = assert false (* TODO *)
  let ( mod ) : word * word -> word = assert false (* TODO *)

  let compare : word * word -> order = assert false (* TODO *)
  let ( < )  : word * word -> bool = assert false (* TODO *)
  let ( <= ) : word * word -> bool = assert false (* TODO *)
  let ( > )  : word * word -> bool = assert false (* TODO *)
  let ( >= ) : word * word -> bool = assert false (* TODO *)
  let ( ~- ) : word -> word = assert false (* TODO *)
  let min : word * word -> word = assert false (* TODO *)
  let max : word * word -> word = assert false (* TODO *)
  let fromString : string -> word option = assert false (* TODO  *)
end
