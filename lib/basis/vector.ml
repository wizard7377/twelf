
open Prelude

module type VECTOR = sig
  type 'a t
  type 'a vector = 'a t
  val maxLen : int
  val fromList : 'a list -> 'a t
  val tabulate : int * (int -> 'a) -> 'a t
  val length : 'a t -> int
  val sub : 'a t -> int -> 'a
  val update : 'a t -> int -> 'a -> 'a t
  val concat : 'a t list -> 'a t
  val appi : (int * 'a -> unit) -> 'a t -> unit
  val app : ('a -> unit) -> 'a t -> unit
  val mapi : (int * 'a -> 'b) -> 'a t -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b
  val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b
  val foldl : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b
  val foldr : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b
  val findi : (int * 'a -> bool) -> 'a t -> (int * 'a) option
  val find : ('a -> bool) -> 'a t -> 'a option
  val exists : ('a -> bool) -> 'a t -> bool
  val all : ('a -> bool) -> 'a t -> bool
  val collate : ('a * 'a -> order) -> 'a t * 'a t -> order
end

module Vector : VECTOR = struct
    type 'a t = 'a array
    type 'a vector = 'a t
  let maxLen : int = assert false
  let fromList : 'a list -> 'a t = assert false
  let tabulate : int * (int -> 'a) -> 'a t = assert false
  let length : 'a t -> int = assert false
  let sub : 'a t -> int -> 'a = assert false
  let update : 'a t -> int -> 'a -> 'a t = assert false
  let concat : 'a t list -> 'a t = assert false
  let appi : (int * 'a -> unit) -> 'a t -> unit = assert false
  let app : ('a -> unit) -> 'a t -> unit = assert false
  let mapi : (int * 'a -> 'b) -> 'a t -> 'b t = assert false
  let map : ('a -> 'b) -> 'a t -> 'b t = assert false
  let foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b = assert false
  let foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b = assert false
  let foldl : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b = assert false
  let foldr : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b = assert false
  let findi : (int * 'a -> bool) -> 'a t -> (int * 'a) option = assert false
  let find : ('a -> bool) -> 'a t -> 'a option = assert false
  let exists : ('a -> bool) -> 'a t -> bool = assert false
  let all : ('a -> bool) -> 'a t -> bool = assert false
  let collate : ('a * 'a -> order) -> 'a t * 'a t -> order = assert false
end
