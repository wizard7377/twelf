open Order

module type LIST = sig
  type 'a t = 'a list

  val null : 'a t -> bool
  val length : 'a t -> int
  val ( @ ) : 'a t * 'a t -> 'a t
  val hd : 'a t -> 'a
  val tl : 'a t -> 'a t
  val last : 'a t -> 'a
  val getItem : 'a t -> ('a * 'a t) option
  val nth : 'a t * int -> 'a
  val take : 'a t * int -> 'a t
  val drop : 'a t * int -> 'a t
  val rev : 'a t -> 'a t
  val concat : 'a t t -> 'a t
  val revAppend : 'a t * 'a t -> 'a t
  val app : ('a -> unit) -> 'a t -> unit
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapPartial : ('a -> 'b option) -> 'a t -> 'b t
  val find : ('a -> bool) -> 'a t -> 'a option
  val filter : ('a -> bool) -> 'a t -> 'a t
  val partition : ('a -> bool) -> 'a t -> 'a t * 'a t
  val foldl : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b
  val foldr : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b
  val exists : ('a -> bool) -> 'a t -> bool
  val all : ('a -> bool) -> 'a t -> bool
  val tabulate : int * (int -> 'a) -> 'a t
  val collate : ('a * 'a -> order) -> 'a t * 'a t -> order
end

module List : LIST = struct
  type 'a t = 'a list

  let null : 'a t -> bool = assert false (* TODO *)
  let length : 'a t -> int = assert false (* TODO *)
  let ( @ ) : 'a t * 'a t -> 'a t = assert false (* TODO *)
  let hd : 'a t -> 'a = assert false (* TODO *)
  let tl : 'a t -> 'a t = assert false (* TODO *)
  let last : 'a t -> 'a = assert false (* TODO *)
  let getItem : 'a t -> ('a * 'a t) option = assert false (* TODO *)
  let nth : 'a t * int -> 'a = assert false (* TODO *)
  let take : 'a t * int -> 'a t = assert false (* TODO *)
  let drop : 'a t * int -> 'a t = assert false (* TODO *)
  let rev : 'a t -> 'a t = assert false (* TODO *)
  let concat : 'a t t -> 'a t = assert false (* TODO *)
  let revAppend : 'a t * 'a t -> 'a t = assert false (* TODO *)
  let app : ('a -> unit) -> 'a t -> unit = assert false (* TODO *)
  let map : ('a -> 'b) -> 'a t -> 'b t = assert false (* TODO *)
  let mapPartial : ('a -> 'b option) -> 'a t -> 'b t = assert false (* TODO *)
  let find : ('a -> bool) -> 'a t -> 'a option = assert false (* TODO *)
  let filter : ('a -> bool) -> 'a t -> 'a t = assert false (* TODO *)
  let partition : ('a -> bool) -> 'a t -> 'a t * 'a t = assert false (* TODO *)
  let foldl : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b = assert false (* TODO *)
  let foldr : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b = assert false (* TODO *)
  let exists : ('a -> bool) -> 'a t -> bool = assert false (* TODO *)
  let all : ('a -> bool) -> 'a t -> bool = assert false (* TODO *)
  let tabulate : int * (int -> 'a) -> 'a t = assert false (* TODO *)

  let collate : ('a * 'a -> order) -> 'a t * 'a t -> order =
    assert false (* TODO *)
end
