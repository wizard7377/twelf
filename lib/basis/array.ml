include Vector ;;
open Order ;;
module type ARRAY = sig
    type 'a array 
    type 'a vector = 'a Vector.t
    val maxLen : int
    val array : int * 'a -> 'a array
    val fromList : 'a list -> 'a array
    val tabulate : int * (int -> 'a) -> 'a array
    val length : 'a array -> int
    val sub : 'a array * int -> 'a
    val update : 'a array * int * 'a -> unit
    val vector : 'a array -> 'a vector
    val copy    : src: 'a array -> dst: 'a array -> di : int -> unit
    val copyVec : src : 'a vector -> dst : 'a array -> di : int -> unit
    val appi : (int * 'a -> unit) -> 'a array -> unit
    val app  : ('a -> unit) -> 'a array -> unit
    val modifyi : (int * 'a -> 'a) -> 'a array -> unit
    val modify  : ('a -> 'a) -> 'a array -> unit
    val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b
    val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b
    val foldl  : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b
    val foldr  : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b
    val findi : (int * 'a -> bool)
                -> 'a array -> (int * 'a) option
    val find  : ('a -> bool) -> 'a array -> 'a option
    val exists : ('a -> bool) -> 'a array -> bool
    val all : ('a -> bool) -> 'a array -> bool
    val collate : ('a * 'a -> order) -> 'a array * 'a array -> order
end ;;

module Array : ARRAY = struct 
    type 'a array = 'a (* TODO *)
    type 'a vector = 'a Vector.vector (* TODO *)
    let maxLen : int = assert false (* TODO *)
    let array : int * 'a -> 'a array = assert false (* TODO *)
    let fromList : 'a list -> 'a array = assert false (* TODO *)
    let tabulate : int * (int -> 'a) -> 'a array = assert false (* TODO *)
    let length : 'a array -> int = assert false (* TODO *)
    let sub : 'a array * int -> 'a = assert false (* TODO *)
    let update : 'a array * int * 'a -> unit = assert false (* TODO *)
    let vector : 'a array -> 'a vector = assert false (* TODO *)
    let copy    : src: 'a array -> dst: 'a array -> di : int -> unit = assert false (* TODO *)
    let copyVec : src : 'a vector -> dst : 'a array -> di : int -> unit = assert false (* TODO *)
    let appi : (int * 'a -> unit) -> 'a array -> unit = assert false (* TODO *)
    let app  : ('a -> unit) -> 'a array -> unit= assert false (* TODO *)
    let modifyi : (int * 'a -> 'a) -> 'a array -> unit = assert false (* TODO *)
    let modify  : ('a -> 'a) -> 'a array -> unit = assert false (* TODO *)
    let foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b = assert false (* TODO *)
    let foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b = assert false (* TODO *)
    let foldl  : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b = assert false (* TODO *)
    let foldr  : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b = assert false (* TODO *)
    let findi : (int * 'a -> bool) -> 'a array -> (int * 'a) option = assert false (* TODO *)
    let find  : ('a -> bool) -> 'a array -> 'a option = assert false (* TODO *)
    let exists : ('a -> bool) -> 'a array -> bool = assert false (* TODO *)
    let all : ('a -> bool) -> 'a array -> bool = assert false (* TODO *)
    let collate : ('a * 'a -> order) -> 'a array * 'a array -> order = assert false (* TODO *)
end
