(** VectorSlice module - SML Basis Library VECTOR_SLICE signature *)

open Order
open Vector

module type VECTOR_SLICE = sig
  type 'a slice
  type 'a vector = 'a array

  val length : 'a slice -> int
  val sub : 'a slice * int -> 'a
  val full : 'a vector -> 'a slice
  val slice : 'a vector * int * int option -> 'a slice
  val subslice : 'a slice * int * int option -> 'a slice
  val base : 'a slice -> 'a vector * int * int
  val vector : 'a slice -> 'a vector
  val concat : 'a slice list -> 'a vector
  val isEmpty : 'a slice -> bool
  val getItem : 'a slice -> ('a * 'a slice) option
  val appi : (int * 'a -> unit) -> 'a slice -> unit
  val app : ('a -> unit) -> 'a slice -> unit
  val mapi : (int * 'a -> 'b) -> 'a slice -> 'b vector
  val map : ('a -> 'b) -> 'a slice -> 'b vector
  val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val foldl : ('a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val foldr : ('a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val findi : (int * 'a -> bool) -> 'a slice -> (int * 'a) option
  val find : ('a -> bool) -> 'a slice -> 'a option
  val exists : ('a -> bool) -> 'a slice -> bool
  val all : ('a -> bool) -> 'a slice -> bool
  val collate : ('a * 'a -> order) -> 'a slice * 'a slice -> order
end

module VectorSlice : VECTOR_SLICE = struct
  type 'a vector = 'a array

  (* A slice is represented as (vector, start, length) *)
  type 'a slice = 'a vector * int * int

  let length (_, _, len) = len

  let sub ((vec, start, len), i) =
    if i < 0 || i >= len then raise (Invalid_argument "VectorSlice.sub")
    else Stdlib.Array.get vec (start + i)

  let full vec = (vec, 0, Stdlib.Array.length vec)

  let slice (vec, start, len_opt) =
    let vlen = Stdlib.Array.length vec in
    if start < 0 || start > vlen then
      raise (Invalid_argument "VectorSlice.slice")
    else
      match len_opt with
      | None -> (vec, start, vlen - start)
      | Some len ->
          if len < 0 || start + len > vlen then
            raise (Invalid_argument "VectorSlice.slice")
          else (vec, start, len)

  let subslice ((vec, start, len), i, len_opt) =
    if i < 0 || i > len then raise (Invalid_argument "VectorSlice.subslice")
    else
      match len_opt with
      | None -> (vec, start + i, len - i)
      | Some n ->
          if n < 0 || i + n > len then
            raise (Invalid_argument "VectorSlice.subslice")
          else (vec, start + i, n)

  let base sl = sl

  let vector (vec, start, len) =
    (* Extract the slice as a new vector (array) *)
    Stdlib.Array.sub vec start len

  let concat slices =
    (* Concatenate multiple slices into a single vector *)
    let vectors = Stdlib.List.map vector slices in
    Stdlib.Array.concat vectors

  let isEmpty (_, _, len) = len = 0

  let getItem (vec, start, len) =
    if len = 0 then None
    else Some (Stdlib.Array.get vec start, (vec, start + 1, len - 1))

  let appi f (vec, start, len) =
    for i = 0 to len - 1 do
      f (i, Stdlib.Array.get vec (start + i))
    done

  let app f (vec, start, len) =
    for i = 0 to len - 1 do
      f (Stdlib.Array.get vec (start + i))
    done

  let mapi f (vec, start, len) =
    Stdlib.Array.init len (fun i -> f (i, Stdlib.Array.get vec (start + i)))

  let map f (vec, start, len) =
    Stdlib.Array.init len (fun i -> f (Stdlib.Array.get vec (start + i)))

  let foldli f init (vec, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (i, Stdlib.Array.get vec (start + i), acc))
    in
    loop 0 init

  let foldri f init (vec, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (i, Stdlib.Array.get vec (start + i), acc))
    in
    loop (len - 1) init

  let foldl f init (vec, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (Stdlib.Array.get vec (start + i), acc))
    in
    loop 0 init

  let foldr f init (vec, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (Stdlib.Array.get vec (start + i), acc))
    in
    loop (len - 1) init

  let findi pred (vec, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Stdlib.Array.get vec (start + i) in
        if pred (i, elem) then Some (i, elem) else loop (i + 1)
    in
    loop 0

  let find pred (vec, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Stdlib.Array.get vec (start + i) in
        if pred elem then Some elem else loop (i + 1)
    in
    loop 0

  let exists pred (vec, start, len) =
    let rec loop i =
      if i >= len then false
      else if pred (Stdlib.Array.get vec (start + i)) then true
      else loop (i + 1)
    in
    loop 0

  let all pred (vec, start, len) =
    let rec loop i =
      if i >= len then true
      else if not (pred (Stdlib.Array.get vec (start + i))) then false
      else loop (i + 1)
    in
    loop 0

  let collate cmp ((vec1, start1, len1), (vec2, start2, len2)) =
    let minlen = min len1 len2 in
    let rec loop i =
      if i >= minlen then
        if len1 < len2 then Less else if len1 > len2 then Greater else Equal
      else
        match
          cmp
            ( Stdlib.Array.get vec1 (start1 + i),
              Stdlib.Array.get vec2 (start2 + i) )
        with
        | Equal -> loop (i + 1)
        | ord -> ord
    in
    loop 0
end
