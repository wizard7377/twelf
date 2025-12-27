(** ArraySlice module - SML Basis Library ARRAY_SLICE signature *)

open Order
open Vector
module type ARRAY_SLICE = sig
  type 'a slice
  type 'a array
  type 'a vector = 'a Vector.t

  val length : 'a slice -> int
  val sub : 'a slice * int -> 'a
  val update : 'a slice * int * 'a -> unit

  val full : 'a array -> 'a slice
  val slice : 'a array * int * int option -> 'a slice
  val subslice : 'a slice * int * int option -> 'a slice

  val base : 'a slice -> 'a array * int * int
  val vector : 'a slice -> 'a vector
  val isEmpty : 'a slice -> bool
  val getItem : 'a slice -> ('a * 'a slice) option

  val appi : (int * 'a -> unit) -> 'a slice -> unit
  val app  : ('a -> unit) -> 'a slice -> unit
  val modifyi : (int * 'a -> 'a) -> 'a slice -> unit
  val modify  : ('a -> 'a) -> 'a slice -> unit
  val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val foldl  : ('a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val foldr  : ('a * 'b -> 'b) -> 'b -> 'a slice -> 'b
  val findi : (int * 'a -> bool) -> 'a slice -> (int * 'a) option
  val find  : ('a -> bool) -> 'a slice -> 'a option
  val exists : ('a -> bool) -> 'a slice -> bool
  val all : ('a -> bool) -> 'a slice -> bool
  val collate : ('a * 'a -> order) -> 'a slice * 'a slice -> order
end

module ArraySlice : ARRAY_SLICE = struct
  (* A slice is represented as (array, start, length) *)
  type 'a slice = 'a array * int * int
  type 'a array = 'a Stdlib.Array.t
  type 'a vector = 'a Vector.t

  let length (_, _, len) = len

  let sub ((arr, start, len), i) =
    if i < 0 || i >= len then
      raise (Invalid_argument "ArraySlice.sub")
    else
      Stdlib.Array.get arr (start + i)

  let update ((arr, start, len), i, x) =
    if i < 0 || i >= len then
      raise (Invalid_argument "ArraySlice.update")
    else
      Stdlib.Array.set arr (start + i) x

  let full arr =
    (arr, 0, Stdlib.Array.length arr)

  let slice (arr, start, len_opt) =
    let alen = Stdlib.Array.length arr in
    if start < 0 || start > alen then
      raise (Invalid_argument "ArraySlice.slice")
    else
      match len_opt with
      | None -> (arr, start, alen - start)
      | Some len ->
          if len < 0 || start + len > alen then
            raise (Invalid_argument "ArraySlice.slice")
          else
            (arr, start, len)

  let subslice ((arr, start, len), i, len_opt) =
    if i < 0 || i > len then
      raise (Invalid_argument "ArraySlice.subslice")
    else
      match len_opt with
      | None -> (arr, start + i, len - i)
      | Some n ->
          if n < 0 || i + n > len then
            raise (Invalid_argument "ArraySlice.subslice")
          else
            (arr, start + i, n)

  let base sl = sl

  let vector (arr, start, len) =
    (* Convert slice to vector *)
    let rec loop i acc =
      if i < 0 then Vector.fromList acc
      else loop (i - 1) (Stdlib.Array.get arr (start + i) :: acc)
    in
    loop (len - 1) []

  let isEmpty (_, _, len) = len = 0

  let getItem (arr, start, len) =
    if len = 0 then None
    else Some (Stdlib.Array.get arr start, (arr, start + 1, len - 1))

  let appi f (arr, start, len) =
    for i = 0 to len - 1 do
      f (i, Stdlib.Array.get arr (start + i))
    done

  let app f (arr, start, len) =
    for i = 0 to len - 1 do
      f (Stdlib.Array.get arr (start + i))
    done

  let modifyi f (arr, start, len) =
    for i = 0 to len - 1 do
      let idx = start + i in
      Stdlib.Array.set arr idx (f (i, Stdlib.Array.get arr idx))
    done

  let modify f (arr, start, len) =
    for i = 0 to len - 1 do
      let idx = start + i in
      Stdlib.Array.set arr idx (f (Stdlib.Array.get arr idx))
    done

  let foldli f init (arr, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (i, Stdlib.Array.get arr (start + i), acc))
    in
    loop 0 init

  let foldri f init (arr, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (i, Stdlib.Array.get arr (start + i), acc))
    in
    loop (len - 1) init

  let foldl f init (arr, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (Stdlib.Array.get arr (start + i), acc))
    in
    loop 0 init

  let foldr f init (arr, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (Stdlib.Array.get arr (start + i), acc))
    in
    loop (len - 1) init

  let findi pred (arr, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Stdlib.Array.get arr (start + i) in
        if pred (i, elem) then Some (i, elem)
        else loop (i + 1)
    in
    loop 0

  let find pred (arr, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Stdlib.Array.get arr (start + i) in
        if pred elem then Some elem
        else loop (i + 1)
    in
    loop 0

  let exists pred (arr, start, len) =
    let rec loop i =
      if i >= len then false
      else if pred (Stdlib.Array.get arr (start + i)) then true
      else loop (i + 1)
    in
    loop 0

  let all pred (arr, start, len) =
    let rec loop i =
      if i >= len then true
      else if not (pred (Stdlib.Array.get arr (start + i))) then false
      else loop (i + 1)
    in
    loop 0

  let collate cmp ((arr1, start1, len1), (arr2, start2, len2)) =
    let minlen = min len1 len2 in
    let rec loop i =
      if i >= minlen then
        if len1 < len2 then Less
        else if len1 > len2 then Greater
        else Equal
      else
        match cmp (Stdlib.Array.get arr1 (start1 + i),
                   Stdlib.Array.get arr2 (start2 + i)) with
        | Equal -> loop (i + 1)
        | ord -> ord
    in
    loop 0
end
