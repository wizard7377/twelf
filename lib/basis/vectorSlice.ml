(** VectorSlice module - SML Basis Library VECTOR_SLICE signature *)

open Order

module type VECTOR_SLICE = sig
  type 'a slice
  type 'a vector = 'a Vector.t

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
  val app  : ('a -> unit) -> 'a slice -> unit
  val mapi : (int * 'a -> 'b) -> 'a slice -> 'b vector
  val map  : ('a -> 'b) -> 'a slice -> 'b vector
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

module VectorSlice : VECTOR_SLICE = struct
  (* A slice is represented as (vector, start, length) *)
  type 'a slice = 'a list * int * int  (* vector is a list in our implementation *)
  type 'a vector = 'a list

  let length (_, _, len) = len

  let sub ((vec, start, len), i) =
    if i < 0 || i >= len then
      raise (Invalid_argument "VectorSlice.sub")
    else
      Stdlib.List.nth vec (start + i)

  let full vec =
    (vec, 0, Stdlib.List.length vec)

  let slice (vec, start, len_opt) =
    let vlen = Stdlib.List.length vec in
    if start < 0 || start > vlen then
      raise (Invalid_argument "VectorSlice.slice")
    else
      match len_opt with
      | None -> (vec, start, vlen - start)
      | Some len ->
          if len < 0 || start + len > vlen then
            raise (Invalid_argument "VectorSlice.slice")
          else
            (vec, start, len)

  let subslice ((vec, start, len), i, len_opt) =
    if i < 0 || i > len then
      raise (Invalid_argument "VectorSlice.subslice")
    else
      match len_opt with
      | None -> (vec, start + i, len - i)
      | Some n ->
          if n < 0 || i + n > len then
            raise (Invalid_argument "VectorSlice.subslice")
          else
            (vec, start + i, n)

  let base sl = sl

  let vector (vec, start, len) =
    (* Extract the slice as a new vector *)
    let rec drop n lst =
      if n <= 0 then lst
      else match lst with
      | [] -> []
      | _::xs -> drop (n - 1) xs
    in
    let rec take n lst =
      if n <= 0 then []
      else match lst with
      | [] -> []
      | x::xs -> x :: take (n - 1) xs
    in
    take len (drop start vec)

  let concat slices =
    (* Concatenate multiple slices into a single vector *)
    Stdlib.List.flatten (Stdlib.List.map vector slices)

  let isEmpty (_, _, len) = len = 0

  let getItem (vec, start, len) =
    if len = 0 then None
    else Some (Stdlib.List.nth vec start, (vec, start + 1, len - 1))

  let appi f (vec, start, len) =
    for i = 0 to len - 1 do
      f (i, Stdlib.List.nth vec (start + i))
    done

  let app f (vec, start, len) =
    for i = 0 to len - 1 do
      f (Stdlib.List.nth vec (start + i))
    done

  let mapi f (vec, start, len) =
    let rec loop i acc =
      if i >= len then Stdlib.List.rev acc
      else loop (i + 1) (f (i, Stdlib.List.nth vec (start + i)) :: acc)
    in
    loop 0 []

  let map f (vec, start, len) =
    let rec loop i acc =
      if i >= len then Stdlib.List.rev acc
      else loop (i + 1) (f (Stdlib.List.nth vec (start + i)) :: acc)
    in
    loop 0 []

  let foldli f init (vec, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (i, Stdlib.List.nth vec (start + i), acc))
    in
    loop 0 init

  let foldri f init (vec, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (i, Stdlib.List.nth vec (start + i), acc))
    in
    loop (len - 1) init

  let foldl f init (vec, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (Stdlib.List.nth vec (start + i), acc))
    in
    loop 0 init

  let foldr f init (vec, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (Stdlib.List.nth vec (start + i), acc))
    in
    loop (len - 1) init

  let findi pred (vec, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Stdlib.List.nth vec (start + i) in
        if pred (i, elem) then Some (i, elem)
        else loop (i + 1)
    in
    loop 0

  let find pred (vec, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Stdlib.List.nth vec (start + i) in
        if pred elem then Some elem
        else loop (i + 1)
    in
    loop 0

  let exists pred (vec, start, len) =
    let rec loop i =
      if i >= len then false
      else if pred (Stdlib.List.nth vec (start + i)) then true
      else loop (i + 1)
    in
    loop 0

  let all pred (vec, start, len) =
    let rec loop i =
      if i >= len then true
      else if not (pred (Stdlib.List.nth vec (start + i))) then false
      else loop (i + 1)
    in
    loop 0

  let collate cmp ((vec1, start1, len1), (vec2, start2, len2)) =
    let minlen = min len1 len2 in
    let rec loop i =
      if i >= minlen then
        if len1 < len2 then Less
        else if len1 > len2 then Greater
        else Equal
      else
        match cmp (Stdlib.List.nth vec1 (start1 + i),
                   Stdlib.List.nth vec2 (start2 + i)) with
        | Equal -> loop (i + 1)
        | ord -> ord
    in
    loop 0
end
