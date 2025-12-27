(** CharVectorSlice module - SML Basis Library MONO_VECTOR_SLICE signature for
    char *)

open Order

module type MONO_VECTOR_SLICE = sig
  type elem = char
  type vector = string
  type slice

  val length : slice -> int
  val sub : slice * int -> elem
  val full : vector -> slice
  val slice : vector -> int -> int option -> slice
  val subslice : slice * int * int option -> slice
  val base : slice -> vector * int * int
  val vector : slice -> vector
  val concat : slice list -> vector
  val isEmpty : slice -> bool
  val getItem : slice -> (elem * slice) option
  val appi : (int * elem -> unit) -> slice -> unit
  val app : (elem -> unit) -> slice -> unit
  val mapi : (int * elem -> elem) -> slice -> vector
  val map : (elem -> elem) -> slice -> vector
  val foldli : (int * elem * 'b -> 'b) -> 'b -> slice -> 'b
  val foldri : (int * elem * 'b -> 'b) -> 'b -> slice -> 'b
  val foldl : (elem * 'b -> 'b) -> 'b -> slice -> 'b
  val foldr : (elem * 'b -> 'b) -> 'b -> slice -> 'b
  val findi : (int * elem -> bool) -> slice -> (int * elem) option
  val find : (elem -> bool) -> slice -> elem option
  val exists : (elem -> bool) -> slice -> bool
  val all : (elem -> bool) -> slice -> bool
  val collate : (elem * elem -> order) -> slice * slice -> order
end

module CharVectorSlice : MONO_VECTOR_SLICE = struct
  type elem = char
  type vector = string
  type slice = string * int * int

  let length (_, _, len) = len

  let sub ((vec, start, len), i) =
    if i < 0 || i >= len then raise (Invalid_argument "CharVectorSlice.sub")
    else Stdlib.String.get vec (start + i)

  let full vec = (vec, 0, Stdlib.String.length vec)

  let slice vec start len_opt =
    let vlen = Stdlib.String.length vec in
    if start < 0 || start > vlen then
      raise (Invalid_argument "CharVectorSlice.slice")
    else
      match len_opt with
      | None -> (vec, start, vlen - start)
      | Some len ->
          if len < 0 || start + len > vlen then
            raise (Invalid_argument "CharVectorSlice.slice")
          else (vec, start, len)

  let subslice ((vec, start, len), i, len_opt) =
    if i < 0 || i > len then raise (Invalid_argument "CharVectorSlice.subslice")
    else
      match len_opt with
      | None -> (vec, start + i, len - i)
      | Some n ->
          if n < 0 || i + n > len then
            raise (Invalid_argument "CharVectorSlice.subslice")
          else (vec, start + i, n)

  let base sl = sl
  let vector (vec, start, len) = Stdlib.String.sub vec start len

  let concat slices =
    let strs = Stdlib.List.map vector slices in
    Stdlib.String.concat "" strs

  let isEmpty (_, _, len) = len = 0

  let getItem (vec, start, len) =
    if len = 0 then None
    else Some (Stdlib.String.get vec start, (vec, start + 1, len - 1))

  let appi f (vec, start, len) =
    for i = 0 to len - 1 do
      f (i, Stdlib.String.get vec (start + i))
    done

  let app f (vec, start, len) =
    for i = 0 to len - 1 do
      f (Stdlib.String.get vec (start + i))
    done

  let mapi f (vec, start, len) =
    Stdlib.String.init len (fun i -> f (i, Stdlib.String.get vec (start + i)))

  let map f (vec, start, len) =
    Stdlib.String.init len (fun i -> f (Stdlib.String.get vec (start + i)))

  let foldli f init (vec, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (i, Stdlib.String.get vec (start + i), acc))
    in
    loop 0 init

  let foldri f init (vec, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (i, Stdlib.String.get vec (start + i), acc))
    in
    loop (len - 1) init

  let foldl f init (vec, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (Stdlib.String.get vec (start + i), acc))
    in
    loop 0 init

  let foldr f init (vec, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (Stdlib.String.get vec (start + i), acc))
    in
    loop (len - 1) init

  let findi pred (vec, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Stdlib.String.get vec (start + i) in
        if pred (i, elem) then Some (i, elem) else loop (i + 1)
    in
    loop 0

  let find pred (vec, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Stdlib.String.get vec (start + i) in
        if pred elem then Some elem else loop (i + 1)
    in
    loop 0

  let exists pred (vec, start, len) =
    let rec loop i =
      if i >= len then false
      else if pred (Stdlib.String.get vec (start + i)) then true
      else loop (i + 1)
    in
    loop 0

  let all pred (vec, start, len) =
    let rec loop i =
      if i >= len then true
      else if not (pred (Stdlib.String.get vec (start + i))) then false
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
            ( Stdlib.String.get vec1 (start1 + i),
              Stdlib.String.get vec2 (start2 + i) )
        with
        | Equal -> loop (i + 1)
        | ord -> ord
    in
    loop 0
end
