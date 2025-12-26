(** CharArraySlice module - SML Basis Library MONO_ARRAY_SLICE signature for char *)

open Order

module type MONO_ARRAY_SLICE = sig
  type elem = char
  type array = CharArray.array
  type slice
  type vector = CharArray.vector
  type vector_slice

  val length : slice -> int
  val sub : slice * int -> elem
  val update : slice * int * elem -> unit

  val full : array -> slice
  val slice : array * int * int option -> slice
  val subslice : slice * int * int option -> slice

  val base : slice -> array * int * int
  val vector : slice -> vector
  val copy : src : slice -> dst : array -> di : int -> unit
  val copyVec : src : vector_slice -> dst : array -> di : int -> unit

  val isEmpty : slice -> bool
  val getItem : slice -> (elem * slice) option

  val appi : (int * elem -> unit) -> slice -> unit
  val app  : (elem -> unit) -> slice -> unit
  val modifyi : (int * elem -> elem) -> slice -> unit
  val modify  : (elem -> elem) -> slice -> unit
  val foldli : (int * elem * 'b -> 'b) -> 'b -> slice -> 'b
  val foldri : (int * elem * 'b -> 'b) -> 'b -> slice -> 'b
  val foldl  : (elem * 'b -> 'b) -> 'b -> slice -> 'b
  val foldr  : (elem * 'b -> 'b) -> 'b -> slice -> 'b
  val findi : (int * elem -> bool) -> slice -> (int * elem) option
  val find  : (elem -> bool) -> slice -> elem option
  val exists : (elem -> bool) -> slice -> bool
  val all : (elem -> bool) -> slice -> bool
  val collate : (elem * elem -> order) -> slice * slice -> order
end

module CharArraySlice : MONO_ARRAY_SLICE = struct
  type elem = char
  type array = Bytes.t
  type slice = Bytes.t * int * int
  type vector = string
  type vector_slice = string * int * int

  let length (_, _, len) = len

  let sub ((arr, start, len), i) =
    if i < 0 || i >= len then
      raise (Invalid_argument "CharArraySlice.sub")
    else
      Bytes.get arr (start + i)

  let update ((arr, start, len), i, c) =
    if i < 0 || i >= len then
      raise (Invalid_argument "CharArraySlice.update")
    else
      Bytes.set arr (start + i) c

  let full arr =
    (arr, 0, Bytes.length arr)

  let slice (arr, start, len_opt) =
    let alen = Bytes.length arr in
    if start < 0 || start > alen then
      raise (Invalid_argument "CharArraySlice.slice")
    else
      match len_opt with
      | None -> (arr, start, alen - start)
      | Some len ->
          if len < 0 || start + len > alen then
            raise (Invalid_argument "CharArraySlice.slice")
          else
            (arr, start, len)

  let subslice ((arr, start, len), i, len_opt) =
    if i < 0 || i > len then
      raise (Invalid_argument "CharArraySlice.subslice")
    else
      match len_opt with
      | None -> (arr, start + i, len - i)
      | Some n ->
          if n < 0 || i + n > len then
            raise (Invalid_argument "CharArraySlice.subslice")
          else
            (arr, start + i, n)

  let base sl = sl

  let vector (arr, start, len) =
    Bytes.sub_string arr start len

  let copy ~src:(arr, start, len) ~dst ~di =
    let dst_len = Bytes.length dst in
    if di < 0 || di + len > dst_len then
      raise (Invalid_argument "CharArraySlice.copy")
    else
      Bytes.blit arr start dst di len

  let copyVec ~src:(str, start, len) ~dst ~di =
    let dst_len = Bytes.length dst in
    if di < 0 || di + len > dst_len then
      raise (Invalid_argument "CharArraySlice.copyVec")
    else
      Bytes.blit_string str start dst di len

  let isEmpty (_, _, len) = len = 0

  let getItem (arr, start, len) =
    if len = 0 then None
    else Some (Bytes.get arr start, (arr, start + 1, len - 1))

  let appi f (arr, start, len) =
    for i = 0 to len - 1 do
      f (i, Bytes.get arr (start + i))
    done

  let app f (arr, start, len) =
    for i = 0 to len - 1 do
      f (Bytes.get arr (start + i))
    done

  let modifyi f (arr, start, len) =
    for i = 0 to len - 1 do
      let idx = start + i in
      Bytes.set arr idx (f (i, Bytes.get arr idx))
    done

  let modify f (arr, start, len) =
    for i = 0 to len - 1 do
      let idx = start + i in
      Bytes.set arr idx (f (Bytes.get arr idx))
    done

  let foldli f init (arr, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (i, Bytes.get arr (start + i), acc))
    in
    loop 0 init

  let foldri f init (arr, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (i, Bytes.get arr (start + i), acc))
    in
    loop (len - 1) init

  let foldl f init (arr, start, len) =
    let rec loop i acc =
      if i >= len then acc
      else loop (i + 1) (f (Bytes.get arr (start + i), acc))
    in
    loop 0 init

  let foldr f init (arr, start, len) =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (Bytes.get arr (start + i), acc))
    in
    loop (len - 1) init

  let findi pred (arr, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Bytes.get arr (start + i) in
        if pred (i, elem) then Some (i, elem)
        else loop (i + 1)
    in
    loop 0

  let find pred (arr, start, len) =
    let rec loop i =
      if i >= len then None
      else
        let elem = Bytes.get arr (start + i) in
        if pred elem then Some elem
        else loop (i + 1)
    in
    loop 0

  let exists pred (arr, start, len) =
    let rec loop i =
      if i >= len then false
      else if pred (Bytes.get arr (start + i)) then true
      else loop (i + 1)
    in
    loop 0

  let all pred (arr, start, len) =
    let rec loop i =
      if i >= len then true
      else if not (pred (Bytes.get arr (start + i))) then false
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
        match cmp (Bytes.get arr1 (start1 + i), Bytes.get arr2 (start2 + i)) with
        | Equal -> loop (i + 1)
        | ord -> ord
    in
    loop 0
end
