(** CharArray module - SML Basis Library MONO_ARRAY signature for char *)

open Order

module type MONO_ARRAY = sig
  type elem = char
  type array
  type vector

  val maxLen : int
  val array : int * elem -> array
  val fromList : elem list -> array
  val tabulate : int * (int -> elem) -> array
  val length : array -> int
  val sub : array * int -> elem
  val update : array * int * elem -> unit
  val vector : array -> vector
  val copy : src : array -> dst : array -> di : int -> unit
  val copyVec : src : vector -> dst : array -> di : int -> unit
  val appi : (int * elem -> unit) -> array -> unit
  val app  : (elem -> unit) -> array -> unit
  val modifyi : (int * elem -> elem) -> array -> unit
  val modify  : (elem -> elem) -> array -> unit
  val foldli : (int * elem * 'b -> 'b) -> 'b -> array -> 'b
  val foldri : (int * elem * 'b -> 'b) -> 'b -> array -> 'b
  val foldl  : (elem * 'b -> 'b) -> 'b -> array -> 'b
  val foldr  : (elem * 'b -> 'b) -> 'b -> array -> 'b
  val findi : (int * elem -> bool) -> array -> (int * elem) option
  val find  : (elem -> bool) -> array -> elem option
  val exists : (elem -> bool) -> array -> bool
  val all : (elem -> bool) -> array -> bool
  val collate : (elem * elem -> order) -> array * array -> order
end

module CharArray : MONO_ARRAY = struct
  type elem = char
  type array = Bytes.t
  type vector = string

  let maxLen = Sys.max_string_length

  let array (n, c) =
    if n < 0 || n > maxLen then
      raise (Invalid_argument "CharArray.array")
    else
      Bytes.make n c

  let fromList lst =
    let len = Stdlib.List.length lst in
    if len > maxLen then
      raise (Invalid_argument "CharArray.fromList")
    else
      let arr = Bytes.create len in
      Stdlib.List.iteri (fun i c -> Bytes.set arr i c) lst;
      arr

  let tabulate (n, f) =
    if n < 0 || n > maxLen then
      raise (Invalid_argument "CharArray.tabulate")
    else
      Bytes.init n f

  let length = Bytes.length

  let sub (arr, i) =
    if i < 0 || i >= Bytes.length arr then
      raise (Invalid_argument "CharArray.sub")
    else
      Bytes.get arr i

  let update (arr, i, c) =
    if i < 0 || i >= Bytes.length arr then
      raise (Invalid_argument "CharArray.update")
    else
      Bytes.set arr i c

  let vector arr =
    Bytes.to_string arr

  let copy ~src ~dst ~di =
    let src_len = Bytes.length src in
    let dst_len = Bytes.length dst in
    if di < 0 || di + src_len > dst_len then
      raise (Invalid_argument "CharArray.copy")
    else
      Bytes.blit src 0 dst di src_len

  let copyVec ~src ~dst ~di =
    let src_len = String.length src in
    let dst_len = Bytes.length dst in
    if di < 0 || di + src_len > dst_len then
      raise (Invalid_argument "CharArray.copyVec")
    else
      Bytes.blit_string src 0 dst di src_len

  let appi f arr =
    for i = 0 to Bytes.length arr - 1 do
      f (i, Bytes.get arr i)
    done

  let app f arr =
    for i = 0 to Bytes.length arr - 1 do
      f (Bytes.get arr i)
    done

  let modifyi f arr =
    for i = 0 to Bytes.length arr - 1 do
      Bytes.set arr i (f (i, Bytes.get arr i))
    done

  let modify f arr =
    for i = 0 to Bytes.length arr - 1 do
      Bytes.set arr i (f (Bytes.get arr i))
    done

  let foldli f init arr =
    let rec loop i acc =
      if i >= Bytes.length arr then acc
      else loop (i + 1) (f (i, Bytes.get arr i, acc))
    in
    loop 0 init

  let foldri f init arr =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (i, Bytes.get arr i, acc))
    in
    loop (Bytes.length arr - 1) init

  let foldl f init arr =
    let rec loop i acc =
      if i >= Bytes.length arr then acc
      else loop (i + 1) (f (Bytes.get arr i, acc))
    in
    loop 0 init

  let foldr f init arr =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (Bytes.get arr i, acc))
    in
    loop (Bytes.length arr - 1) init

  let findi pred arr =
    let rec loop i =
      if i >= Bytes.length arr then None
      else
        let elem = Bytes.get arr i in
        if pred (i, elem) then Some (i, elem)
        else loop (i + 1)
    in
    loop 0

  let find pred arr =
    let rec loop i =
      if i >= Bytes.length arr then None
      else
        let elem = Bytes.get arr i in
        if pred elem then Some elem
        else loop (i + 1)
    in
    loop 0

  let exists pred arr =
    let rec loop i =
      if i >= Bytes.length arr then false
      else if pred (Bytes.get arr i) then true
      else loop (i + 1)
    in
    loop 0

  let all pred arr =
    let rec loop i =
      if i >= Bytes.length arr then true
      else if not (pred (Bytes.get arr i)) then false
      else loop (i + 1)
    in
    loop 0

  let collate cmp (arr1, arr2) =
    let len1 = Bytes.length arr1 in
    let len2 = Bytes.length arr2 in
    let minlen = min len1 len2 in
    let rec loop i =
      if i >= minlen then
        if len1 < len2 then Less
        else if len1 > len2 then Greater
        else Equal
      else
        match cmp (Bytes.get arr1 i, Bytes.get arr2 i) with
        | Equal -> loop (i + 1)
        | ord -> ord
    in
    loop 0
end
