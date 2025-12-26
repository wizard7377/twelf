(** Word8Array module - SML Basis Library MONO_ARRAY signature for Word8 *)

open Order

module type WORD8_ARRAY = sig
  type elem = int  (* Word8 represented as int *)
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

module Word8Array : WORD8_ARRAY = struct
  type elem = int
  type array = (int, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t
  type vector = int list

  let maxLen = Sys.max_array_length

  let array (n, init) =
    if n < 0 || n > maxLen then
      raise (Invalid_argument "Word8Array.array")
    else
      let arr = Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout n in
      Bigarray.Array1.fill arr init;
      arr

  let fromList lst =
    let len = Stdlib.List.length lst in
    if len > maxLen then
      raise (Invalid_argument "Word8Array.fromList")
    else
      let arr = Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout len in
      Stdlib.List.iteri (fun i v -> Bigarray.Array1.set arr i v) lst;
      arr

  let tabulate (n, f) =
    if n < 0 || n > maxLen then
      raise (Invalid_argument "Word8Array.tabulate")
    else
      let arr = Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout n in
      for i = 0 to n - 1 do
        Bigarray.Array1.set arr i (f i)
      done;
      arr

  let length = Bigarray.Array1.dim

  let sub (arr, i) =
    if i < 0 || i >= Bigarray.Array1.dim arr then
      raise (Invalid_argument "Word8Array.sub")
    else
      Bigarray.Array1.get arr i

  let update (arr, i, v) =
    if i < 0 || i >= Bigarray.Array1.dim arr then
      raise (Invalid_argument "Word8Array.update")
    else
      Bigarray.Array1.set arr i v

  let vector arr =
    let len = Bigarray.Array1.dim arr in
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (Bigarray.Array1.get arr i :: acc)
    in
    loop (len - 1) []

  let copy ~src ~dst ~di =
    let src_len = Bigarray.Array1.dim src in
    let dst_len = Bigarray.Array1.dim dst in
    if di < 0 || di + src_len > dst_len then
      raise (Invalid_argument "Word8Array.copy")
    else
      for i = 0 to src_len - 1 do
        Bigarray.Array1.set dst (di + i) (Bigarray.Array1.get src i)
      done

  let copyVec ~src ~dst ~di =
    let src_len = Stdlib.List.length src in
    let dst_len = Bigarray.Array1.dim dst in
    if di < 0 || di + src_len > dst_len then
      raise (Invalid_argument "Word8Array.copyVec")
    else
      Stdlib.List.iteri (fun i v -> Bigarray.Array1.set dst (di + i) v) src

  let appi f arr =
    for i = 0 to Bigarray.Array1.dim arr - 1 do
      f (i, Bigarray.Array1.get arr i)
    done

  let app f arr =
    for i = 0 to Bigarray.Array1.dim arr - 1 do
      f (Bigarray.Array1.get arr i)
    done

  let modifyi f arr =
    for i = 0 to Bigarray.Array1.dim arr - 1 do
      Bigarray.Array1.set arr i (f (i, Bigarray.Array1.get arr i))
    done

  let modify f arr =
    for i = 0 to Bigarray.Array1.dim arr - 1 do
      Bigarray.Array1.set arr i (f (Bigarray.Array1.get arr i))
    done

  let foldli f init arr =
    let rec loop i acc =
      if i >= Bigarray.Array1.dim arr then acc
      else loop (i + 1) (f (i, Bigarray.Array1.get arr i, acc))
    in
    loop 0 init

  let foldri f init arr =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (i, Bigarray.Array1.get arr i, acc))
    in
    loop (Bigarray.Array1.dim arr - 1) init

  let foldl f init arr =
    let rec loop i acc =
      if i >= Bigarray.Array1.dim arr then acc
      else loop (i + 1) (f (Bigarray.Array1.get arr i, acc))
    in
    loop 0 init

  let foldr f init arr =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (Bigarray.Array1.get arr i, acc))
    in
    loop (Bigarray.Array1.dim arr - 1) init

  let findi pred arr =
    let rec loop i =
      if i >= Bigarray.Array1.dim arr then None
      else
        let elem = Bigarray.Array1.get arr i in
        if pred (i, elem) then Some (i, elem)
        else loop (i + 1)
    in
    loop 0

  let find pred arr =
    let rec loop i =
      if i >= Bigarray.Array1.dim arr then None
      else
        let elem = Bigarray.Array1.get arr i in
        if pred elem then Some elem
        else loop (i + 1)
    in
    loop 0

  let exists pred arr =
    let rec loop i =
      if i >= Bigarray.Array1.dim arr then false
      else if pred (Bigarray.Array1.get arr i) then true
      else loop (i + 1)
    in
    loop 0

  let all pred arr =
    let rec loop i =
      if i >= Bigarray.Array1.dim arr then true
      else if not (pred (Bigarray.Array1.get arr i)) then false
      else loop (i + 1)
    in
    loop 0

  let collate cmp (arr1, arr2) =
    let len1 = Bigarray.Array1.dim arr1 in
    let len2 = Bigarray.Array1.dim arr2 in
    let minlen = min len1 len2 in
    let rec loop i =
      if i >= minlen then
        if len1 < len2 then Less
        else if len1 > len2 then Greater
        else Equal
      else
        match cmp (Bigarray.Array1.get arr1 i, Bigarray.Array1.get arr2 i) with
        | Equal -> loop (i + 1)
        | ord -> ord
    in
    loop 0
end
