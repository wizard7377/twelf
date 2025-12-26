(** CharVector module - SML Basis Library MONO_VECTOR signature for char *)

open Order

module type MONO_VECTOR = sig
  type elem = char
  type vector = string

  val maxLen : int
  val fromList : elem list -> vector
  val tabulate : int * (int -> elem) -> vector
  val length : vector -> int
  val sub : vector * int -> elem
  val update : vector * int * elem -> vector
  val concat : vector list -> vector
  val appi : (int * elem -> unit) -> vector -> unit
  val app  : (elem -> unit) -> vector -> unit
  val mapi : (int * elem -> elem) -> vector -> vector
  val map  : (elem -> elem) -> vector -> vector
  val foldli : (int * elem * 'b -> 'b) -> 'b -> vector -> 'b
  val foldri : (int * elem * 'b -> 'b) -> 'b -> vector -> 'b
  val foldl  : (elem * 'b -> 'b) -> 'b -> vector -> 'b
  val foldr  : (elem * 'b -> 'b) -> 'b -> vector -> 'b
  val findi : (int * elem -> bool) -> vector -> (int * elem) option
  val find  : (elem -> bool) -> vector -> elem option
  val exists : (elem -> bool) -> vector -> bool
  val all : (elem -> bool) -> vector -> bool
  val collate : (elem * elem -> order) -> vector * vector -> order
end

module CharVector : MONO_VECTOR = struct
  type elem = char
  type vector = string

  let maxLen = Sys.max_string_length

  let fromList lst =
    let len = Stdlib.List.length lst in
    if len > maxLen then
      raise (Invalid_argument "CharVector.fromList")
    else
      let buf = Buffer.create len in
      Stdlib.List.iter (Buffer.add_char buf) lst;
      Buffer.contents buf

  let tabulate (n, f) =
    if n < 0 || n > maxLen then
      raise (Invalid_argument "CharVector.tabulate")
    else
      String.init n f

  let length = String.length

  let sub (vec, i) =
    if i < 0 || i >= String.length vec then
      raise (Invalid_argument "CharVector.sub")
    else
      String.get vec i

  let update (vec, i, c) =
    if i < 0 || i >= String.length vec then
      raise (Invalid_argument "CharVector.update")
    else
      let bytes = Bytes.of_string vec in
      Bytes.set bytes i c;
      Bytes.to_string bytes

  let concat = String.concat ""

  let appi f vec =
    for i = 0 to String.length vec - 1 do
      f (i, String.get vec i)
    done

  let app f vec =
    for i = 0 to String.length vec - 1 do
      f (String.get vec i)
    done

  let mapi f vec =
    String.mapi (fun i c -> f (i, c)) vec

  let map f vec =
    String.map f vec

  let foldli f init vec =
    let rec loop i acc =
      if i >= String.length vec then acc
      else loop (i + 1) (f (i, String.get vec i, acc))
    in
    loop 0 init

  let foldri f init vec =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (i, String.get vec i, acc))
    in
    loop (String.length vec - 1) init

  let foldl f init vec =
    let rec loop i acc =
      if i >= String.length vec then acc
      else loop (i + 1) (f (String.get vec i, acc))
    in
    loop 0 init

  let foldr f init vec =
    let rec loop i acc =
      if i < 0 then acc
      else loop (i - 1) (f (String.get vec i, acc))
    in
    loop (String.length vec - 1) init

  let findi pred vec =
    let rec loop i =
      if i >= String.length vec then None
      else
        let elem = String.get vec i in
        if pred (i, elem) then Some (i, elem)
        else loop (i + 1)
    in
    loop 0

  let find pred vec =
    let rec loop i =
      if i >= String.length vec then None
      else
        let elem = String.get vec i in
        if pred elem then Some elem
        else loop (i + 1)
    in
    loop 0

  let exists pred vec =
    let rec loop i =
      if i >= String.length vec then false
      else if pred (String.get vec i) then true
      else loop (i + 1)
    in
    loop 0

  let all pred vec =
    let rec loop i =
      if i >= String.length vec then true
      else if not (pred (String.get vec i)) then false
      else loop (i + 1)
    in
    loop 0

  let collate cmp (vec1, vec2) =
    let len1 = String.length vec1 in
    let len2 = String.length vec2 in
    let minlen = min len1 len2 in
    let rec loop i =
      if i >= minlen then
        if len1 < len2 then Less
        else if len1 > len2 then Greater
        else Equal
      else
        match cmp (String.get vec1 i, String.get vec2 i) with
        | Equal -> loop (i + 1)
        | ord -> ord
    in
    loop 0
end
