(** Word8Vector module - SML Basis Library MONO_VECTOR signature for Word8 *)

(* For simplicity, we use a bytes representation for Word8Vector *)
module type WORD8_VECTOR = sig
  type elem = int
  type vector = bytes

  val maxLen : int
  val fromList : elem list -> vector
  val tabulate : int -> (int -> elem) -> vector
  val length : vector -> int
  val sub : vector -> int -> elem
  val concat : vector list -> vector
  val appi : (int * elem -> unit) -> vector -> unit
  val app  : (elem -> unit) -> vector -> unit
  val foldli : (int * elem * 'b -> 'b) -> 'b -> vector -> 'b
  val foldl  : (elem * 'b -> 'b) -> 'b -> vector -> 'b
  val findi : (int * elem -> bool) -> vector -> (int * elem) option
  val find  : (elem -> bool) -> vector -> elem option
end

module Word8Vector : WORD8_VECTOR = struct
  type elem = int
  type vector = bytes

  let maxLen = Sys.max_string_length

  let fromList lst =
    let len = Stdlib.List.length lst in
    let vec = Bytes.create len in
    Stdlib.List.iteri (fun i v -> Bytes.set vec i (Stdlib.Char.chr v)) lst;
    vec

  let tabulate n f =
    Bytes.init n (fun i -> Stdlib.Char.chr (f i))

  let length = Bytes.length

  let sub vec i = Stdlib.Char.code (Bytes.get vec i)

  let concat vecs = Bytes.concat Bytes.empty vecs

  let appi f vec =
    for i = 0 to Bytes.length vec - 1 do
      f (i, Stdlib.Char.code (Bytes.get vec i))
    done

  let app f vec =
    for i = 0 to Bytes.length vec - 1 do
      f (Stdlib.Char.code (Bytes.get vec i))
    done

  let foldli f init vec =
    let rec loop i acc =
      if i >= Bytes.length vec then acc
      else loop (i + 1) (f (i, Stdlib.Char.code (Bytes.get vec i), acc))
    in
    loop 0 init

  let foldl f init vec =
    let rec loop i acc =
      if i >= Bytes.length vec then acc
      else loop (i + 1) (f (Stdlib.Char.code (Bytes.get vec i), acc))
    in
    loop 0 init

  let findi pred vec =
    let rec loop i =
      if i >= Bytes.length vec then None
      else
        let elem = Stdlib.Char.code (Bytes.get vec i) in
        if pred (i, elem) then Some (i, elem)
        else loop (i + 1)
    in
    loop 0

  let find pred vec =
    let rec loop i =
      if i >= Bytes.length vec then None
      else
        let elem = Stdlib.Char.code (Bytes.get vec i) in
        if pred elem then Some elem
        else loop (i + 1)
    in
    loop 0
end
