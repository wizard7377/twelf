open Basis

(* Sparse 1-Dimensional Arrays *)

(* Author: Roberto Virga *)

open Table_sig

module type SPARSE_ARRAY = sig
  type 'a array

  val array : 'a -> 'a array
  val sub : 'a array * int -> 'a
  val update : 'a array * int * 'a -> unit
  val extract : 'a array * int * int -> 'a Vector.t

  type 'a copy_vec_args = {
    src : 'a Vector.t;
    si : int;
    len : int option;
    dst : 'a array;
    di : int;
  }

  val copyVec : 'a copy_vec_args -> unit
  val app : (int * 'a -> unit) -> 'a array * int * int -> unit
  val foldl : (int * 'a * 'b -> 'b) -> 'b -> 'a array * int * int -> 'b
  val foldr : (int * 'a * 'b -> 'b) -> 'b -> 'a array * int * int -> 'b
  val modify : (int * 'a -> 'a) -> 'a array * int * int -> unit
end

(* signature SPARSE_ARRAY *)
(* Sparse 1-Dimensional Arrays *)

(* Author: Roberto Virga *)

module SparseArray (IntTable : TABLE with type key = int) : SPARSE_ARRAY =
struct
  type 'a array = { default : 'a; table : 'a IntTable.table }

  type 'a copy_vec_args = {
    src : 'a Vector.t;
    si : int;
    len : int option;
    dst : 'a array;
    di : int;
  }

  let size = 29

  let rec unsafeSub ({ table; default }, i) =
    match IntTable.lookup table i with None -> default | Some v -> v

  let rec unsafeUpdate ({ table; default }, i, v) = IntTable.insert table (i, v)
  let rec array default = { default; table = IntTable.new_ size }

  let rec sub (array, i) =
    if i >= 0 then unsafeSub (array, i) else raise General.Subscript

  let rec update (array, i, v) =
    if i >= 0 then unsafeUpdate (array, i, v) else raise General.Subscript

  let rec extract (array, i, len) =
    if i >= 0 && len >= 0 then
      Vector.tabulate (len, fun off -> unsafeSub (array, i + off))
    else raise General.Subscript

  let rec copyVec { src; si; len; dst; di } =
    if di >= 0 then
      let actualLen =
        match len with Some l -> l | None -> Vector.length src - si
      in
      let rec loop i =
        if i < actualLen then begin
          unsafeUpdate (dst, di + i, Vector.sub src (si + i));
          loop (i + 1)
        end
      in
      loop 0
    else raise General.Subscript

  let rec app f (array, i, len) =
    if i >= 0 && len >= 0 then
      let imax = i + len in
      let rec app' i' =
        if i' < imax then (
          f (i', unsafeSub (array, i'));
          app' (i' + 1))
        else ()
      in
      app' i
    else raise General.Subscript

  let rec foldl f init (array, i, len) =
    if i >= 0 && len >= 0 then
      let rec foldl' i' =
        if i' >= i then f (i', unsafeSub (array, i'), foldl' (i' - 1)) else init
      in
      foldl' (i + len - 1)
    else raise General.Subscript

  let rec foldr f init (array, i, len) =
    if i >= 0 && len >= 0 then
      let imax = i + len in
      let rec foldr' i' =
        if i' < imax then f (i', unsafeSub (array, i'), foldr' (i' + 1))
        else init
      in
      foldr' i
    else raise General.Subscript

  let rec modify f (array, i, len) =
    if i >= 0 && len >= 0 then
      let imax = i + len in
      let rec modify' i' =
        if i' < imax then (
          unsafeUpdate (array, i', f (i', unsafeSub (array, i')));
          modify' (i' + 1))
        else ()
      in
      modify' i
    else raise General.Subscript
end

(* structure SparseArray *)
