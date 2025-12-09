(* Sparse 1-Dimensional Arrays *)
(* Author: Roberto Virga *)

module SparseArray (IntTable : TABLE with type key = int)
  :> SPARSE_ARRAY =
struct

  type 'a array = {default : 'a, table : 'a IntTable.Table}

  let size = 29;

  let rec unsafeSub ({table, default}, i) =
        case (IntTable.lookup table i)
          of NONE => default
           | SOME(v) => v

  let rec unsafeUpdate ({table, default}, i, v) =
        IntTable.insert table (i, v)

  let rec array default =
        {default = default, table = IntTable.new size}

  let rec sub (array, i) =
        if (i >= 0)
        then unsafeSub (array, i)
        else raise General.Subscript

  let rec update (array, i, v) =
        if (i >= 0)
        then unsafeUpdate (array, i, v)
        else raise General.Subscript

  let rec extract (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then Vector.tabulate (len, (fun off -> unsafeSub (array, i+off)))
        else raise General.Subscript

  let rec copyVec {src, si, len, dst, di} =
        if (di >= 0)
        then
          VectorSlice.appi (fn (i, v) => unsafeUpdate (dst, i, v))
                           (VectorSlice.slice (src, si, len))
        else raise General.Subscript

  let rec app f (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then
          let
            let imax = i+len
            let rec app' i' =
                  if (i' < imax)
                  then
                    (
                      f(i', unsafeSub (array, i'));
                      app' (i'+1)
                    )
                  else ()
          in
            app' i
          end
        else raise General.Subscript

  let rec foldl f init (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then
          let
            let rec foldl' i' =
                  if (i' >= i)
                  then f(i', unsafeSub (array, i'), foldl' (i'-1))
                  else init
          in
            foldl' (i+len-1)
          end
        else raise General.Subscript

  let rec foldr f init (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then
          let
            let imax = i+len
            let rec foldr' i' =
                  if (i' < imax)
                  then f(i', unsafeSub (array, i'), foldr' (i'+1))
                  else init
          in
            foldr' i
          end
        else raise General.Subscript

  let rec modify f (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then
          let
            let imax = i+len
            let rec modify' i' =
                  if (i' < imax)
                  then
                    (
                      unsafeUpdate (array, i', f(i', unsafeSub (array, i')));
                      modify' (i'+1)
                    )
                  else ()
          in
            modify' i
          end
        else raise General.Subscript
end;; (* module SparseArray *)
