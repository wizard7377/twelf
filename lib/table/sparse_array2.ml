(* Sparse 2-Dimensional Arrays *)
(* Author: Roberto Virga *)

module SparseArray2 (IntTable : TABLE with type key = int)
  :> SPARSE_ARRAY2 =
struct

  type 'a array = {default : 'a, table : 'a IntTable.Table}

  type 'a region = {base : 'a array, row : int, col : int, nrows : int, ncols : int}

  type traversal = RowMajor | ColMajor

  let size = 29;

  let rec fromInt (code) =
        let
          let rec fromInt' r =
                let
                  let code' = (r + 1)*(r + 2) div 2
                in
                  if(code < code')
                  then
                    let
                      let diff = code'-code-1
                    in
                      (diff, r-diff)
                    end
                  else
                    fromInt' (r+1)
                end
        in
          fromInt' 0
        end

  let rec toInt (m, n) =
        let
          let sum = m + n
        in
          sum*(sum + 1) div 2 + n
        end

  let rec unsafeSub ({table, default}, i, j) =
        case (IntTable.lookup table (toInt (i, j)))
          of NONE => default
           | SOME(v) => v

  let rec unsafeUpdate ({table, default}, i, j, v) =
        IntTable.insert table (toInt (i, j), v)

  let rec checkRegion {base, row, col, nrows, ncols} =
        (row >= 0) andalso (col >= 0) andalso (nrows >= 0) andalso (ncols >= 0)

  let rec array default =
        {default = default, table = IntTable.new size}

  let rec sub (array, i, j) =
        if (i >= 0) andalso (j >= 0)
        then unsafeSub (array, i, j)
        else raise General.Subscript

  let rec update (array, i, j, v) =
        if (i >= 0) andalso (j >= 0)
        then unsafeUpdate (array, i, j, v)
        else raise General.Subscript

  let rec row (array, i, (j, len)) =
        if (i >= 0) andalso (j >= 0) andalso (len >= 0)
        then Vector.tabulate (len, (fun off -> unsafeSub (array, i, j+off)))
        else raise General.Subscript

  let rec column (array, j, (i, len)) =
        if (j >= 0) andalso (i >= 0) andalso (len >= 0)
        then Vector.tabulate (len, (fun off -> unsafeSub (array, i+off, j)))
        else raise General.Subscript

  let rec app traversal f (region as {base, row, col, nrows, ncols}) =
        if checkRegion region
        then
          let
            let rmax = row+nrows
            let cmax = col+ncols
            let rec appR (row', col') =
                   if (row' < rmax)
                   then
                     if (col' < cmax)
                     then
                       (
                         f(row', col', unsafeSub(base, row', col'));
                         appR (row', col'+1)
                       )
                     else
                       appR (row'+1, col)
                   else ()
            let rec appC (row', col') =
                   if (col' < cmax)
                   then
                     if (row' < rmax)
                     then
                       (
                         f(row', col', unsafeSub(base, row', col'));
                         appC (row'+1, col')
                       )
                     else
                       appC (row, col'+1)
                   else ()
          in
            case traversal
              of RowMajor => appR (row, col)
               | ColMajor => appC (row, col)
          end
        else raise General.Subscript

  let rec fold traversal f init (region as {base, row, col, nrows, ncols}) =
        if checkRegion region
        then
          let
            let rmax = row+nrows
            let cmax = col+ncols
            let rec foldR (row', col') =
                   if (row' < rmax)
                   then
                     if (col' < cmax)
                     then
                       f(row', col', unsafeSub (base, row', col'),
                         foldR (row', col'+1))
                     else
                       foldR (row'+1, col)
                   else
                     init
            let rec foldC (row', col') =
                   if (col' < cmax)
                   then
                     if (row' < rmax)
                     then
                       f(row', col', unsafeSub (base, row', col'),
                         foldC (row'+1, col'))
                     else
                       foldC (row, col'+1)
                   else
                     init
          in
            case traversal
              of RowMajor => foldR (row, col)
               | ColMajor => foldC (row, col)
          end
        else raise General.Subscript

  let rec modify traversal f (region as {base, row, col, nrows, ncols}) =
        if checkRegion region
        then
          let
            let rmax = row+nrows
            let cmax = col+ncols
            let rec modifyR (row', col') =
                   if (row' < rmax)
                   then
                     if (col' < cmax)
                     then
                       (
                         unsafeUpdate (base, row', col',
                                       f(row', col',
                                         unsafeSub(base, row', col')));
                         modifyR (row', col'+1)
                       )
                     else
                       modifyR (row'+1, col)
                   else ()
            let rec modifyC (row', col') =
                   if (col' < cmax)
                   then
                     if (row' < rmax)
                     then
                       (
                         unsafeUpdate (base, row', col',
                                       f(row', col',
                                         unsafeSub(base, row', col')));
                         modifyC (row'+1, col')
                       )
                     else
                       modifyC (row, col'+1)
                   else ()
          in
            case traversal
              of RowMajor => modifyR (row, col)
               | ColMajor => modifyC (row, col)
          end
        else raise General.Subscript

end;; (* module SparseArray2 *)
