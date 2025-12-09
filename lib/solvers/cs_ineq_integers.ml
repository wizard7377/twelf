(* Solver for linear inequations, based on branch & bound *)
(* Author: Roberto Virga *)

module CSIneqIntegers (Integers : INTEGERS)
   (Rationals : RATIONALS)
                          sharing Rationals.Integers = Integers
                          (*! (IntSyn : INTSYN) !*)
                        (Trail : TRAIL)
                        (Unify : UNIFY)
                        (*! sharing Unify.IntSyn = IntSyn !*)
                        module SparseArray  : SPARSE_ARRAY
                        (SparseArray2 : SPARSE_ARRAY2)
                        (*! (CSManager : CS_MANAGER) !*)
                        (*! sharing CSManager.IntSyn = IntSyn !*)
                        (CSEqIntegers : CS_EQ_INTEGERS)
                          sharing CSEqIntegers.Integers = Integers
                          (*! sharing CSEqIntegers.IntSyn = IntSyn !*)
                          (*! sharing CSEqIntegers.CSManager = CSManager !*)
                        (Compat : COMPAT) =
struct
  (*! module CSManager = CSManager !*)

  local
    open IntSyn
    open Rationals
    open CSEqIntegers

    module CSM = CSManager
    module FX = CSM.Fixity
    module MS = ModeSyn (* CSM.ModeSyn *)

    module Array  = SparseArray
    module Array2 = SparseArray2

    (* useful integer values *)
    let zero_int = Integers.fromInt(0)
    let one_int  = Integers.fromInt(1)

    (* solver ID of this solver *)
    let myID = ref ~1 : cid ref

   (* constant IDs of the declared type constants *)
    let geqID  = ref ~1 : cid ref

    (* constructors for the declared types *)
    let rec geq (U, V) = Root (Const (!geqID), App (U, App (V, Nil)))

    (* specialized constructors for the declared types *)
    let rec geq0 (U) = geq (U, constant (zero_int))

    (* constant IDs of the declared object constants *)
    let geqAddID = ref ~1 : cid ref

    (* constructors for the declared objects *)
    let rec geqAdd (U1, U2, V, W) =
          Root (Const (!geqAddID), App (U1, App (U2, App (V,  App (W, Nil)))))

    (* constant declaration for the proof object d>=0 *)
    let rec geqNConDec (d) = ConDec (Integers.toString (d) ^ ">=" ^ Integers.toString (zero_int),
                                 NONE, 0, Normal, geq0 (constant (d)), Type)

    (* foreign constant for the proof object d>=0 *)
    let rec geqNExp (d) = Root (FgnConst (!myID, geqNConDec (d)), Nil)

    (* parsing proof objects d>=0 *)
    let rec parseGeqN string =
          let
            let suffix   = (">=" ^ (toString (zero)))
            let stringLen  = String.size string
            let suffixLen = String.size suffix
            let numLen  = Int.-(stringLen, suffixLen)
          in
            if Int.>(stringLen, suffixLen)
              andalso (String.substring (string, numLen, suffixLen) = suffix)
            then
              (case Integers.fromString (String.substring (string, 0, numLen))
                 of SOME(d) => if Integers.>=(d, zero_int)
                               then SOME(geqNConDec (d))
                               else NONE
                  | NONE => NONE)
            else
              NONE
          end

    type position =                               (* position of a tableau entry       *)
      Row of int
    | Col of int

    type owner =                                  (* owner of an entry:                *)
      Var of IntSyn.dctx * Mon                        (*   - monomial                      *)
    | Exp of IntSyn.dctx * sum                        (*   - sum                           *)

    type Restriction =                            (* Restriction: (proof object)       *)
      Restr of IntSyn.dctx * IntSyn.exp               (*   Restr (G, U)                    *)

    type label =
           {owner : owner,                            (* owner of the row/column (if any)  *)
            tag   : int ref,                          (* tag: used to keep track of the    *)
                                                      (* position of a tableau entry       *)
            restr : Restriction option ref,           (* restriction (if any)              *)
            dead  : bool ref}                         (* has the row/column already been   *)
                                                      (* solved?                           *)

    type Operation =                              (* Undoable operations:              *)
      Insert of position                              (* insert a new row/column           *)
    | Pivot of int * int                              (* pivot on (i, j)                   *)
    | Kill of position                                (* mark the given position solved    *)
    | Restrict of position                            (* restrict the given position       *)
    | UpdateOwner of position * owner * int ref       (* change the owner                  *)

    type tableau =                                    (* Tableau:                          *)
           {rlabels : label Array.array,              (* row labels                        *)
            clabels : label Array.array,              (* column labels                     *)
            consts : number Array.array,              (* constant terms                    *)
            coeffs : number Array2.array,             (* variables coefficients            *)
            nrows : int ref, ncols : int ref,         (* dimensions                        *)
            trail : Operation Trail.trail}            (* undo mechanism                    *)

    exception MyFgnCnstrRep of int ref                (* FgnCnstr representation *)

    exception Error

    (* Representational invariants:
         rlabels[i] = vacuous
         clabels[j] = vacuous
         const[i] = zero
         coeff[i,j] = zero
       for i >= !nrows or j > !ncols, where "vacuous" is the vacuous label:
          #owner(vacuous) = Exp (Null, sum (zero, nil))
          #restr(vacuous) = ref NONE
          #dead(vacuous) = ref true
    *)

    (* little random generation routine taken from Paulson '91 *)
    local
      let a = 16807.0 and m = 2147483647.0
      let seed = ref 1999.0
    in
      let rec rand (min, size) =
        let
          let rec nextrand ()=
                let
                  let t = Real.*(a, !seed)
                in
                  (
                    seed := Real.-(t, Real.*(m, Real.fromInt(Real.floor(t/m))));
                    Real.-(!seed, 1.0) / Real.-(m, 1.0)
                  )
                end
        in
          Int.+(min, Real.floor(Real.*(nextrand(), Real.fromInt(size))))
        end
    end

    (* create a new (empty) tableau *)
    let tableau =
          let
            let l = {owner = Exp (Null, sum(zero_int, nil)), tag = ref 0,
                     restr = ref NONE, dead = ref true}
          in
            {rlabels = Array.array (l), clabels = Array.array (l),
             consts = Array.array (zero), coeffs = Array2.array (zero),
             nrows = ref 0, ncols = ref 0, trail = Trail.trail ()} : tableau
          end

    (* i-th tableau row label *)
    let rec rlabel (i) =
          Array.sub (#rlabels(tableau), i)

    (* j-th tableau column label *)
    let rec clabel (j) =
          Array.sub (#clabels(tableau), j)

    (* i-th tableau constant term *)
    let rec const (i) =
          Array.sub (#consts(tableau), i)

    (* coefficient in row i, column j *)
    let rec coeff (i, j) =
          Array2.sub (#coeffs(tableau), i, j)

    (* number of rows *)
    let rec nRows () = !(#nrows(tableau))

    (* number of columns *)
    let rec nCols () = !(#ncols(tableau))

    (* increase the number of rows, and return the index of the last row *)
    let rec incrNRows () =
          let
            let old = nRows ()
          in
            (#nrows(tableau) := Int.+(old, 1); old)
          end

    (* increase the number of columns, and return the index of the last column *)
    let rec incrNCols () =
          let
            let old = nCols ()
          in
            (#ncols(tableau) := Int.+(old, 1); old)
          end

    (* decrease the number of rows *)
    let rec decrNRows () =
          #nrows(tableau) := Int.-(nRows(), 1)

    (* decrease the number of columns *)
    let rec decrNCols () =
          #ncols(tableau) := Int.-(nCols(), 1)

    (* increase by the given amount the element i of the array *)
    let rec incrArray (array, i, value) =
          Array.update (array, i, Array.sub (array, i) + value)

    (* increase by the given amount the element (i, j) of the array *)
    let rec incrArray2 (array, i, j, value) =
          Array2.update (array, i, j, Array2.sub (array, i, j) + value)

    (* increase by f(j') all the elements (i, j'), with j <= j' < j+len *)
    let rec incrArray2Row (array, i, (j, len), f) =
          Compat.Vector.mapi
            (fn (j, value) => Array2.update (array, i, j, value + f(j)))
            (Array2.row (array, i, (j, len)))

    (* increase by f(i') all the elements (i', j), with i <= i' < i+len *)
    let rec incrArray2Col (array, j, (i, len), f) =
          Compat.Vector.mapi
            (fn (i, value) => Array2.update (array, i, j, value + f(i)))
            (Array2.column (array, j, (i, len)))

    (* set the given row to zero *)
    let rec clearArray2Row (array, i, (j, len)) =
          Compat.Vector.mapi
            (fn (j, value) => Array2.update (array, i, j, zero))
            (Array2.row (array, i, (j, len)))

    (* set the given column to zero *)
    let rec clearArray2Col (array, j, (i, len)) =
          Compat.Vector.mapi
            (fn (i, value) => Array2.update (array, i, j, zero))
            (Array2.column (array, j, (i, len)))

    (* return the label at the given position (row or column) *)
    let rec label = function (Row(i)) -> rlabel (i)
      | (Col(j)) -> clabel (j)

    (* return the restriction on the given label *)
    let rec restriction (l : label) = !(#restr(l))

    (* is the given label is restricted? *)
    let rec restricted (l : label) =
          (case (restriction (l))
             of SOME _ => true
              | NONE => false)

    (* return true iff the given label has been solved *)
    let rec dead (l : label) = !(#dead(l))

    (* set the ownership of the given position *)
    let rec setOwnership (pos, owner, tag) =
          let
            let old = label(pos)
            let new = {owner = owner,
                       tag = tag,
                       restr = ref (restriction (old)),
                       dead = ref (dead (old))}
          in
            (case pos
               of Row(i) =>
                    Array.update (#rlabels(tableau), i, new)
                | Col(j) =>
                    Array.update (#clabels(tableau), j, new))
          end

    (* return the context of a owner *)
    let rec ownerContext = function (Var (G, mon)) -> G
      | (Exp (G, sum)) -> G

    (* return the owner as a sum *)
    let rec ownerSum = function (Var (G, mon)) -> sum(zero_int, [mon])
      | (Exp (G, sum)) -> sum

    (* debugging code - REMOVE *)
    let rec displayPos = function (Row(row)) -> 
          print ("row " ^ Int.toString(row) ^ "\n")
      | (Col(col)) -> 
          print ("column " ^ Int.toString(col) ^ "\n")

    (* debugging code - REMOVE *)
    let rec displaySum = function (sum(m, Mon(n, _) :: monL)) -> 
          (
            print (Integers.toString n);
            print " ? + ";
            displaySum (sum(m, monL))
          )
      | (sum(m, nil)) -> 
          (
            print (Integers.toString m);
            print " >= 0\n"
          )

    (* debugging code - REMOVE *)
    let rec display () =
          let
            let rec printLabel (col, l : label) =
                  (
                    print "\t";
                    (case (#owner(l)) of Var _ => print "V" | Exp _ => print "E");
                    if restricted (l) then print ">" else print "*";
                    if dead (l) then print "#" else print ""
                  )
            let rec printRow (row, l : label) =
                  let
                    let rec printCol (col, d : number) =
                          (
                            print "\t";
                            print (toString d)
                          )
                    let vec = Array2.row (#coeffs(tableau), row, (0, nCols()))
                  in
                    (
                      (case (#owner(l)) of Var _ => print "V" | Exp _ => print "E");
                      if restricted (l) then print ">" else print "*";
                      if dead (l) then print "#" else print "";
                      print "\t";
                      Compat.Vector.mapi printCol vec;
                      print "\t";
                      print (toString (const (row)));
                      print "\n"
                    )
                  end
          in
            (
              print "\t";
              Array.app printLabel (#clabels(tableau), 0, nCols());
              print "\n";
              Array.app printRow (#rlabels(tableau), 0, nRows());
              print "Columns:\n";
              Array.app (fn (_, l : label) => displaySum (ownerSum (#owner (l))))
                        (#clabels(tableau), 0, nCols());
              print "Rows:\n";
              Array.app (fn (_, l : label) => displaySum (ownerSum (#owner (l))))
                        (#rlabels(tableau), 0, nRows())
            )
          end

    (* find the given monomial in the tableau *)
    let rec findMon (mon) =
          let
            exception Found of int

            let rec find (i, l : label) =
                  (case (#owner(l))
                     of (Var (G, mon')) =>
                          if compatibleMon (mon, mon')
                          then raise Found i
                          else ()
                      | _ => ())
          in
            (Array.app find (#clabels(tableau), 0, nCols());
               (Array.app find (#rlabels(tableau), 0, nRows());
                  NONE)
                handle Found i => SOME(Row(i)))
             handle Found j => SOME(Col(j))
          end

    (* return the a position in the tableau of the tagged expression *)
    let rec findTag (t) =
          let
            exception Found of int

            let rec find (i, l : label) =
                  if (#tag(l) = t)
                  then raise Found i
                  else ()
          in
            (Array.app find (#clabels(tableau), 0, nCols());
               (Array.app find (#rlabels(tableau), 0, nRows());
                  NONE)
                handle Found i => SOME(Row(i)))
             handle Found j => SOME(Col(j))
          end

    (* return true iff the given row is null at all the active columns *)
    let rec isConstant (row) =
          Array.foldl
           (fn (j, l, rest) =>
              (dead (l) orelse (coeff (row, j) = zero)) andalso rest)
           true
           (#clabels(tableau), 0, nCols())

    (* return the position of the row/column of the tableau (if any) that makes the
       given row redundant *)
    let rec isSubsumed (row) =
          let
            let constRow = const (row)

            let rec isSubsumedByRow () =
                  let
                    (* the candidates are those (active) rows with the same constant
                       term *)
                    let candidates =
                          Array.foldl
                            (fn (i, l : label, rest) =>
                               if (i <> row)
                                 andalso not (dead (l))
                                 andalso (const (i) = constRow)
                               then (i :: rest)
                               else rest)
                            nil
                            (#rlabels(tableau), 0, nRows())
                    (* if j is active, trim the list of candidates to those that have
                       the same coefficient in column j
                    *)
                    let rec filter = function (j, l, nil) -> nil
                      | (j, l : label, candidates) -> 
                          if not (dead (l))
                          then
                             List.filter
                               (fun i -> (coeff (i, j) = coeff (row, j)))
                               candidates
                          else
                            candidates
                  in
                    (case (Array.foldl filter candidates
                                       (#clabels(tableau), 0, nCols()))
                       of nil => NONE
                        | (i :: _) => SOME(i))
                  end

            let rec isSubsumedByCol () =
                  if (constRow = zero)
                  then
                    let
                      (* compute the list of non-null coefficients in the row *)
                      let nonNull =
                            Array.foldl
                              (fn (j, l : label, rest) =>
                                 if not (dead (l))
                                 then
                                   let
                                     let value = coeff (row, j)
                                   in
                                     if (value <> zero)
                                     then ((j, value) :: rest)
                                     else rest
                                   end
                                 else
                                   rest)
                             nil
                             (#clabels(tableau), 0, nCols())
                    in
                      (case nonNull
                         of [(j, value)] =>
                              if (value = one) then SOME(j)
                              else NONE
                          | _ => NONE)
                    end
                  else
                    NONE
          in
            case isSubsumedByRow ()
              of SOME(i) => SOME(Row(i))
               | NONE => (case isSubsumedByCol ()
                            of SOME(j) => SOME(Col(j))
                             | NONE => NONE)
          end

     (* find the coordinates of the pivot which gives the largest increase in
        const(row) *)
     let rec findPivot (row) =
          let
            (* extend Integers.compare to deal with NONE (= infinity) *)
            let rec compareScore = function (SOME(d), SOME(d')) -> 
                  compare (d, d')
              | (SOME(d), NONE) -> LESS
              | (NONE, SOME(d')) -> GREATER
              | (NONE, NONE) -> EQUAL

            (* find the best pivot candidates for the given row *)
            let rec findPivotCol (j, l : label, result as (score, champs)) =
                  let
                    let value = coeff(row, j)
                    (* find the best pivot candidates for the given row and column *)
                    let rec findPivotRow sgn (i, l : label, result as (score, champs)) =
                          let
                            let value = coeff (i, j)
                          in
                            if (not (dead (l))) andalso (i <> row) andalso restricted (l)
                              andalso ((fromInt (sgn) * value) < zero)
                            then
                              let
                                let score' = SOME(abs (const (i) * inverse (value)))
                              in
                                case compareScore (score, score')
                                  (* always choose the smallest *)
                                  of GREATER => (score', [(i, j)])
                                   | EQUAL => (score, (i, j) :: champs)
                                   | LESS => result
                              end
                            else
                              result
                          end
                  in
                    if (not (dead (l))) andalso (value <> zero)
                      andalso (not (restricted (l)) orelse (value > zero))
                    then
                      let
                        let (result' as (score', champs')) =
                              Array.foldl (findPivotRow (sign value))
                                                (NONE, [(row, j)])
                                                (#rlabels(tableau), 0, nRows ())
                      in
                        case compareScore (score, score')
                          (* always choose the largest *)
                          of GREATER => result
                           | EQUAL => (score, champs @ champs')
                           | LESS => result'
                      end
                    else
                      result
                  end
          in
            case (Array.foldl findPivotCol (SOME(zero), nil)
                                    (#clabels(tableau), 0, nCols ()))
              of (_, nil) => NONE
               | (_, champs) =>
                   (* choose one randomly to ensure fairness *)
                   SOME(List.nth (champs, rand (0, List.length (champs))))
          end

    (* pivot the element at the given coordinates *)
    let rec pivot (row, col) =
          let
            let pCoeffInverse = inverse (coeff (row, col))

            let pRowVector =
                  Array2.row (#coeffs(tableau), row, (0, nCols ()))
            let rec pRow(j) = Vector.sub (pRowVector, j)

            let pColVector =
                  Array2.column (#coeffs(tableau), col, (0, nRows ()))
            let rec pCol(i) = Vector.sub (pColVector, i)

            let pConst = const (row)

            let pRLabel = rlabel (row)
            let pCLabel = clabel (col)
          in
            (
               Array.modify
                 (fn (i, value) =>
                    if (i = row) then
                      (* same row as the pivot *)
                      ~(value * pCoeffInverse)
                    else
                      (* any other row *)
                      value - (pConst * pCol(i) * pCoeffInverse))
                 (#consts(tableau), 0, nRows());

                Array2.modify Array2.ColMajor
                  (fn (i, j, value) =>
                     (case (i = row, j = col)
                        of (true, true) =>
                             (* pivot *)
                             pCoeffInverse
                         | (true, false) =>
                             (* same row as the pivot *)
                             ~(value * pCoeffInverse)
                         | (false, true) =>
                             (* same column as the pivot *)
                             value * pCoeffInverse
                         | (false, false) =>
                             (* any other row/column *)
                             value - (pRow(j) * pCol (i) * pCoeffInverse)))
                  {base = (#coeffs(tableau)), row = 0, col = 0,
                   nrows = nRows(), ncols = nCols ()};

               Array.update (#rlabels(tableau), row, pCLabel);
               Array.update (#clabels(tableau), col, pRLabel)
            )
          end

    (* delay all terms of a monomial on the given constraint *)
    let rec delayMon (Mon(n, UsL), cnstr) =
          List.app (fun Us -> Unify.delay (Us, cnstr)) UsL

    (* unify two restrictions *)
    let rec unifyRestr (Restr (G, proof), proof') =
          if Unify.unifiable (G, (proof, id), (proof', id)) then ()
          else raise Error

    (* unify a sum with a number *)
    let rec unifySum (G, sum, d) =
          if (Unify.unify (G, (toExp (sum), id),
                                  (constant (floor (d)), id)); true)
          then ()
          else raise Error

    (* decomposition of an expression as the weighted sum of tableau positions *)
    type decomp = number * (number * position) list

    (* change sign to the given decomposition *)
    let rec unaryMinusDecomp ((d, wposL)) =
          (~d, List.map (fn (d, pos) => (~d, pos)) wposL)

    type MaximizeResult =              (* Result of maximization of a row:             *)
      Nonnegative of number                (* nonnegative value c                          *)
    | Unbounded of int                     (* manifestly unbounded, pivoting on column col *)

    type BranchResult =
      BranchSucceed of int option
    | BranchFail
    | BranchDivide of int * BranchResult * BranchResult

    (* decompose a sum in whnf into a weighted sum of tableau positions *)
    let rec decomposeSum (G, sum (m, monL)) =
          let
            let rec monToWPos (mon as (Mon(n, UsL))) =
                  (case findMon (mon)
                     of SOME(pos) => (fromInteger (n), pos)
                      | NONE =>
                          let
                            let new = incrNCols()
                            let l = {owner = Var (G, Mon(one_int, UsL)),
                                     tag = ref 0,
                                     restr = ref NONE,
                                     dead = ref false}
                          in
                             (
                               Trail.log (#trail(tableau), Insert(Col(new)));
                               delayMon (mon, ref (makeCnstr (#tag(l))));
                               Array.update (#clabels(tableau), new, l);
                               (fromInteger (n), Col(new))
                             )
                          end)
          in
            (fromInteger (m), List.map monToWPos monL)
          end

    (* maximize the given row by performing pivot operations.
       Return a term of type MaximizeResult *)
    and maximizeRow (row) =
          let
            let value = const(row)
          in
            if (value < zero)
            then
              (case findPivot (row)
                 of SOME(i,j) =>
                      if (i <> row) then
                        (
                          Trail.log (#trail(tableau), Pivot(i, j));
                          pivot (i, j);
                          maximizeRow row
                        )
                      else
                        (* the tableau is unbounded *)
                        Unbounded j
                  | NONE => raise Error)
            else Nonnegative value
          end

    (* insert the given expression in the tableau, labelling it with owner *)
    and insertDecomp (decomp as (d, wposL), owner) =
          let
            let new = incrNRows ()

            let rec insertWPos (d, pos) =
                  (case pos
                     of Row(row) =>
                          (
                            incrArray2Row (#coeffs(tableau), new,
                                           (0, nCols()),
                                           (fn (j) =>
                                              d*coeff(row, j)));
                            incrArray (#consts(tableau), new,
                                       d*const(row))
                          )
                      | Col(col) =>
                          incrArray2 (#coeffs(tableau), new, col, d))
          in
            (
              (* add the decomposition to the newly created row *)
              List.app insertWPos wposL;
              incrArray(#consts(tableau), new, d);
              (* is this row trivial? *)
              case isSubsumed (new)
                of SOME(pos) =>
                     (
                       clearArray2Row (#coeffs(tableau), new, (0, nCols()));
                       Array.update (#consts(tableau), new, zero);
                       decrNRows ();
                       pos
                     )
                 | NONE =>
                     (
                       setOwnership (Row(new), owner, ref 0);
                       #dead(label(Row(new))) := isConstant(new);
                       (* log the creation of this row *)
                       Trail.log (#trail(tableau), Insert(Row(new)));
                       (* return its position *)
                       Row(new)
                     )
            )
          end

    (* insert the given (unrestricted) expression in the tableau *)
    and insert (G, Us) =
          let
            let sum = fromExp Us
          in
            insertDecomp (decomposeSum (G, sum), Exp (G, sum))
          end

    (* restrict the given row/column to be nonnegative *)
    and restrict (pos as Col(col), restr) =
          let
            let l = label(pos)
          in
            if dead(l)
            then
              (unifyRestr (restr, geqNExp (zero_int)); NONE)
            else
              case restriction (l)
                of SOME(Restr(_, proof')) =>
                     (unifyRestr (restr, proof'); NONE)
                 | NONE =>
                     let
                       (* compute the list of non-null row entries *)
                       let nonNull =
                             Array.foldl
                               (fn (i, l : label, rest) =>
                                  if not (dead(l))
                                  then
                                    let
                                      let value = coeff (i, col)
                                    in
                                      if (value <> zero) then (i :: rest)
                                      else rest
                                    end
                                  else
                                    rest)
                             nil
                             (#rlabels(tableau), 0, nRows())
                     in
                       case nonNull
                         of (row :: _) =>
                              (
                                (* pivot to a row position; this is sound since
                                   the column is unrestricted (see Nelson '81)
                                *)
                                Trail.log (#trail(tableau), Pivot(row, col));
                                pivot (row, col);
                                restrict (Row(row), restr)
                              )
                          | nil =>
                              (
                                (* the column is zero at all the active row
                                   positions, so we can restrict it right away
                                *)
                                Trail.log (#trail(tableau), Restrict(Col(col)));
                                #restr(label(Col(col))) := SOME(restr);
                                NONE
                              )
                     end
          end
      | restrict (pos as Row(row), restr) =
          let
            let l = label(pos)
          in
            if dead(l)
            then
              (* it is an integer *)
              (unifyRestr (restr, geqNExp (floor (const (row)))); NONE)
            else
              case restriction (l)
                of SOME(Restr(_, proof')) =>
                     (unifyRestr (restr, proof'); NONE)
                 | NONE =>
                     case maximizeRow (row)
                       of Unbounded col =>
                            (
                              Trail.log (#trail(tableau), Restrict(Row(row)));
                              #restr(Array.sub (#rlabels(tableau), row)) := SOME(restr);
                              if (const(row) < zero)
                              then
                                (
                                  Trail.log (#trail(tableau), Pivot(row, col));
                                  pivot (row, col)
                                )
                              else ();
                              NONE
                            )
                        | Nonnegative value =>
                            (
                              Trail.log (#trail(tableau), Restrict(Row(row)));
                              #restr(Array.sub (#rlabels(tableau), row)) := SOME(restr);
                              SOME(row)
                            )
          end

    (* insert the equality Var(pos) = Us as two inequalities:
         Var(pos) - Us >= zero
         Us - Var(pos) >= zero
    *)
    and insertEqual (G, pos, sum) =
          let
            let (m, wposL) = decomposeSum (G, sum)

            let decomp' = (m, (~one, pos) :: wposL)
            let pos' = insertDecomp (decomp', Exp (G, sum(zero_int, nil)))

            let decomp'' = unaryMinusDecomp (decomp')
            let tag'' = #tag(label (insertDecomp (decomp'', Exp (G, sum(zero_int, nil)))))
          in
            (
               (* the second expression may change position when we
                  restrict the first. We use tags to keep track of it *)
               restrictBB (exploreBB (pos', Restr (G, geqNExp (zero_int))));
               (case findTag (tag'')
                  of SOME(pos'') =>
                       restrictBB (exploreBB (pos'', Restr (G, geqNExp (zero_int)))))
            )
          end

    (* update the tableau upon discovery that Var(pos) = sum *)
    and update (G, pos, sum) =
          let
            let l = label (pos)
          in
            (
              (* if the given position has a owner, delete it, since not doing so
                 may violate the invariant *)
              Trail.log (#trail(tableau), UpdateOwner(pos, #owner(l), #tag(l)));
              setOwnership (pos, Exp (G, sum), ref 0);
              (* analyze the given position to see exactly how to represent this
                 equality *)
              if dead(l)
              then
                (case pos
                   of Row(row) =>
                        (* find out why it died *)
                        if isConstant (row)
                        then
                          (* row is dead because constant and equal to n *)
                          unifySum (G, sum, const(row))
                        else
                          (* row is dead because is subsumed by another *)
                          (case isSubsumed (row)
                             of SOME(pos') => update (G, pos', sum))
                    | Col(col) =>
                        (* column is dead because = 0 *)
                        unifySum (G, sum, zero))
              else
                let
                  let rec isVar = function (sum(m, [mon as Mon(n, _)])) -> 
                        if (m = zero_int) andalso (n = one_int)
                        then SOME(mon)
                        else NONE
                    | (sum) -> NONE
                in
                  case isVar (sum)
                    of SOME(mon) =>
                         (* the nf is another variable *)
                          (case findMon (mon)
                            of SOME _ => insertEqual (G, pos, sum)
                             | NONE =>
                                let
                                  let tag = ref 0
                                in
                                  (
                                    (* recycle the current label *)
                                    Trail.log (#trail(tableau),
                                               UpdateOwner (pos, #owner(l), #tag(l)));
                                    setOwnership (pos, Var (G, mon), tag);
                                    delayMon (mon, ref (makeCnstr (tag)))
                                  )
                                end)
                     | NONE => insertEqual (G, pos, sum)
                 end
            )
          end

    (* insert the proof term used to restrict l (if any) at the beginning of UL *)
    and insertRestrExp (l, UL) =
          (case restriction (l)
             of NONE => UL
              | SOME(Restr(_, _)) =>
                  let
                    let owner = #owner(l)
                    let G = ownerContext (owner)
                    let U = toExp (ownerSum (owner))
                  in
                    (G, geq0 (U)) :: UL
                  end)

    (* returns the list of unsolved constraints associated with the given position *)
    and restrictions (pos) =
          let
            let rec member (x, l) = List.exists (fun y -> x = y) l
            let rec test (l) = restricted(l) andalso not (dead(l))
            let rec reachable = function ((pos as Row(row)) :: candidates, tried, closure) -> 
                  if member (pos, tried)
                  then reachable (candidates, tried, closure)
                  else
                    let
                      let new_candidates =
                            Array.foldl
                              (fn (col, _, candidates) =>
                                    if (coeff(row, col) <> zero)
                                    then (Col(col)) :: candidates
                                    else candidates)
                              nil
                              (#clabels(tableau), 0, nCols())
                      let closure' = if test (label(pos)) then (pos :: closure)
                                     else closure
                    in
                      reachable (new_candidates @ candidates,
                                 pos :: tried,
                                 closure')
                    end
              | ((pos as Col(col)) :: candidates, tried, closure) -> 
                  if member (pos, tried)
                  then reachable (candidates, tried, closure)
                  else
                    let
                      let candidates' =
                            Array.foldl
                              (fn (row, _, candidates) =>
                                    if (coeff(row, col) <> zero)
                                    then (Row(row)) :: candidates
                                    else candidates)
                              nil
                              (#rlabels(tableau), 0, nRows())
                      let closure' = if test (label(pos)) then (pos :: closure)
                                     else closure
                    in
                      reachable (candidates' @ candidates,
                                 pos :: tried,
                                 closure')
                    end
              | (nil, _, closure) -> closure
            let rec restrExp (pos) =
                  let
                    let l = label(pos)
                    let owner = #owner(l)
                    let G = ownerContext (owner)
                    let U = toExp (ownerSum (owner))
                  in
                    (G, geq0 (U))
                  end

          in
            List.map restrExp (reachable ([pos], nil, nil))
          end

    (* returns the list of unsolved constraints associated with the given tag *)
    and toInternal (tag) () =
           (case findTag (tag)
              of NONE => nil
               | SOME(pos) => restrictions (pos))

    (* awake function for tableau constraints *)
    and awake (tag) () =
          (
            (case findTag (tag)
               of SOME(pos) =>
                    let
                      let owner = #owner(label (pos))
                      let G = ownerContext(owner)
                      let sum = normalize (ownerSum (owner))
                   in
                      (update (G, pos, sum) ; true)
                    end
                | NONE => true)
            handle Error => false
          )

    (* simplify function for tableau constraints *)
    and simplify (tag) () =
          (case toInternal (tag) ()
             of nil => true
              | (_ :: _) => false)

    (* create a foreign constraint for the given tag *)
    and makeCnstr (tag) =
          FgnCnstr (!myID, MyFgnCnstrRep (tag))

    (* checks if the (primally and dually) feasible solution is an integral solution;
       returns NONE if it is, otherwise the coordinate of a non-integral component *)
    and isIntegral () =
          let
            exception Found of int

            let rec find (i, l : label) =
                  if not (dead (l)) then
                    if (denominator (const (i)) <> one_int)
                    then raise Found i
                    else ()
                  else () (* unbounded component *)
          in
            (Array.app find (#rlabels(tableau), 0, nRows());
             NONE) handle Found i => SOME(i)
          end

    (* bound the given expression below d *)
    and boundLower (G, decomp, d) =
          let
            let W = newEVar (G, number ())
            let proof = newEVar (G, geq0 (W))

            let (d', wPosL) = unaryMinusDecomp (decomp)
            let pos = insertDecomp ((d' + d, wPosL), Var(G, Mon(one_int, [(W, id)])))
          in
            (pos, Restr(G, proof))
          end

    (* bound the given expression above d *)
    and boundUpper (G, decomp, d) =
          let
            let W = newEVar (G, number ())
            let proof = newEVar (G, geq0 (W))

            let (d', wPosL) = decomp
            let pos = insertDecomp ((d' - d, wPosL), Var(G, Mon(one_int, [(W, id)])))
          in
            (pos, Restr (G, proof))
          end

    (* explore the relaxed solution space looking for integer solutions *)
    and exploreBB (pos, restr) =
          (let
             let result = restrict (pos, restr)
           in
             case isIntegral ()
               of SOME(row) =>
                    let
                      let value = const (row)
                      let decomp = (zero, [(one, Row(row))])
                      let G = ownerContext(#owner(label(Row(row))))

                      let lower = fromInteger (floor (value))
                      let upper = fromInteger (ceiling (value))

                      let rec left () =
                            exploreBB (boundLower (G, decomp, lower))
                      let rec right () =
                            exploreBB (boundUpper (G, decomp, upper))
                    in
                      case (CSM.trail left, CSM.trail right)
                        of (BranchFail, BranchFail) => BranchFail
                         | (resultL, resultR) => BranchDivide(row, resultL, resultR)
                    end
                 | NONE => BranchSucceed(result)
           end) handle Error => BranchFail

    (* minimize a tableau that has been determined non-minimal (but consistent) as a
       consequence of adding the given row
    *)
    and minimizeBB (row) =
          let
            (* check if the column is zero for all possible solutions *)
            let rec zeroColumn (j, l : label) =
                  let
                    let decomp = (zero, [(one, Col(j))])
                    let G = ownerContext(#owner(label(Col(j))))

                    let lower = ~one
                    let upper = one

                    let rec left () =
                          exploreBB (boundLower (G, decomp, lower))
                    let rec right () =
                          exploreBB (boundUpper (G, decomp, upper))
                  in
                    if restricted(l)
                    then (CSM.trail right = BranchFail)
                    else (CSM.trail left = BranchFail) andalso (CSM.trail right = BranchFail)
                  end
            (* equate the given column to zero if coeff(row, j) <> zero *)
            let rec killColumn (j, l : label) =
                  if (not (dead(l))) andalso (coeff(row, j) <> zero)
                    andalso zeroColumn (j, l)
                  then
                    (
                      (* mark the column dead *)
                      Trail.log (#trail(tableau), Kill(Col(j)));
                      #dead(Array.sub (#clabels(tableau), j)) := true;
                      (* if restricted, instantiate the proof object to 0>=0 *)
                      (case restriction (l)
                         of SOME(restr) =>
                              unifyRestr (restr, geqNExp (zero_int))
                          | NONE => ());
                      (* if owned by a monomial, unify it with zero *)
                      (case #owner(l)
                         of (owner as (Var _)) =>
                              unifySum (ownerContext (owner), ownerSum (owner), zero)
                          | _ => ())
                    )
                  else ()
            (* find out if the given row has been made trivial by killing some columns *)
            let rec killRow (i, l : label) =
                  if not (dead(l))
                  then
                    if isConstant (i)
                    then (* row is now constant and equal to n = const(i) *)
                      (
                        (* check if it is an integer *)
                        if denominator (const(i)) = one_int then () else raise Error;
                        (* mark the row dead *)
                        Trail.log (#trail(tableau), Kill(Row(i)));
                        #dead(Array.sub (#rlabels(tableau), i)) := true;
                        (* if restricted, instantiate the proof object to n>=0 *)
                        (case restriction (l)
                           of SOME(restr) =>
                                if denominator (const(i)) = one_int
                                then unifyRestr (restr, geqNExp (floor (const(i))))
                                else raise Error
                            | NONE => ());
                        (* if owned by a monomial, unify it with n *)
                        (case #owner(l)
                           of (owner as (Var _)) =>
                                unifySum (ownerContext (owner), ownerSum (owner), const(i))
                            | _ => ())
                      )
                    else
                      case isSubsumed (i)
                        of SOME(pos') =>
                             let
                               let l' = label(pos')
                             in
                               (
                                 Trail.log (#trail(tableau), Kill(Row(i)));
                                 #dead(Array.sub (#rlabels(tableau), i)) := true;
                                 (case (restriction (l), restriction (l'))
                                    of (SOME(restr), SOME(Restr(_, proof'))) =>
                                         unifyRestr (restr, proof')
                                     | (SOME _, NONE) =>
                                         (
                                           (* it is safe to restrict without doing all
                                              the checks in this case, since the two rows
                                              are identical *)
                                           Trail.log (#trail(tableau), Restrict(pos'));
                                           #restr(l') := restriction (l)
                                         )
                                     | (NONE, _) => ())
                               )
                             end
                         | NONE => ()
                  else ()
          in
            (
              Array.app killColumn (#clabels(tableau), 0, nCols());
              Array.app killRow (#rlabels(tableau), 0, nRows())
            )
          end

    and restrictBB (result) =
          case result
            of BranchFail => raise Error
             | BranchDivide(row, resultL, BranchFail) =>
                 let
                   let value = fromInteger (floor (const (row)))
                   let decomp = (zero, [(one, Row(row))])
                   let G = ownerContext(#owner(label(Row(row))))
                   let _ = restrict (boundLower (G, decomp, value))
                 in
                   restrictBB (resultL)
                 end
             | BranchDivide(row, BranchFail, resultR) =>
                 let
                   let value = fromInteger (ceiling (const (row)))
                   let decomp = (zero, [(one, Row(row))])
                   let G = ownerContext(#owner(label(Row(row))))
                   let _ = restrict (boundUpper (G, decomp, value))
                 in
                   restrictBB (resultR)
                 end
             | BranchSucceed result =>
                 (case result
                    of SOME(row) => minimizeBB (row)
                     | NONE => ())
             | _ => ()

    (* undo function for trailing tableau operations *)
    let rec undo = function (Insert(Row(row))) -> 
          (
            #dead(Array.sub (#rlabels(tableau), row)) := true;
            clearArray2Row (#coeffs(tableau), row, (0, nCols()));
            Array.update(#consts(tableau), row, zero);
            decrNRows ()
          )
      | (Insert(Col(col))) -> 
          (
            #dead(Array.sub (#clabels(tableau), col)) := true;
            clearArray2Col (#coeffs(tableau), col, (0, nRows()));
            decrNCols ()
          )
      | (Pivot(row, col)) -> 
          pivot(row, col)
      | (Kill(pos)) -> 
          #dead(label(pos)) := false
      | (Restrict(pos)) -> 
          #restr(label(pos)) := NONE
      | (UpdateOwner(pos, owner, tag)) -> 
          setOwnership (pos, owner, tag)

    (* reset the internal status of the tableau *)
    let rec reset () =
          let
            let l = {owner = Exp (Null, sum(zero_int, nil)), tag = ref 0,
                     restr = ref NONE, dead = ref true}
          in
            (
               Array.modify
                 (fun _ -> l)
                 (#rlabels(tableau), 0, nRows());
               Array.modify
                 (fun _ -> l)
                 (#clabels(tableau), 0, nCols());
               Array.modify
                 (fun _ -> zero)
                 (#consts(tableau), 0, nRows());
               Array2.modify
                 Array2.RowMajor (fun _ -> zero)
                 {base = #coeffs(tableau), row = 0, col = 0,
                  nrows = nRows(), ncols = nCols()};
               #nrows(tableau) := 0; #ncols(tableau) := 0;
               Trail.reset (#trail(tableau))
            )
          end

    (* trailing functions *)
    let rec mark () =
          Trail.mark (#trail(tableau))

    let rec unwind () =
          Trail.unwind (#trail(tableau), undo)

    (* fst (S, s) = U1, the first argument in S[s] *)
    let rec fst = function (App (U1, _), s) -> (U1, s)
      | (SClo (S, s'), s) -> fst (S, comp (s', s))

    (* snd (S, s) = U2, the second argument in S[s] *)
    let rec snd = function (App (U1, S), s) -> fst (S, s)
      | (SClo (S, s'), s) -> snd (S, comp (s', s))

    (* checks if the given foreign term can be simplified to a constant *)
    let rec isConstantExp (U) =
          (case (fromExp (U, id))
             of (sum(m, nil)) => SOME(m)
              | _ => NONE)

    (* checks if the given foreign term can be simplified to zero *)
    let rec isZeroExp (U) =
          (case isConstantExp (U)
             of SOME(d) => (d = zero_int)
              | NONE => false)

    (* solveGeq (G, S, n) tries to find the n-th solution to G |- '>=' @ S : type *)
    let rec solveGeq = function (G, S, 0) -> 
          let
            let rec solveGeq0 (W) =
                  case isConstantExp (W)
                    of SOME(d) =>
                         if Integers.>=(d, zero_int)
                         then geqNExp (d)
                         else raise Error
                     | NONE =>
                         let
                           let proof = newEVar (G, geq0 (W))
                           let _ = restrictBB (exploreBB (insert (G, (W, id)),
                                                           Restr (G, proof)))
                         in
                           proof
                         end

            let U1 = EClo (fst (S, id))
            let U2 = EClo (snd (S, id))
          in
            (
              if isZeroExp (U2)
              then SOME(solveGeq0 (U1))
              else
                let
                  let W = minus (U1, U2)
                  let proof = solveGeq0 (W)
                in
                  SOME(geqAdd (W, constant (zero_int), U2, proof))
                end
            ) handle Error => NONE
          end
      | (G, S, n) -> NONE

    (* constructors for higher-order types *)
    let rec pi (name, U, V) = Pi ((Dec (SOME(name), U), Maybe), V)
    let rec arrow (U, V) = Pi ((Dec (NONE, U), No), V)

    let rec installFgnCnstrOps () = let
        let csid = !myID
        let _ = FgnCnstrStd.ToInternal.install (csid,
                                                (fn (MyFgnCnstrRep tag) => toInternal (tag)
                                                  | fc => raise UnexpectedFgnCnstr fc))
        let _ = FgnCnstrStd.Awake.install (csid,
                                           (fn (MyFgnCnstrRep tag) => awake (tag)
                                             | fc => raise UnexpectedFgnCnstr fc))
        let _ = FgnCnstrStd.Simplify.install (csid,
                                              (fn (MyFgnCnstrRep tag) => simplify (tag)
                                                | fc => raise UnexpectedFgnCnstr fc))
    in
        ()
    end

    (* install the module type *)
    let rec init (cs, installF) =
          (
            myID := cs;

            geqID :=
              installF (ConDec (">=", NONE, 0,
                                Constraint (!myID, solveGeq),
                                arrow (number (), arrow (number (), Uni (Type))), Kind),
                        SOME(FX.Infix(FX.minPrec, FX.None)),
                        [MS.Mapp(MS.Marg(MS.Star, NONE),
                                MS.Mapp(MS.Marg(MS.Star, NONE), MS.Mnil))]);

            geqAddID :=
              installF (ConDec ("+>=", NONE, 2, Normal,
                                pi ("X", number(),
                                    pi ("Y", number(),
                                        pi ("Z", number(),
                                            arrow (geq (Root (BVar 3, Nil),
                                                        Root (BVar 2, Nil)),
                                                   geq (plus (Root (BVar 4, Nil),
                                                              Root (BVar 2, Nil)),
                                                        plus (Root (BVar 3, Nil),
                                                              Root (BVar 2, Nil))))))),
                                Type),
                        NONE, nil);

            installFgnCnstrOps ();
            ()
          )
  in
    let solver =
          {
            name = ("inequality/integers"),
            keywords = "arithmetic,inequality",
            needs = ["Unify", #name(CSEqIntegers.solver)],

            fgnConst = SOME({parse = parseGeqN}),

            init = init,

            reset  = reset,
            mark   = mark,
            unwind = unwind
          } : CSManager.solver
  end
end  (* functor CSIneqIntegers *)
