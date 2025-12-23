(* Solver for_sml linear inequations, based on branch & bound *)

(* Author: Roberto Virga *)

module CSIneqIntegers
    (Integers : Integers.INTEGERS)
    (Rationals : Rationals.RATIONALS)
    (Trail : Trail.TRAIL)
    (Unify : Unify.UNIFY)
    (SparseArray : Sparse_array.SPARSE_ARRAY)
    (SparseArray2 : Sparse_array.Sparse_array2.SPARSE_ARRAY2)
    (CSEqIntegers : Cs.Cs_eq_integers.CS_EQ_INTEGERS)
    (Compat : Compat.COMPAT) =
struct
  (*! structure Cs.CSManager = Cs.CSManager !*)

  open IntSyn
  open Rationals
  open Cs.CSEqIntegers
  module CSM = Cs.CSManager
  module FX = Cs.CSMFixity
  module MS = ModeSyn
  (* Cs.CSM.ModeSyn *)

  module Array = SparseArray
  module Array2 = SparseArray2
  (* useful integer values *)

  let zero_int = Integers.fromInt 0
  let one_int = Integers.fromInt 1
  (* solver ID of this solver *)

  let myID = (ref - 1 : cid ref)
  (* constant IDs of the declared type constants *)

  let geqID = (ref - 1 : cid ref)
  (* constructors for_sml the declared types *)

  let rec geq (U, V) = Root (Const !geqID, App (U, App (V, Nil)))
  (* specialized constructors for_sml the declared types *)

  let rec geq0 U = geq (U, constant zero_int)
  (* constant IDs of the declared object constants *)

  let geqAddID = (ref - 1 : cid ref)
  (* constructors for_sml the declared objects *)

  let rec geqAdd (U1, U2, V, W) =
    Root (Const !geqAddID, App (U1, App (U2, App (V, App (W, Nil)))))
  (* constant declaration for_sml the proof object d>=0 *)

  let rec geqNConDec d =
    ConDec
      ( Integers.toString d ^ ">=" ^ Integers.toString zero_int,
        None,
        0,
        Normal,
        geq0 (constant d),
        Type )
  (* foreign constant for_sml the proof object d>=0 *)

  let rec geqNExp d = Root (FgnConst (!myID, geqNConDec d), Nil)
  (* parsing proof objects d>=0 *)

  let rec parseGeqN string =
    let suffix = ">=" ^ toString zero in
    let stringLen = String.size string in
    let suffixLen = String.size suffix in
    let numLen = (Int).-(stringLen, suffixLen) in
    if
      (Int).>(stringLen, suffixLen)
      && String.substring (string, numLen, suffixLen) = suffix
    then
      match Integers.fromString (String.substring (string, 0, numLen)) with
      | Some d ->
          if (Integers).>=(d, zero_int) then Some (geqNConDec d) else None
      | None -> None
    else None

  type position = Row of int | Col of int
  type owner = Var of IntSyn.dctx * mon | Exp of IntSyn.dctx * sum
  (*   - sum                           *)

  type restriction = Restr of IntSyn.dctx * IntSyn.exp
  (*   Restr (G, U)                    *)

  type label =
    < owner : owner (* owner of the row/column (if any)  *)
    ; tag : int ref (* tag: used to keep track of the    *)
    ; (* position of a tableau entry       *)
    restr : restriction option ref (* restriction (if any)              *)
    ; dead : bool ref >
  (* has the row/column already been   *)

  (* solved?                           *)

  type operation =
    | Insert of position
    | Pivot of int * int
    | Kill of position
    | Restrict of position
    | UpdateOwner of position * owner * int ref
  (* change the owner                  *)

  type tableau =
    (* Tableau:                          *)
    < rlabels : label Array.array (* row labels                        *)
    ; clabels : label Array.array (* column labels                     *)
    ; consts : number Array.array (* constant terms                    *)
    ; coeffs : number Array2.array (* variables coefficients            *)
    ; nrows : int ref
    ; ncols : int ref (* dimensions                        *)
    ; trail : operation Trail.trail >
  (* undo mechanism                    *)

  exception MyFgnCnstrRep of int ref
  (* FgnCnstr representation *)

  exception Error
  (* Representational invariants:
         rlabels[i] = vacuous
         clabels[j] = vacuous
         const[i] = zero
         coeff[i,j] = zero
       for_sml i >= !nrows or j > !ncols, where "vacuous" is the vacuous label:
          #owner(vacuous) = Exp (Null, Sum (zero, nil))
          #restr(vacuous) = ref NONE
          #dead(vacuous) = ref true
    *)

  (* little random generation routine taken from Paulson '91 *)

  let a = 16807.0
  and m = 2147483647.0

  let seed = ref 1999.0

  let rec rand (min, size) =
    let rec nextrand () =
      let t = (Real).*(a, !seed) in
      seed := (Real).-(t, (Real).*(m, Real.fromInt (Real.floor (t / m))));
      (Real).-(!seed, 1.0) / (Real).-(m, 1.0)
    in
    (Int).+(min, Real.floor (Real).*(nextrand (), Real.fromInt size))
  (* create a new (empty) tableau *)

  let tableau =
    let l =
      {
        owner = Exp (Null, Sum (zero_int, []));
        tag = ref 0;
        restr = ref None;
        dead = ref true;
      }
    in
    ({
       rlabels = Array.array l;
       clabels = Array.array l;
       consts = Array.array zero;
       coeffs = Array2.array zero;
       nrows = ref 0;
       ncols = ref 0;
       trail = Trail.trail ();
     }
      : tableau)
  (* i-th tableau row label *)

  let rec rlabel i = Array.sub (rlabels tableau, i)
  (* j-th tableau column label *)

  let rec clabel j = Array.sub (clabels tableau, j)
  (* i-th tableau constant term *)

  let rec const i = Array.sub (consts tableau, i)
  (* coefficient in row i, column j *)

  let rec coeff (i, j) = Array2.sub (coeffs tableau, i, j)
  (* number of rows *)

  let rec nRows () = !(nrows tableau)
  (* number of columns *)

  let rec nCols () = !(ncols tableau)
  (* increase the number of rows, and return the index of the last row *)

  let rec incrNRows () =
    let old = nRows () in
    nrows tableau := (Int).+(old, 1);
    old
  (* increase the number of columns, and return the index of the last column *)

  let rec incrNCols () =
    let old = nCols () in
    ncols tableau := (Int).+(old, 1);
    old
  (* decrease the number of rows *)

  let rec decrNRows () = nrows tableau := (Int).-(nRows (), 1)
  (* decrease the number of columns *)

  let rec decrNCols () = ncols tableau := (Int).-(nCols (), 1)
  (* increase by the given amount the element i of the array *)

  let rec incrArray (array, i, value) =
    Array.update (array, i, Array.sub (array, i) + value)
  (* increase by the given amount the element (i, j) of the array *)

  let rec incrArray2 (array, i, j, value) =
    Array2.update (array, i, j, Array2.sub (array, i, j) + value)
  (* increase by f(j') all the elements (i, j'), with j <= j' < j+len *)

  let rec incrArray2Row (array, i, (j, len), f) =
    Compat.Vector.mapi
      (fun (j, value) -> Array2.update (array, i, j, value + f j))
      (Array2.row (array, i, (j, len)))
  (* increase by f(i') all the elements (i', j), with i <= i' < i+len *)

  let rec incrArray2Col (array, j, (i, len), f) =
    Compat.Vector.mapi
      (fun (i, value) -> Array2.update (array, i, j, value + f i))
      (Array2.column (array, j, (i, len)))
  (* set the given row to zero *)

  let rec clearArray2Row (array, i, (j, len)) =
    Compat.Vector.mapi
      (fun (j, value) -> Array2.update (array, i, j, zero))
      (Array2.row (array, i, (j, len)))
  (* set the given column to zero *)

  let rec clearArray2Col (array, j, (i, len)) =
    Compat.Vector.mapi
      (fun (i, value) -> Array2.update (array, i, j, zero))
      (Array2.column (array, j, (i, len)))
  (* return the label at the given position (row or column) *)

  let rec label = function Row i -> rlabel i | Col j -> clabel j
  (* return the restriction on the given label *)

  let rec restriction (l : label) = !(restr l)
  (* is the given label is restricted? *)

  let rec restricted (l : label) =
    match restriction l with Some _ -> true | None -> false
  (* return true iff the given label has been solved *)

  let rec dead (l : label) = !(dead l)
  (* set the ownership of the given position *)

  let rec setOwnership (pos, owner, tag) =
    let old = label pos in
    let new_ =
      { owner; tag; restr = ref (restriction old); dead = ref (dead old) }
    in
    match pos with
    | Row i -> Array.update (rlabels tableau, i, new_)
    | Col j -> Array.update (clabels tableau, j, new_)
  (* return the context of a owner *)

  let rec ownerContext = function Var (G, mon) -> G | Exp (G, sum) -> G
  (* return the a sum *)

  let rec ownerSum = function
    | Var (G, mon) -> Sum (zero_int, [ mon ])
    | Exp (G, sum) -> sum
  (* debugging code - REMOVE *)

  let rec displayPos = function
    | Row row -> print ("row " ^ Int.toString row ^ "\n")
    | Col col -> print ("column " ^ Int.toString col ^ "\n")
  (* debugging code - REMOVE *)

  let rec displaySum = function
    | Sum (m, Mon (n, _) :: monL) ->
        print (Integers.toString n);
        print " ? + ";
        displaySum (Sum (m, monL))
    | Sum (m, []) ->
        print (Integers.toString m);
        print " >= 0\n"
  (* debugging code - REMOVE *)

  let rec display () =
    let rec printLabel (col, (l : label)) =
      print "\t";
      (match owner l with Var _ -> print "V" | Exp _ -> print "E");
      if restricted l then print ">" else print "*";
      if dead l then print "#" else print ""
    in
    let rec printRow (row, (l : label)) =
      let rec printCol ((col, d) : number) =
        print "\t";
        print (toString d)
      in
      let vec = Array2.row (coeffs tableau, row, (0, nCols ())) in
      (match owner l with Var _ -> print "V" | Exp _ -> print "E");
      if restricted l then print ">" else print "*";
      if dead l then print "#" else print "";
      print "\t";
      Compat.Vector.mapi printCol vec;
      print "\t";
      print (toString (const row));
      print "\n"
    in
    print "\t";
    Array.app printLabel (clabels tableau, 0, nCols ());
    print "\n";
    Array.app printRow (rlabels tableau, 0, nRows ());
    print "Columns:\n";
    Array.app
      (fun (_, (l : label)) -> displaySum (ownerSum (owner l)))
      (clabels tableau, 0, nCols ());
    print "Rows:\n";
    Array.app
      (fun (_, (l : label)) -> displaySum (ownerSum (owner l)))
      (rlabels tableau, 0, nRows ())
  (* find the given monomial in the tableau *)

  let rec findMon mon =
    let exception Found of int in
    let rec find (i, (l : label)) =
      match owner l with
      | Var (G, mon') ->
          if compatibleMon (mon, mon') then raise (Found i) else ()
      | _ -> ()
    in
    try
      Array.app find (clabels tableau, 0, nCols ());
      try
        Array.app find (rlabels tableau, 0, nRows ());
        None
      with Found i -> Some (Row i)
    with Found j -> Some (Col j)
  (* return the a position in the tableau of the tagged expression *)

  let rec findTag t =
    let exception Found of int in
    let rec find (i, (l : label)) = if tag l = t then raise (Found i) else () in
    try
      Array.app find (clabels tableau, 0, nCols ());
      try
        Array.app find (rlabels tableau, 0, nRows ());
        None
      with Found i -> Some (Row i)
    with Found j -> Some (Col j)
  (* return true iff the given row is null at all the active columns *)

  let rec isConstant row =
    Array.foldl
      (fun (j, l, rest) -> (dead l || coeff (row, j) = zero) && rest)
      true
      (clabels tableau, 0, nCols ())
  (* return the position of the row/column of the tableau (if any) that makes the
       given row redundant *)

  let rec isSubsumed row =
    let constRow = const row in
    let rec isSubsumedByRow () =
      (* the candidates are those (active) rows with the same constant
                       term *)
      (* if j is active, trim the list of candidates to those that have
                       the same coefficient in column j
                    *)
      let candidates =
        Array.foldl
          (fun (i, (l : label), rest) ->
            if i <> row && (not (dead l)) && const i = constRow then i :: rest
            else rest)
          []
          (rlabels tableau, 0, nRows ())
      in
      let rec filter = function
        | j, l, [] -> []
        | j, (l : label), candidates ->
            if not (dead l) then
              List.filter (fun i -> coeff (i, j) = coeff (row, j)) candidates
            else candidates
      in
      match Array.foldl filter candidates (clabels tableau, 0, nCols ()) with
      | [] -> None
      | i :: _ -> Some i
    in
    let rec isSubsumedByCol () =
      if constRow = zero then
        (* compute the list of non-null coefficients in the row *)
        let nonNull =
          Array.foldl
            (fun (j, (l : label), rest) ->
              if not (dead l) then
                let value = coeff (row, j) in
                if value <> zero then (j, value) :: rest else rest
              else rest)
            []
            (clabels tableau, 0, nCols ())
        in
        match nonNull with
        | [ (j, value) ] -> if value = one then Some j else None
        | _ -> None
      else None
    in
    match isSubsumedByRow () with
    | Some i -> Some (Row i)
    | None -> (
        match isSubsumedByCol () with Some j -> Some (Col j) | None -> None)
  (* find the coordinates of the pivot which gives the largest increase in
        const(row) *)

  let rec findPivot row =
    (* extend Integers.compare to deal with NONE (= infinity) *)
    (* find the best pivot candidates for_sml the given row *)
    let rec compareScore = function
      | Some d, Some d' -> compare (d, d')
      | Some d, None -> Lt
      | None, Some d' -> Gt
      | None, None -> Eq
    in
    let rec findPivotCol (j, (l : label), result) =
      (* find the best pivot candidates for_sml the given row and column *)
      let value = coeff (row, j) in
      let rec findPivotRow sgn (i, (l : label), result) =
        let value = coeff (i, j) in
        if
          (not (dead l))
          && i <> row && restricted l
          && fromInt sgn * value < zero
        then
          let score' = Some (abs (const i * inverse value)) in
          match
            compareScore (score, score') (* always choose the smallest *)
          with
          | Gt -> (score', [ (i, j) ])
          | Eq -> (score, (i, j) :: champs)
          | Lt -> result
        else result
      in
      if
        (not (dead l)) && value <> zero && ((not (restricted l)) || value > zero)
      then
        let result' =
          Array.foldl
            (findPivotRow (sign value))
            (None, [ (row, j) ])
            (rlabels tableau, 0, nRows ())
        in
        match compareScore (score, score') (* always choose the largest *) with
        | Gt -> result
        | Eq -> (score, champs @ champs')
        | Lt -> result'
      else result
    in
    match
      Array.foldl findPivotCol (Some zero, []) (clabels tableau, 0, nCols ())
    with
    | _, [] -> None
    | _, champs ->
        (* choose one randomly to ensure fairness *)
        Some (List.nth (champs, rand (0, List.length champs)))
  (* pivot the element at the given coordinates *)

  let rec pivot (row, col) =
    let pCoeffInverse = inverse (coeff (row, col)) in
    let pRowVector = Array2.row (coeffs tableau, row, (0, nCols ())) in
    let rec pRow j = Vector.sub (pRowVector, j) in
    let pColVector = Array2.column (coeffs tableau, col, (0, nRows ())) in
    let rec pCol i = Vector.sub (pColVector, i) in
    let pConst = const row in
    let pRLabel = rlabel row in
    let pCLabel = clabel col in
    Array.modify
      (fun (i, value) ->
        if i = row then (* same the pivot *)
          ~-(value * pCoeffInverse)
        else (* any other row *)
          value - (pConst * pCol i * pCoeffInverse))
      (consts tableau, 0, nRows ());
    Array2.modify Array2.ColMajor
      (fun (i, j, value) ->
        match (i = row, j = col) with
        | true, true ->
            (* pivot *)
            pCoeffInverse
        | true, false ->
            (* same the pivot *)
            ~-(value * pCoeffInverse)
        | false, true ->
            (* same the pivot *)
            value * pCoeffInverse
        | false, false ->
            (* any other row/column *)
            value - (pRow j * pCol i * pCoeffInverse))
      {
        base = coeffs tableau;
        row = 0;
        col = 0;
        nrows = nRows ();
        ncols = nCols ();
      };
    Array.update (rlabels tableau, row, pCLabel);
    Array.update (clabels tableau, col, pRLabel)
  (* delay all terms of a monomial on the given constraint *)

  let rec delayMon (Mon (n, UsL), cnstr) =
    List.app (fun Us -> Unify.delay (Us, cnstr)) UsL
  (* unify two restrictions *)

  let rec unifyRestr (Restr (G, proof), proof') =
    if Unify.unifiable (G, (proof, id), (proof', id)) then () else raise Error
  (* unify a sum with a number *)

  let rec unifySum (G, sum, d) =
    if
      Unify.unify (G, (toExp sum, id), (constant (floor d), id));
      true
    then ()
    else raise Error
  (* decomposition of an the weighted sum of tableau positions *)

  type decomp = number * number * position list
  (* change sign to the given decomposition *)

  let rec unaryMinusDecomp (d, wposL) =
    (~-d, List.map (fun (d, pos) -> (~-d, pos)) wposL)

  type maximizeResult = Nonnegative of number | Unbounded of int
  (* manifestly unbounded, pivoting on column col *)

  type branchResult =
    | BranchSucceed of int option
    | BranchFail
    | BranchDivide of int * branchResult * branchResult
  (* decompose a sum in whnf into a weighted sum of tableau positions *)

  let rec decomposeSum (G, Sum (m, monL)) =
    let rec monToWPos mon =
      match findMon mon with
      | Some pos -> (fromInteger n, pos)
      | None ->
          let new_ = incrNCols () in
          let l =
            {
              owner = Var (G, Mon (one_int, UsL));
              tag = ref 0;
              restr = ref None;
              dead = ref false;
            }
          in
          Trail.log (trail tableau, Insert (Col new_));
          delayMon (mon, ref (makeCnstr (tag l)));
          Array.update (clabels tableau, new_, l);
          (fromInteger n, Col new_)
    in
    (fromInteger m, List.map monToWPos monL)

  and maximizeRow row =
    let value = const row in
    if value < zero then
      match findPivot row with
      | Some (i, j) ->
          if i <> row then (
            Trail.log (trail tableau, Pivot (i, j));
            pivot (i, j);
            maximizeRow row)
          else (* the tableau is unbounded *)
            Unbounded j
      | None -> raise Error
    else Nonnegative value

  and insertDecomp (decomp, owner) =
    let new_ = incrNRows () in
    let rec insertWPos (d, pos) =
      match pos with
      | Row row ->
          incrArray2Row
            (coeffs tableau, new_, (0, nCols ()), fun j -> d * coeff (row, j));
          incrArray (consts tableau, new_, d * const row)
      | Col col -> incrArray2 (coeffs tableau, new_, col, d)
    in
    (* add the decomposition to the newly created row *)
    List.app insertWPos wposL;
    incrArray (consts tableau, new_, d);
    (* is this row trivial? *)
    match isSubsumed new_ with
    | Some pos ->
        clearArray2Row (coeffs tableau, new_, (0, nCols ()));
        Array.update (consts tableau, new_, zero);
        decrNRows ();
        pos
    | None ->
        setOwnership (Row new_, owner, ref 0);
        dead (label (Row new_)) := isConstant new_;
        (* log the creation of this row *)
        Trail.log (trail tableau, Insert (Row new_));
        (* return its position *)
        Row new_

  and insert (G, Us) =
    let sum = fromExp Us in
    insertDecomp (decomposeSum (G, sum), Exp (G, sum))

  and restrict = function
    | pos, restr -> (
        let l = label pos in
        if dead l then (
          unifyRestr (restr, geqNExp zero_int);
          None)
        else
          match restriction l with
          | Some (Restr (_, proof')) ->
              unifyRestr (restr, proof');
              None
          | None -> (
              (* compute the list of non-null row entries *)
              let nonNull =
                Array.foldl
                  (fun (i, (l : label), rest) ->
                    if not (dead l) then
                      let value = coeff (i, col) in
                      if value <> zero then i :: rest else rest
                    else rest)
                  []
                  (rlabels tableau, 0, nRows ())
              in
              match nonNull with
              | row :: _ ->
                  (* pivot to a row position; this is sound since
                                   the column is unrestricted (see Nelson '81)
                                *)
                  Trail.log (trail tableau, Pivot (row, col));
                  pivot (row, col);
                  restrict (Row row, restr)
              | [] ->
                  (* the column is zero at all the active row
                                   positions, so we can restrict it right away
                                *)
                  Trail.log (trail tableau, Restrict (Col col));
                  restr (label (Col col)) := Some restr;
                  None))
    | pos, restr -> (
        let l = label pos in
        if dead l then (* it is an integer *)
          (
          unifyRestr (restr, geqNExp (floor (const row)));
          None)
        else
          match restriction l with
          | Some (Restr (_, proof')) ->
              unifyRestr (restr, proof');
              None
          | None -> (
              match maximizeRow row with
              | Unbounded col ->
                  Trail.log (trail tableau, Restrict (Row row));
                  restr (Array.sub (rlabels tableau, row)) := Some restr;
                  if const row < zero then (
                    Trail.log (trail tableau, Pivot (row, col));
                    pivot (row, col))
                  else ();
                  None
              | Nonnegative value ->
                  Trail.log (trail tableau, Restrict (Row row));
                  restr (Array.sub (rlabels tableau, row)) := Some restr;
                  Some row))

  and insertEqual (G, pos, sum) =
    let m, wposL = decomposeSum (G, sum) in
    let decomp' = (m, (~one, pos) :: wposL) in
    let pos' = insertDecomp (decomp', Exp (G, Sum (zero_int, []))) in
    let decomp'' = unaryMinusDecomp decomp' in
    let tag'' =
      tag (label (insertDecomp (decomp'', Exp (G, Sum (zero_int, [])))))
    in
    (* the second expression may change position when we
                  restrict the first. We use tags to keep track of it *)
    restrictBB (exploreBB (pos', Restr (G, geqNExp zero_int)));
    match findTag tag'' with
    | Some pos'' -> restrictBB (exploreBB (pos'', Restr (G, geqNExp zero_int)))

  and update (G, pos, sum) =
    let l = label pos in
    (* if the given position has a owner, delete it, since not doing so
                 may violate the invariant *)
    Trail.log (trail tableau, UpdateOwner (pos, owner l, tag l));
    setOwnership (pos, Exp (G, sum), ref 0);
    (* analyze the given position to see exactly how to represent this
                 equality *)
    if dead l then
      match pos with
      | Row row -> (
          if
            (* find out why it died *)
            isConstant row
          then
            (* row is dead because constant and equal to n *)
            unifySum (G, sum, const row)
          else (* row is dead because is subsumed by another *)
            match isSubsumed row with Some pos' -> update (G, pos', sum))
      | Col col ->
          (* column is dead because = 0 *)
          unifySum (G, sum, zero)
    else
      let rec isVar = function
        | Sum (m, [ mon ]) ->
            if m = zero_int && n = one_int then Some mon else None
        | sum -> None
      in
      match isVar sum with
      | Some mon -> (
          (* the nf is another variable *)
          match findMon mon with
          | Some _ -> insertEqual (G, pos, sum)
          | None ->
              let tag = ref 0 in
              (* recycle the current label *)
              Trail.log (trail tableau, UpdateOwner (pos, owner l, tag l));
              setOwnership (pos, Var (G, mon), tag);
              delayMon (mon, ref (makeCnstr tag)))
      | None -> insertEqual (G, pos, sum)

  and insertRestrExp (l, UL) =
    match restriction l with
    | None -> UL
    | Some (Restr (_, _)) ->
        let owner = owner l in
        let G = ownerContext owner in
        let U = toExp (ownerSum owner) in
        (G, geq0 U) :: UL

  and restrictions pos =
    let rec member (x, l) = List.exists (fun y -> x = y) l in
    let rec test l = restricted l && not (dead l) in
    let rec reachable = function
      | pos :: candidates, tried, closure ->
          if member (pos, tried) then reachable (candidates, tried, closure)
          else
            let new_candidates =
              Array.foldl
                (fun (col, _, candidates) ->
                  if coeff (row, col) <> zero then Col col :: candidates
                  else candidates)
                []
                (clabels tableau, 0, nCols ())
            in
            let closure' =
              if test (label pos) then pos :: closure else closure
            in
            reachable (new_candidates @ candidates, pos :: tried, closure')
      | pos :: candidates, tried, closure ->
          if member (pos, tried) then reachable (candidates, tried, closure)
          else
            let candidates' =
              Array.foldl
                (fun (row, _, candidates) ->
                  if coeff (row, col) <> zero then Row row :: candidates
                  else candidates)
                []
                (rlabels tableau, 0, nRows ())
            in
            let closure' =
              if test (label pos) then pos :: closure else closure
            in
            reachable (candidates' @ candidates, pos :: tried, closure')
      | [], _, closure -> closure
    in
    let rec restrExp pos =
      let l = label pos in
      let owner = owner l in
      let G = ownerContext owner in
      let U = toExp (ownerSum owner) in
      (G, geq0 U)
    in
    List.map restrExp (reachable ([ pos ], [], []))

  and toInternal tag () =
    match findTag tag with None -> [] | Some pos -> restrictions pos

  and awake tag () =
    try
      match findTag tag with
      | Some pos ->
          let owner = owner (label pos) in
          let G = ownerContext owner in
          let sum = normalize (ownerSum owner) in
          update (G, pos, sum);
          true
      | None -> true
    with Error -> false

  and simplify tag () =
    match toInternal tag () with [] -> true | _ :: _ -> false

  and makeCnstr tag = FgnCnstr (!myID, MyFgnCnstrRep tag)

  and isIntegral () =
    let exception
      (* unbounded component *)
      Found of int
    in
    let rec find (i, (l : label)) =
      if not (dead l) then
        if denominator (const i) <> one_int then raise (Found i) else ()
      else ()
    in
    try
      Array.app find (rlabels tableau, 0, nRows ());
      None
    with Found i -> Some i

  and boundLower (G, decomp, d) =
    let W = newEVar (G, number ()) in
    let proof = newEVar (G, geq0 W) in
    let d', wPosL = unaryMinusDecomp decomp in
    let pos =
      insertDecomp ((d' + d, wPosL), Var (G, Mon (one_int, [ (W, id) ])))
    in
    (pos, Restr (G, proof))

  and boundUpper (G, decomp, d) =
    let W = newEVar (G, number ()) in
    let proof = newEVar (G, geq0 W) in
    let d', wPosL = decomp in
    let pos =
      insertDecomp ((d' - d, wPosL), Var (G, Mon (one_int, [ (W, id) ])))
    in
    (pos, Restr (G, proof))

  and exploreBB (pos, restr) =
    try
      let result = restrict (pos, restr) in
      match isIntegral () with
      | Some row -> (
          let value = const row in
          let decomp = (zero, [ (one, Row row) ]) in
          let G = ownerContext (owner (label (Row row))) in
          let lower = fromInteger (floor value) in
          let upper = fromInteger (ceiling value) in
          let rec left () = exploreBB (boundLower (G, decomp, lower)) in
          let rec right () = exploreBB (boundUpper (G, decomp, upper)) in
          match (Cs.CSM.trail left, Cs.CSM.trail right) with
          | BranchFail, BranchFail -> BranchFail
          | resultL, resultR -> BranchDivide (row, resultL, resultR))
      | None -> BranchSucceed result
    with Error -> BranchFail

  and minimizeBB row =
    (* check if the column is zero for_sml all possible solutions *)
    (* equate the given column to zero if coeff(row, j) <> zero *)
    (* find out if the given row has been made trivial by killing some columns *)
    let rec zeroColumn (j, (l : label)) =
      let decomp = (zero, [ (one, Col j) ]) in
      let G = ownerContext (owner (label (Col j))) in
      let lower = ~-one in
      let upper = one in
      let rec left () = exploreBB (boundLower (G, decomp, lower)) in
      let rec right () = exploreBB (boundUpper (G, decomp, upper)) in
      if restricted l then Cs.CSM.trail right = BranchFail
      else Cs.CSM.trail left = BranchFail && Cs.CSM.trail right = BranchFail
    in
    let rec killColumn (j, (l : label)) =
      if (not (dead l)) && coeff (row, j) <> zero && zeroColumn (j, l) then (
        (* mark the column dead *)
        Trail.log (trail tableau, Kill (Col j));
        dead (Array.sub (clabels tableau, j)) := true;
        (* if restricted, instantiate the proof object to 0>=0 *)
        (match restriction l with
        | Some restr -> unifyRestr (restr, geqNExp zero_int)
        | None -> ());
        (* if owned by a monomial, unify it with zero *)
        match owner l with
        | owner -> unifySum (ownerContext owner, ownerSum owner, zero)
        | _ -> ())
      else ()
    in
    let rec killRow (i, (l : label)) =
      if not (dead l) then
        if isConstant i then (* row is now constant and equal to n = const(i) *)
          (
          (* check if it is an integer *)
          if denominator (const i) = one_int then () else raise Error;
          (* mark the row dead *)
          Trail.log (trail tableau, Kill (Row i));
          dead (Array.sub (rlabels tableau, i)) := true;
          (* if restricted, instantiate the proof object to n>=0 *)
          (match restriction l with
          | Some restr ->
              if denominator (const i) = one_int then
                unifyRestr (restr, geqNExp (floor (const i)))
              else raise Error
          | None -> ());
          (* if owned by a monomial, unify it with n *)
          match owner l with
          | owner -> unifySum (ownerContext owner, ownerSum owner, const i)
          | _ -> ())
        else
          match isSubsumed i with
          | Some pos' -> (
              let l' = label pos' in
              Trail.log (trail tableau, Kill (Row i));
              dead (Array.sub (rlabels tableau, i)) := true;
              match (restriction l, restriction l') with
              | Some restr, Some (Restr (_, proof')) ->
                  unifyRestr (restr, proof')
              | Some _, None ->
                  (* it is safe to restrict without doing all
                                              the checks in this case, since the two rows
                                              are identical *)
                  Trail.log (trail tableau, Restrict pos');
                  restr l' := restriction l
              | None, _ -> ())
          | None -> ()
      else ()
    in
    Array.app killColumn (clabels tableau, 0, nCols ());
    Array.app killRow (rlabels tableau, 0, nRows ())

  and restrictBB result =
    match result with
    | BranchFail -> raise Error
    | BranchDivide (row, resultL, BranchFail) ->
        let value = fromInteger (floor (const row)) in
        let decomp = (zero, [ (one, Row row) ]) in
        let G = ownerContext (owner (label (Row row))) in
        let _ = restrict (boundLower (G, decomp, value)) in
        restrictBB resultL
    | BranchDivide (row, BranchFail, resultR) ->
        let value = fromInteger (ceiling (const row)) in
        let decomp = (zero, [ (one, Row row) ]) in
        let G = ownerContext (owner (label (Row row))) in
        let _ = restrict (boundUpper (G, decomp, value)) in
        restrictBB resultR
    | BranchSucceed result -> (
        match result with Some row -> minimizeBB row | None -> ())
    | _ -> ()
  (* undo function for_sml trailing tableau operations *)

  let rec undo = function
    | Insert (Row row) ->
        dead (Array.sub (rlabels tableau, row)) := true;
        clearArray2Row (coeffs tableau, row, (0, nCols ()));
        Array.update (consts tableau, row, zero);
        decrNRows ()
    | Insert (Col col) ->
        dead (Array.sub (clabels tableau, col)) := true;
        clearArray2Col (coeffs tableau, col, (0, nRows ()));
        decrNCols ()
    | Pivot (row, col) -> pivot (row, col)
    | Kill pos -> dead (label pos) := false
    | Restrict pos -> restr (label pos) := None
    | UpdateOwner (pos, owner, tag) -> setOwnership (pos, owner, tag)
  (* reset the internal status of the tableau *)

  let rec reset () =
    let l =
      {
        owner = Exp (Null, Sum (zero_int, []));
        tag = ref 0;
        restr = ref None;
        dead = ref true;
      }
    in
    Array.modify (fun _ -> l) (rlabels tableau, 0, nRows ());
    Array.modify (fun _ -> l) (clabels tableau, 0, nCols ());
    Array.modify (fun _ -> zero) (consts tableau, 0, nRows ());
    Array2.modify Array2.RowMajor
      (fun _ -> zero)
      {
        base = coeffs tableau;
        row = 0;
        col = 0;
        nrows = nRows ();
        ncols = nCols ();
      };
    nrows tableau := 0;
    ncols tableau := 0;
    Trail.reset (trail tableau)
  (* trailing functions *)

  let rec mark () = Trail.mark (trail tableau)
  let rec unwind () = Trail.unwind (trail tableau, undo)
  (* fst (S, s) = U1, the first argument in S[s] *)

  let rec fst = function
    | App (U1, _), s -> (U1, s)
    | SClo (S, s'), s -> fst (S, comp (s', s))
  (* snd (S, s) = U2, the second argument in S[s] *)

  let rec snd = function
    | App (U1, S), s -> fst (S, s)
    | SClo (S, s'), s -> snd (S, comp (s', s))
  (* checks if the given foreign term can be simplified to a constant *)

  let rec isConstantExp U =
    match fromExp (U, id) with Sum (m, []) -> Some m | _ -> None
  (* checks if the given foreign term can be simplified to zero *)

  let rec isZeroExp U =
    match isConstantExp U with Some d -> d = zero_int | None -> false
  (* solveGeq (G, S, n) tries to find the n-th solution to G |- '>=' @ S : type *)

  let rec solveGeq = function
    | G, S, 0 -> (
        let rec solveGeq0 W =
          match isConstantExp W with
          | Some d ->
              if (Integers).>=(d, zero_int) then geqNExp d else raise Error
          | None ->
              let proof = newEVar (G, geq0 W) in
              let _ =
                restrictBB (exploreBB (insert (G, (W, id)), Restr (G, proof)))
              in
              proof
        in
        let U1 = EClo (fst (S, id)) in
        let U2 = EClo (snd (S, id)) in
        try
          if isZeroExp U2 then Some (solveGeq0 U1)
          else
            let W = minus (U1, U2) in
            let proof = solveGeq0 W in
            Some (geqAdd (W, constant zero_int, U2, proof))
        with Error -> None)
    | G, S, n -> None
  (* constructors for_sml higher-order types *)

  let rec pi (name, U, V) = Pi ((Dec (Some name, U), Maybe), V)
  let rec arrow (U, V) = Pi ((Dec (None, U), No), V)

  let rec installFgnCnstrOps () =
    let csid = !myID in
    let _ =
      FgnCnstrStd.ToInternal.install
        ( csid,
          function
          | MyFgnCnstrRep tag -> toInternal tag
          | fc -> raise (UnexpectedFgnCnstr fc) )
    in
    let _ =
      FgnCnstrStd.Awake.install
        ( csid,
          function
          | MyFgnCnstrRep tag -> awake tag
          | fc -> raise (UnexpectedFgnCnstr fc) )
    in
    let _ =
      FgnCnstrStd.Simplify.install
        ( csid,
          function
          | MyFgnCnstrRep tag -> simplify tag
          | fc -> raise (UnexpectedFgnCnstr fc) )
    in
    ()
  (* install the signature *)

  let rec init (cs, installF) =
    myID := cs;
    geqID :=
      installF
        ( ConDec
            ( ">=",
              None,
              0,
              Constraint (!myID, solveGeq),
              arrow (number (), arrow (number (), Uni Type)),
              Kind ),
          Some (FX.Infix (FX.minPrec, FX.None)),
          [
            MS.Mapp
              ( MS.Marg (MS.Star, None),
                MS.Mapp (MS.Marg (MS.Star, None), MS.Mnil) );
          ] );
    geqAddID :=
      installF
        ( ConDec
            ( "+>=",
              None,
              2,
              Normal,
              pi
                ( "X",
                  number (),
                  pi
                    ( "Y",
                      number (),
                      pi
                        ( "Z",
                          number (),
                          arrow
                            ( geq (Root (BVar 3, Nil), Root (BVar 2, Nil)),
                              geq
                                ( plus (Root (BVar 4, Nil), Root (BVar 2, Nil)),
                                  plus (Root (BVar 3, Nil), Root (BVar 2, Nil))
                                ) ) ) ) ),
              Type ),
          None,
          [] );
    installFgnCnstrOps ();
    ()

  let solver =
    ({
       name = "inequality/integers";
       keywords = "arithmetic,inequality";
       needs = [ "Unify"; name Cs.CSEqIntegers.solver ];
       fgnConst = Some { parse = parseGeqN };
       init;
       reset;
       mark;
       unwind;
     }
      : Cs.CSManager.solver)
end

(* functor Cs.CSIneqIntegers *)
