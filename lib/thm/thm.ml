(* Theorem and Related Declarations *)

(* Author: Carsten Schuermann *)

(* Modified: Brigitte Pientka *)

module Thm
    (Global : GLOBAL)
    (ThmSyn' : THMSYN)
    (TabledSyn : TABLEDSYN)
    (ModeTable : MODETABLE)
    (Order : ORDER)
    (ThmPrint : THMPRINT) : THM = struct
  module ThmSyn = ThmSyn'
  (*! structure Paths = Paths' !*)

  module TabledSyn = TabledSyn
  (* -bp *)

  type order = Varg | Lex of order list | Simul of order list

  exception Error of string

  module L = ThmSyn
  module M = ModeSyn
  (* L.ModeSyn *)

  module I = IntSyn
  module P = ThmPrint
  module O = Order

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
  (* To check validity of a termination declaration  O C
       we enforce that all variable names which occur in C must be distinct
       and if C = C1 .. Cm then we ensure that for_sml all Varg (X1 .. Xn) in O,

           1) n = m
       and 2) each Ci contains an occurrence of Xi
    *)

  (* unique (((a, P), r), A) = A'

       Invariant:
       If   A is a list of variables already collected in a call pattern
       and  P does not contain any variables in A
       then A' = A, Var (P)
       else exception Error is raised.
       (r is region information for_sml error message)
    *)

  let rec unique (((a, P), r), A) =
    let rec unique' = function
      | I.Uni _, [], A -> A
      | I.Pi (_, V), None :: P, A -> unique' (V, P, A)
      | I.Pi (_, V), Some x :: P, A ->
          List.app
            (fun x' ->
              if x = x' then error (r, "Variable " ^ x ^ " used more than once")
              else ())
            A;
          unique' (V, P, x :: A)
      | I.Uni _, _, _ ->
          error
            ( r,
              "Too many arguments supplied to type family "
              ^ Names.qidToString (Names.constQid a) )
      | I.Pi (_, V), [], _ ->
          error
            ( r,
              "Too few arguments supplied to type family "
              ^ Names.qidToString (Names.constQid a) )
      | I.Root _, _, _ ->
          error
            ( r,
              "Constant "
              ^ Names.qidToString (Names.constQid a)
              ^ " is an object, not a type family" )
    in
    let rec skip = function
      | 0, V, P, A -> unique' (V, P, A)
      | k, I.Pi (_, V), P, A -> skip (k - 1, V, P, A)
    in
    skip (I.constImp a, I.constType a, P, A)
  (* uniqueCallpats (L, rs) = ()

       Invariant:
       If   L is a callpattern
       and  each variable in L is unique
       then uniqueCallpats returns ()
       else exception Error is raised.

       (rs is a list of region information for_sml error message,
       each region corresponds to one type in the call pattern,
       in order)
    *)

  let rec uniqueCallpats (L, rs) =
    let rec uniqueCallpats' = function
      | ([], []), A -> ()
      | (aP :: L, r :: rs), A -> uniqueCallpats' ((L, rs), unique ((aP, r), A))
    in
    uniqueCallpats' ((L, rs), [])
  (* wfCallpats (L, C, r) = ()

       Invariant:
       If   L is a list of variable names of a virtual argument
       and  C is a call pattern, the predicate in C has a mode
       then wfCallpats terminates with () if
            1) there many call variable names
            2) each variable name occurs in a different call pattern
       else exception Error is raised
       (r region information, needed for_sml error messages)
    *)

  let rec wfCallpats (L0, C0, r) =
    (* skip (i, x, P, mS)  ignores first i argument in modeSpine mS,
             then returns true iff x occurs in argument list P
             Effect: raises Error if position of x is not input (+).
          *)
    let rec makestring = function
      | [] -> ""
      | s :: [] -> s
      | s :: L -> s ^ " " ^ makestring L
    in
    let rec exists' = function
      | x, [], _ -> false
      | x, None :: L, M.Mapp (_, mS) -> exists' (x, L, mS)
      | x, Some y :: L, M.Mapp (M.Marg (mode, _), mS) ->
          if x = y then
            match mode with
            | M.Plus -> true
            | _ ->
                error
                  ( r,
                    "Expected " ^ x ^ " to have " ^ M.modeToString M.Plus
                    ^ " mode" )
          else exists' (x, L, mS)
    in
    let rec skip = function
      | 0, x, P, mS -> exists' (x, P, mS)
      | k, x, P, M.Mapp (_, mS) -> skip (k - 1, x, P, mS)
    in
    let rec delete = function
      | x, aP :: C ->
          if
            skip (I.constImp a, x, P, valOf (ModeTable.modeLookup a))
            (* exists by invariant *)
          then C
          else aP :: delete (x, C)
      | x, [] -> error (r, "Variable " ^ x ^ " does not argument")
    in
    let rec wfCallpats' = function
      | [], [] -> ()
      | x :: L, C -> wfCallpats' (L, delete (x, C))
      | _ ->
          error
            ( r,
              "Mutual argument (" ^ makestring L0
              ^ ") does not cover all call patterns" )
    in
    wfCallpats' (L0, C0)
  (* wf ((O, C), (r, rs)) = ()

       Invariant:
       If   O is an order
       and  C is a call pattern
       then wf terminates with ()
            if C contains pairwise different variable names
            and each virtual argument in O covers all call patterns.
       else exception Error is raised
       (r, rs  region information, needed for_sml error messages)
    *)

  let rec wf ((O, L.Callpats C), (r, rs)) =
    let rec wfOrder = function
      | L.Varg L -> wfCallpats (L, C, r)
      | L.Lex L -> wfOrders L
      | L.Simul L -> wfOrders L
    and wfOrders = function
      | [] -> ()
      | O :: L ->
          wfOrder O;
          wfOrders L
    in
    let rec allModed = function
      | [] -> ()
      | (a, P) :: Cs -> (
          match ModeTable.modeLookup a with
          | None ->
              error
                ( r,
                  "Expected "
                  ^ Names.qidToString (Names.constQid a)
                  ^ " to be moded" )
          | Some mS ->
              ();
              allModed Cs)
    in
    allModed C;
    uniqueCallpats (C, rs);
    wfOrder O
  (* argPos (x, L, n) = nOpt

       Invariant:
       If   x is a variable name
       and  L is a list of argument for_sml a call pattern
       and  n is the position of the first argument name in L
            in the call pattern
       then nOpt describes the optional  position of the occurrence
    *)

  let rec argPos = function
    | x, [], n -> None
    | x, None :: L, n -> argPos (x, L, n + 1)
    | x, Some x' :: L, n -> if x = x' then Some n else argPos (x, L, n + 1)
  (* locate (L, P, n) = n'

       Invariant:
       If   L is a list of variable names (as part of a virtual argument)
       and  P is an argument list (from a call pattern)
       and  n is the position of the first argument name in P
            in the call pattern
       then n' describes the position of the virtual argument in P
    *)

  let rec locate (x :: vars, params, imp) =
    match argPos (x, params, imp + 1) with
    | None -> locate (vars, params, imp)
    | Some n -> n
  (* locate nil cannot occur by invariant *)

  (* argOrder (O, P, n) = O'

       Invariant:
       If   O is an order
       and  P is the argument spine of a call pattern
       and  n is the number of implicit arguments of the
                 call pattern
       then O' is an order where all virtual arguments are
                  replaced by positions

    *)

  let rec argOrder = function
    | L.Varg L, P, n -> O.Arg (locate (L, P, n))
    | L.Simul L, P, n -> O.Simul (argOrderL (L, P, n))
    | L.Lex L, P, n -> O.Lex (argOrderL (L, P, n))

  and argOrderL = function
    | [], P, n -> []
    | O :: L, P, n -> argOrder (O, P, n) :: argOrderL (L, P, n)
  (*  argOrderMutual (C, k, A) = A'

        Invariant:

        If   C is a list of call patterns
        and  k is a function, mapping a call patterns to 'a
        and  A is an acculmulator for_sml objects of type 'a
        then A' is an accumulator extending A containing all
             images of C under k.
    *)

  let rec argOrderMutual = function
    | [], k, A -> A
    | P :: L, k, A -> argOrderMutual (L, k, k (P, A))
  (* installorder (O, LE, LT) = ()

       Invariant:
       If   O is an order,
       and  LE is a list of callpatterns where ind. argument must LT decrease
       and  LT is a list of callpatterns where ind. argument must LE decrease
       then installorder terminates with ()

       Effect: updates table associating argument order with type families.
    *)

  let rec installOrder = function
    | _, [], _ -> ()
    | O, aP :: thmsLE, thmsLT ->
        let M' =
          argOrderMutual
            ( thmsLE,
              fun ((a, _), L) ->
                ( O.LE (a, L),
                  argOrderMutual
                    (aP :: thmsLT, fun ((a, _), L) -> (O.LT (a, L), O.Empty)) )
            )
        in
        let O' = argOrder (O, P, I.constImp a) in
        let S' = O.install (a, O.TDec (O', M')) in
        installOrder (O, thmsLE, aP :: thmsLT)
  (* installDecl (O, C) = L'

       Invariant:
       If   O is an order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C

       Effect: All orders are stored
    *)

  let rec installDecl (O, L.Callpats L) =
    installOrder (O, L, []);
    map (fun (a, _) -> a) L
  (* installTerminates (T, (r,rs)) = L'

       Invariant:
       If   T is a termination declaration of (O, C)
       and  O is an order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C
            if (O, C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for_sml error messages)
    *)

  let rec installTerminates (L.TDecl T, rrs) =
    wf (T, rrs);
    installDecl T

  let rec uninstallTerminates cid = O.uninstall cid
  (* installTotal (T, (r, rs)) = L'
       in installTerminates
    *)

  let rec installTotal (L.TDecl T, rrs) =
    wf (T, rrs);
    installDecl T

  let rec uninstallTotal cid = O.uninstall cid
  (* -bp *)

  (* argROrder (O, P, n) = O'

       Invariant:
       If   O is an order
       and  P is the argument spine of a call pattern
       and  n is the number of implicit arguments of the
                 call pattern
       then O' is an order where all virtual arguments are
                  replaced by positions

    *)

  let rec argROrder = function
    | L.Varg L, P, n -> O.Arg (locate (L, P, n))
    | L.Simul L, P, n -> O.Simul (argROrderL (L, P, n))
    | L.Lex L, P, n -> O.Lex (argROrderL (L, P, n))

  and argROrderL = function
    | [], P, n -> []
    | O :: L, P, n -> argROrder (O, P, n) :: argROrderL (L, P, n)

  let rec argPredicate = function
    | L.Less, O, O' -> O.Less (O, O')
    | L.Leq, O, O' -> O.Leq (O, O')
    | L.Eq, O, O' -> O.Eq (O, O')
  (* installPredicate (name, R, LE, LT) = ()

       Invariant:
       If   R is a reduction order,
       and  LE is a list of callpatterns where ind. argument must LT decrease
       and  LT is a list of callpatterns where ind. argument must LE decrease
       then installorder terminates with ()

       Effect: updates table associating argument reduction order with
               type families.

    *)

  let rec installPredicate = function
    | _, [], _ -> ()
    | L.RedOrder (Pred, O1, O2), aP :: thmsLE, thmsLT ->
        (* install termination order *)
        (* bug: %reduces should not entail %terminates *)
        (* fixed: Sun Mar 13 09:41:18 2005 -fp *)
        (* val S'  = O.install (a, O.TDec (O2', M')) *)
        (* install reduction order   *)
        let M' =
          argOrderMutual
            ( thmsLE,
              fun ((a, _), L) ->
                ( O.LE (a, L),
                  argOrderMutual
                    (aP :: thmsLT, fun ((a, _), L) -> (O.LT (a, L), O.Empty)) )
            )
        in
        let O1' = argROrder (O1, P, I.constImp a) in
        let O2' = argROrder (O2, P, I.constImp a) in
        let pr = argPredicate (Pred, O1', O2') in
        let S'' = O.installROrder (a, O.RDec (pr, M')) in
        installPredicate (L.RedOrder (Pred, O1, O2), thmsLE, aP :: thmsLT)
  (* installRDecl (R, C) = L'

       Invariant:
       If   R is a reduction order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C

       Effect: reduction order is stored
    *)

  let rec installRDecl (R, L.Callpats L) =
    installPredicate (R, L, []);
    map (fun (a, _) -> a) L
  (* wfRCallpats
       well-formed call pattern in a reduction declaration
       pattern does not need to be moded
       Tue Apr 30 10:32:31 2002 -bp
     *)

  let rec wfRCallpats (L0, C0, r) =
    let rec makestring = function
      | [] -> ""
      | s :: [] -> s
      | s :: L -> s ^ " " ^ makestring L
    in
    let rec exists' = function
      | x, [] -> false
      | x, None :: L -> exists' (x, L)
      | x, Some y :: L -> if x = y then true else exists' (x, L)
    in
    let rec delete = function
      | x, aP :: C -> if exists' (x, P) then C else aP :: delete (x, C)
      | x, [] -> error (r, "Variable " ^ x ^ " does not argument")
    in
    let rec wfCallpats' = function
      | [], [] -> ()
      | x :: L, C -> wfCallpats' (L, delete (x, C))
      | _ ->
          error
            ( r,
              "Mutual argument (" ^ makestring L0
              ^ ") does not cover all call patterns" )
    in
    wfCallpats' (L0, C0)
  (* wfred ((Red(Pred,O.O'), C), (r, rs)) = ()

       Invariant:
       If   O,O' is an order and Pred is some predicate
       and  C is a call pattern
       then wfred terminates with ()
            if C contains pairwise different variable names
            and each virtual argument in O covers all call patterns.
       else exception Error is raised
       (r, rs  region information, needed for_sml error messages)
    *)

  let rec wfred ((L.RedOrder (Pred, O, O'), L.Callpats C), (r, rs)) =
    let rec wfOrder = function
      | L.Varg L ->
          wfRCallpats (L, C, r);
          Varg
      | L.Lex L -> Lex (wfOrders L)
      | L.Simul L -> Simul (wfOrders L)
    and wfOrders = function [] -> [] | O :: L -> wfOrder O :: wfOrders L in
    uniqueCallpats (C, rs);
    if wfOrder O = wfOrder O' then ()
    else
      error
        ( r,
          "Reduction Order ("
          ^ P.rOrderToString (L.RedOrder (Pred, O, O'))
          ^ ") requires both orders to be of the same type." )
  (* installRedOrder (R, (r,rs)) = L'

       Invariant:
       If   R is a reduction declaration of (pred(O,O'), C)
       and  O,O' is an order
       and pred is a predicate
       and  C is a call pattern
       then L' is a list of all type families mentioned in C
            if (pred(O,O'), C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for_sml error messages)
    *)

  let rec installReduces (L.RDecl (R, C), rrs) =
    wfred ((R, C), rrs);
    installRDecl (R, C)

  let rec uninstallReduces cid = O.uninstallROrder cid
  let rec installTabled (L.TabledDecl cid) = TabledSyn.installTabled cid

  let rec installKeepTable (L.KeepTableDecl cid) =
    TabledSyn.installKeepTable cid

  let installTotal = installTotal
  let uninstallTotal = uninstallTotal
  let installTerminates = installTerminates
  let uninstallTerminates = uninstallTerminates
  let installReduces = installReduces
  let uninstallReduces = uninstallReduces
  let installTabled = installTabled
  let installKeepTable = installKeepTable
  (* local *)
end

(* functor Thm *)
