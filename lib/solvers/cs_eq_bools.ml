(* Booleans Equation Solver *)

(* Author: Roberto Virga *)

module CSEqBools (Whnf : Whnf.WHNF) (Unify : Unify.UNIFY) : Cs.CS = struct
  (*! structure Cs.CSManager = Cs.CSManager !*)

  (*! structure IntSyn = IntSyn !*)

  type 'a set = 'a list
  (* Set                        *)

  type sum = Sum of bool * mon set
  and mon = Mon of IntSyn.exp * IntSyn.sub set
  (* Mon ::= U1[s1] * ...       *)

  (* A monomial (U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum;
       (b) the terms Ui[si] are pairwise distinct.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)

  open IntSyn
  module FX = Cs.CSManagerFixity
  module MS = ModeSyn
  (* Cs.CSManager.ModeSyn *)

  exception MyIntsynRep of sum

  let rec extractSum = function
    | MyIntsynRep sum -> sum
    | fe -> raise (UnexpectedFgnExp fe)

  let myID = (ref - 1 : csid ref)
  let boolID = (ref - 1 : cid ref)
  let rec bool () = Root (Const !boolID, Nil)
  let trueID = (ref - 1 : cid ref)
  let falseID = (ref - 1 : cid ref)
  let rec trueExp () = Root (Const !trueID, Nil)
  let rec falseExp () = Root (Const !falseID, Nil)

  let rec solveBool = function
    | G, S, 0 -> Some (trueExp ())
    | G, S, 1 -> Some (falseExp ())
    | G, S, k -> None

  let notID = (ref - 1 : cid ref)
  let xorID = (ref - 1 : cid ref)
  let andID = (ref - 1 : cid ref)
  let orID = (ref - 1 : cid ref)
  let impliesID = (ref - 1 : cid ref)
  let iffID = (ref - 1 : cid ref)
  let rec notExp U = Root (Const !notID, App (U, Nil))
  let rec xorExp (U, V) = Root (Const !xorID, App (U, App (V, Nil)))
  let rec andExp (U, V) = Root (Const !andID, App (U, App (V, Nil)))
  let rec orExp (U, V) = Root (Const !orID, App (U, App (V, Nil)))
  let rec impliesExp (U, V) = Root (Const !impliesID, App (U, App (V, Nil)))
  let rec iffExp (U, V) = Root (Const !iffID, App (U, App (V, Nil)))
  (* member eq (x, L) = true iff there there is a y in L s.t. eq(y, x) *)

  let rec member eq (x, L) = List.exists (fun y -> eq (x, y)) L
  (* differenceSet eq L1 L2 = (L1 \ L2) U (L2 \ L1) *)

  let rec differenceSet eq (L1, L2) =
    let L1' = List.filter (fun x -> not (member eq (x, L2))) L1 in
    let L2' = List.filter (fun x -> not (member eq (x, L1))) L2 in
    L1' @ L2'
  (* equalSet eq (L1, L2) = true iff L1 is equal to L2 (both sets) *)

  let rec equalSet eq (L1, L2) =
    match differenceSet eq (L1, L2) with [] -> true | _ :: _ -> false
  (* unionSet eq (L1, L2) = L1 U L2 *)

  let rec unionSet eq (L1, L2) =
    let L2' = List.filter (fun x -> not (member eq (x, L1))) L2 in
    L1 @ L2'
  (* toExp sum = U

       Invariant:
       If sum is normal
       G |- U : V and U is the Twelf syntax conversion of sum
    *)

  let rec toExp = function
    | Sum (m, []) ->
        let cid = if m then !trueID else !falseID in
        Root (Const cid, Nil)
    | Sum (m, [ mon ]) ->
        if m = false then toExpMon mon
        else xorExp (toExp (Sum (m, [])), toExpMon mon)
    | Sum (m, monLL) -> xorExp (toExp (Sum (m, monL)), toExpMon mon)

  and toExpMon = function
    | Mon [ Us ] -> toExpEClo Us
    | Mon (Us :: UsL) -> andExp (toExpMon (Mon UsL), toExpEClo Us)

  and toExpEClo = function U, Shift 0 -> U | Us -> EClo Us
  (* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *)

  let rec compatibleMon (Mon UsL1, Mon UsL2) =
    equalSet (fun (Us1, Us2) -> sameExp (Us1, Us2)) (UsL1, UsL2)

  and sameExpW = function
    | Us1, Us2 -> (
        match (H1, H2) with
        | BVar k1, BVar k2 -> k1 = k2 && sameSpine ((S1, s1), (S2, s2))
        | FVar (n1, _, _), FVar (n2, _, _) ->
            n1 = n2 && sameSpine ((S1, s1), (S2, s2))
        | _ -> false)
    | Us1, Us2 -> r1 = r2 && sameSub (s1, s2)
    | _ -> false

  and sameExp (Us1, Us2) = sameExpW (Whnf.whnf Us1, Whnf.whnf Us2)

  and sameSpine = function
    | (Nil, s1), (Nil, s2) -> true
    | (SClo (S1, s1'), s1), Ss2 -> sameSpine ((S1, comp (s1', s1)), Ss2)
    | Ss1, (SClo (S2, s2'), s2) -> sameSpine (Ss1, (S2, comp (s2', s2)))
    | (App (U1, S1), s1), (App (U2, S2), s2) ->
        sameExp ((U1, s1), (U2, s2)) && sameSpine ((S1, s1), (S2, s2))
    | _ -> false

  and sameSub = function
    | Shift _, Shift _ -> true
    | Dot (Idx k1, s1), Dot (Idx k2, s2) -> k1 = k2 && sameSub (s1, s2)
    | s1, Shift k2 ->
        sameSub (s1, Dot (Idx (Int).+(k2, 1), Shift (Int).+(k2, 1)))
    | Shift k1, s2 ->
        sameSub (Dot (Idx (Int).+(k1, 1), Shift (Int).+(k1, 1)), s2)
    | _ -> false
  (* xorSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 xor sum2
    *)

  let rec xorSum (Sum (m1, monL1), Sum (m2, monL2)) =
    Sum (not (m1 = m2), differenceSet compatibleMon (monL1, monL2))
  (* andSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 and sum2
    *)

  let rec andSum = function
    | sum1, sum2 -> sum1
    | sum1, sum2 -> sum2
    | sum1, sum2 -> sum2
    | sum1, sum2 -> sum1
    | Sum (m1, mon1 :: monL1), sum2 ->
        xorSum (andSumMon (sum2, mon1), andSum (Sum (m1, monL1), sum2))

  and andSumMon = function
    | Sum (true, []), mon -> Sum (false, [ mon ])
    | sum1, mon -> sum1
    | Sum (m1, Mon UsL1 :: monL1), mon2 ->
        let UsL = unionSet sameExp (UsL1, UsL2) in
        xorSum (Sum (false, [ Mon UsL ]), andSumMon (Sum (m1, monL1), mon2))
  (* notSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = not sum
    *)

  let rec notSum (Sum (m, monL)) = Sum (not m, monL)
  (* orSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 or sum2
    *)

  let rec orSum (sum1, sum2) = xorSum (sum1, xorSum (sum2, andSum (sum1, sum2)))
  (* impliesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 implies sum2
    *)

  let rec impliesSum (sum1, sum2) = notSum (xorSum (sum1, andSum (sum1, sum2)))
  (* iffSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 iff sum2
    *)

  let rec iffSum (sum1, sum2) = notSum (xorSum (sum1, sum2))
  (* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)

  let rec fromExpW = function
    | Us ->
        if cs = !myID then normalizeSum (extractSum fe)
        else Sum (false, [ Mon [ Us ] ])
    | Us -> Sum (false, [ Mon [ Us ] ])

  and fromExp Us = fromExpW (Whnf.whnf Us)

  and normalizeSum = function
    | sum -> sum
    | Sum (m, [ mon ]) -> xorSum (Sum (m, []), normalizeMon mon)
    | Sum (m, mon :: monL) ->
        xorSum (normalizeMon mon, normalizeSum (Sum (m, monL)))

  and normalizeMon = function
    | Mon [ Us ] -> fromExp Us
    | Mon (Us :: UsL) -> andSum (fromExp Us, normalizeMon (Mon UsL))

  and mapSum (f, Sum (m, monL)) =
    Sum (m, List.map (fun mon -> mapMon (f, mon)) monL)

  and mapMon (f, Mon UsL) =
    Mon (List.map (fun Us -> Whnf.whnf (f (EClo Us), id)) UsL)
  (* appSum (f, m + M1 + ...) = ()     and appMon (f, Mi) for_sml each i *)

  let rec appSum (f, Sum (m, monL)) = List.app (fun mon -> appMon (f, mon)) monL
  and appMon (f, Mon UsL) = List.app (fun Us -> f (EClo Us)) UsL
  (* findMon f (G, sum) =
         SOME(x) if f(M) = SOME(x) for_sml some monomial M in sum
         NONE    if f(M) = NONE for_sml all monomials M in sum
    *)

  let rec findMon f (G, Sum (m, monL)) =
    let rec findMon' = function
      | [], monL2 -> None
      | mon :: monL1, monL2 -> (
          match f (G, mon, Sum (m, monL1 @ monL2)) with
          | result -> result
          | None -> findMon' (monL1, mon :: monL2))
    in
    findMon' (monL, [])
  (* unifySum (G, sum1, sum2) = result

       Invariant:
       If   G |- sum1 : number     sum1 normal
       and  G |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by gaussian elimination.
    *)

  let rec unifySum (G, sum1, sum2) =
    let rec invertMon = function
      | G, Mon [ (LHS, s) ], sum ->
          if Whnf.isPatSub s then
            let ss = Whnf.invert s in
            let RHS = toFgn sum in
            if Unify.invertible (G, (RHS, id), ss, r) then Some (G, LHS, RHS, ss)
            else None
          else None
      | _ -> None
    in
    match xorSum (sum2, sum1) with
    | Sum (false, []) -> Succeed []
    | Sum (true, []) -> Fail
    | sum -> (
        match findMon invertMon (G, sum) with
        | Some assignment -> Succeed [ Assign assignment ]
        | None ->
            let U = toFgn sum in
            let cnstr = ref (Eqn (G, U, falseExp ())) in
            Succeed [ Delay (U, cnstr) ])

  and toFgn = function
    | sum -> toExp sum
    | sum -> FgnExp (!myID, MyIntsynRep sum)
  (* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep sum) and sum : normal
       then U is the Twelf syntax conversion of sum
    *)

  let rec toInternal = function
    | MyIntsynRep sum, () -> toExp (normalizeSum sum)
    | fe, () -> raise (UnexpectedFgnExp fe)
  (* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep sum)   sum : normal
       and
         f sum = f (m + mon1 + ... + monN) =
               = m + f (m1 * Us1 * ... * UsM) + ...
               = m + (m1 * (f Us1) * ... * f (UsM))
               = sum'           sum' : normal
       then
         U' is a foreign expression representing sum'
    *)

  let rec map = function
    | MyIntsynRep sum, f -> toFgn (normalizeSum (mapSum (f, sum)))
    | fe, _ -> raise (UnexpectedFgnExp fe)
  (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep sum)     sum : normal
       and
          sum = m + mon1 + ... monN
          where moni = mi * Usi1 * ... UsiMi
       then f is applied to each Usij
         (since sum : normal, each Usij is in whnf)
    *)

  let rec app = function
    | MyIntsynRep sum, f -> appSum (f, sum)
    | fe, _ -> raise (UnexpectedFgnExp fe)

  let rec equalTo = function
    | MyIntsynRep sum, U2 -> (
        match
          xorSum (normalizeSum sum, fromExp (U2, id))
          (* AK: redundant normalizeSum ? *)
        with
        | Sum (m, []) -> m = false
        | _ -> false)
    | fe, _ -> raise (UnexpectedFgnExp fe)

  let rec unifyWith = function
    | MyIntsynRep sum, (G, U2) ->
        unifySum (G, normalizeSum sum, fromExp (U2, id))
    | fe, _ -> raise (UnexpectedFgnExp fe)

  let rec installFgnExpOps () =
    let csid = !myID in
    let _ = FgnExpStd.ToInternal.install (csid, toInternal) in
    let _ = FgnExpStd.Map.install (csid, map) in
    let _ = FgnExpStd.App.install (csid, app) in
    let _ = FgnExpStd.UnifyWith.install (csid, unifyWith) in
    let _ = FgnExpStd.EqualTo.install (csid, equalTo) in
    ()

  let rec makeFgn (arity, opExp) S =
    let rec makeParams = function
      | 0 -> Nil
      | n -> App (Root (BVar n, Nil), makeParams (Int).-(n, 1))
    in
    let rec makeLam = function
      | E, 0 -> E
      | E, n -> Lam (Dec (None, bool ()), makeLam E (Int).-(n, 1))
    in
    let rec expand = function
      | (Nil, s), arity -> (makeParams arity, arity)
      | (App (U, S), s), arity ->
          let S', arity' = expand ((S, s), (Int).-(arity, 1)) in
          (App (EClo (U, comp (s, Shift arity')), S'), arity')
      | (SClo (S, s'), s), arity -> expand ((S, comp (s', s)), arity)
    in
    let S', arity' = expand ((S, id), arity) in
    makeLam (toFgn (opExp S')) arity'

  let rec makeFgnUnary opSum =
    makeFgn (1, fun (App (U, Nil)) -> opSum (fromExp (U, id)))

  let rec makeFgnBinary opSum =
    makeFgn
      ( 2,
        fun (App (U1, App (U2, Nil))) ->
          opSum (fromExp (U1, id), fromExp (U2, id)) )

  let rec arrow (U, V) = Pi ((Dec (None, U), No), V)
  (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)

  let rec init (cs, installF) =
    myID := cs;
    boolID :=
      installF
        ( ConDec ("bool", None, 0, Constraint (!myID, solveBool), Uni Type, Kind),
          None,
          [ MS.Mnil ] );
    trueID :=
      installF
        ( ConDec
            ( "true",
              None,
              0,
              Foreign (!myID, fun _ -> toFgn (Sum (true, []))),
              bool (),
              Type ),
          None,
          [] );
    falseID :=
      installF
        ( ConDec
            ( "false",
              None,
              0,
              Foreign (!myID, fun _ -> toFgn (Sum (false, []))),
              bool (),
              Type ),
          None,
          [] );
    notID :=
      installF
        ( ConDec
            ( "!",
              None,
              0,
              Foreign (!myID, makeFgnUnary notSum),
              arrow (bool (), bool ()),
              Type ),
          Some (FX.Prefix FX.maxPrec),
          [] );
    xorID :=
      installF
        ( ConDec
            ( "||",
              None,
              0,
              Foreign (!myID, makeFgnBinary xorSum),
              arrow (bool (), arrow (bool (), bool ())),
              Type ),
          Some (FX.Infix (FX.dec FX.maxPrec, FX.Left)),
          [] );
    andID :=
      installF
        ( ConDec
            ( "&",
              None,
              0,
              Foreign (!myID, makeFgnBinary andSum),
              arrow (bool (), arrow (bool (), bool ())),
              Type ),
          Some (FX.Infix (FX.dec FX.maxPrec, FX.Left)),
          [] );
    orID :=
      installF
        ( ConDec
            ( "|",
              None,
              0,
              Foreign (!myID, makeFgnBinary orSum),
              arrow (bool (), arrow (bool (), bool ())),
              Type ),
          Some (FX.Infix (FX.dec FX.maxPrec, FX.Left)),
          [] );
    impliesID :=
      installF
        ( ConDec
            ( "=>",
              None,
              0,
              Foreign (!myID, makeFgnBinary impliesSum),
              arrow (bool (), arrow (bool (), bool ())),
              Type ),
          Some (FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
          [] );
    iffID :=
      installF
        ( ConDec
            ( "<=>",
              None,
              0,
              Foreign (!myID, makeFgnBinary iffSum),
              arrow (bool (), arrow (bool (), bool ())),
              Type ),
          Some (FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
          [] );
    installFgnExpOps ();
    ()

  let solver =
    {
      name = "equality/booleans";
      keywords = "booleans,equality";
      needs = [ "Unify" ];
      fgnConst = None;
      init;
      reset = (fun () -> ());
      mark = (fun () -> ());
      unwind = (fun () -> ());
    }
end

(* functor Cs.CSEqBools *)
