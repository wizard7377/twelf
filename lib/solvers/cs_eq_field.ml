open Basis ;; 
(* Gaussian-Elimination Equation Solver *)

(* Author: Roberto Virga *)

module type CS_EQ_FIELD = sig
  include Cs.CS
  module Field : Field.FIELD

  (*! structure IntSyn : Intsyn.INTSYN !*)
  (* Foreign expressions *)
  type 'a mset = 'a list

  (* MultiSet                   *)
  type sum = Sum of Field.number * mon mset
  and mon = Mon of Field.number * IntSyn.exp * IntSyn.sub mset

  (* Mon ::= n * U1[s1] * ...   *)
  val fromExp : IntSyn.eclo -> sum
  val toExp : sum -> IntSyn.exp
  val normalize : sum -> sum
  val compatibleMon : mon * mon -> bool

  (* Internal expressions constructors *)
  val number : unit -> IntSyn.exp
  val unaryMinus : IntSyn.exp -> IntSyn.exp
  val plus : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val minus : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val times : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val constant : Field.number -> IntSyn.exp
end

(* signature Cs.CS_EQ_FIELD *)
(* Gaussian-Elimination Equation Solver *)

(* Author: Roberto Virga *)

module CSEqField
    (Field : Field.FIELD)
    (Whnf : Whnf.WHNF)
    (Unify : Unify.UNIFY) : Cs.CS_EQ_FIELD = struct
  (*! structure Cs.CSManager = Cs.CSManager !*)

  module Field = Field
  (*! structure IntSyn = IntSyn !*)

  type 'a mset = 'a list
  (* MultiSet                   *)

  type sum = Sum of Field.number * mon mset
  and mon = Mon of Field.number * IntSyn.exp * IntSyn.sub mset
  (* Mon ::= n * U1[s1] * ...   *)

  (* A monomial (n * U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) the coefficient n is different from zero;
       (b) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)

  open IntSyn
  open Field
  module FX = Cs.CSManagerFixity
  module MS = ModeSyn
  (* Cs.CSManager.ModeSyn *)

  exception MyIntsynRep of sum
  (* FgnExp representation for_sml this domain *)

  let rec extractSum = function
    | MyIntsynRep sum -> sum
    | fe -> raise (UnexpectedFgnExp fe)
  (* constraint solver ID of this module *)

  let myID = (ref - 1 : csid ref)
  (* constant ID of the type family constant "number" *)

  let numberID = (ref - 1 : cid ref)
  let rec number () = Root (Const !numberID, Nil)
  (* constant ID's of the object constants defined by this module *)

  let unaryMinusID = (ref - 1 : cid ref)
  (* ~ : number -> number           *)

  let plusID = (ref - 1 : cid ref)
  (* + : number -> number -> number *)

  let minusID = (ref - 1 : cid ref)
  (* - : number -> number -> number *)

  let timesID = (ref - 1 : cid ref)
  (* * : number -> number -> number *)

  let rec unaryMinusExp U = Root (Const !unaryMinusID, App (U, Nil))
  let rec plusExp U V = Root (Const !plusID, App (U, App (V, Nil)))
  let rec minusExp U V = Root (Const !minusID, App (U, App (V, Nil)))
  let rec timesExp U V = Root (Const !timesID, App (U, App (V, Nil)))
  let rec numberConDec d = ConDec (toString d, None, 0, Normal, number (), Type)
  let rec numberExp d = Root (FgnConst (!myID, numberConDec d), Nil)
  (* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)

  let rec parseNumber string =
    match fromString string with
    | Some d -> Some (numberConDec d)
    | None -> None
  (* solveNumber k = SOME(U)

       Invariant:
       U is the term obtained applying the foreign constant
       corresponding to the number k to an empty spine
    *)

  let rec solveNumber G S k = Some (numberExp (fromInt k))
  (* findMset eq (x, L) =
         SOME (y, L') if there exists y such that eq (x, y)
                         and L ~ (y :: L') (multiset equality)
         NONE if there is no y in L such that eq (x, y)
    *)

  let rec findMSet eq (x, L) =
    let rec findMSet' = function
      | tried, [] -> None
      | tried, y :: L ->
          if eq (x, y) then Some (y, tried @ L) else findMSet' (y :: tried, L)
    in
    findMSet' ([], L)
  (* equalMset eq (L, L') = true iff L ~ L' (multiset equality) *)

  let rec equalMSet eq =
    let rec equalMSet' = function
      | [], [] -> true
      | x :: L1', L2 -> (
          match findMSet eq (x, L2) with
          | Some (y, L2') -> equalMSet' (L1', L2')
          | None -> false)
      | _ -> false
    in
    equalMSet'
  (* toExp sum = U

       Invariant:
       If sum is normal
       G |- U : V and U is the Twelf syntax conversion of sum
    *)

  let rec toExp = function
    | Sum (m, []) -> numberExp m
    | Sum (m, [ mon ]) ->
        if m = zero then toExpMon mon
        else plusExp (toExp (Sum (m, [])), toExpMon mon)
    | Sum (m, monLL) -> plusExp (toExp (Sum (m, monL)), toExpMon mon)

  and toExpMon = function
    | Mon (n, []) -> numberExp n
    | Mon (n, [ Us ]) ->
        if n = one then toExpEClo Us
        else timesExp (toExpMon (Mon (n, [])), toExpEClo Us)
    | Mon (n, Us :: UsL) -> timesExp (toExpMon (Mon (n, UsL)), toExpEClo Us)

  and toExpEClo = function U, Shift 0 -> U | Us -> EClo Us
  (* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *)

  let rec compatibleMon (Mon (_, UsL1), Mon (_, UsL2)) =
    equalMSet (fun Us1 Us2 -> sameExpW (Us1, Us2)) (UsL1, UsL2)

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
  (* plusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 + sum2
    *)

  let rec plusSum = function
    | Sum (m1, []), Sum (m2, monL2) -> Sum (m1 + m2, monL2)
    | Sum (m1, monL1), Sum (m2, []) -> Sum (m1 + m2, monL1)
    | Sum (m1, mon1 :: monL1), Sum (m2, monL2) ->
        plusSumMon (plusSum (Sum (m1, monL1), Sum (m2, monL2)), mon1)

  and plusSumMon = function
    | Sum (m, []), mon -> Sum (m, [ mon ])
    | Sum (m, monL), mon -> (
        match findMSet compatibleMon (mon, monL) with
        | Some (Mon (n', _), monL') ->
            let n'' = n + n' in
            if n'' = zero then Sum (m, monL')
            else Sum (m, Mon (n'', UsL) :: monL')
        | None -> Sum (m, mon :: monL))
  (* timesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 * sum2
    *)

  let rec timesSum = function
    | Sum (m1, []), Sum (m2, []) -> Sum (m1 * m2, [])
    | Sum (m1, mon1 :: monL1), sum2 ->
        plusSum (timesSumMon (sum2, mon1), timesSum (Sum (m1, monL1), sum2))
    | sum1, Sum (m2, mon2 :: monL2) ->
        plusSum (timesSumMon (sum1, mon2), timesSum (sum1, Sum (m2, monL2)))

  and timesSumMon = function
    | Sum (m, []), Mon (n, UsL) ->
        let n' = m * n in
        if n' = zero then Sum (n', []) else Sum (zero, [ Mon (n', UsL) ])
    | Sum (m, Mon (n', UsL') :: monL), mon ->
        let n'' = n * n' in
        let UsL'' = UsL @ UsL' in
        let (Sum (m', monL')) = timesSumMon (Sum (m, monL), mon) in
        Sum (m', Mon (n'', UsL'') :: monL')
  (* unaryMinusSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = ~1 * sum
    *)

  let rec unaryMinusSum sum = timesSum (Sum (-one, []), sum)
  (* minusSum sum1 sum2 = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 - sum2
    *)

  let rec minusSum sum1 sum2 = plusSum (sum1, unaryMinusSum sum2)
  (* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)

  let rec fromExpW = function
    | Us ->
        if cs = !myID then normalizeSum (extractSum fe)
        else Sum (zero, [ Mon (one, [ Us ]) ])
    | Us ->
        if cs = !myID then
          match fromString (conDecName conDec) with Some m -> Sum (m, [])
        else Sum (zero, [ Mon (one, [ Us ]) ])
    | Us -> fromExpW (Whnf.expandDef Us)
    | Us -> Sum (zero, [ Mon (one, [ Us ]) ])

  and fromExp Us = fromExpW (Whnf.whnf Us)

  and normalizeSum = function
    | sum -> sum
    | Sum (m, [ mon ]) -> plusSum (Sum (m, []), normalizeMon mon)
    | Sum (m, mon :: monL) ->
        plusSum (normalizeMon mon, normalizeSum (Sum (m, monL)))

  and normalizeMon = function
    | mon -> Sum (n, [])
    | Mon (n, [ Us ]) -> timesSum (Sum (n, []), fromExp Us)
    | mon -> timesSum (fromExp Us, normalizeMon (Mon (n, UsL)))

  and mapSum (f, Sum (m, monL)) =
    Sum (m, List.map (fun mon -> mapMon (f, mon)) monL)

  and mapMon (f, Mon (n, UsL)) =
    Mon (n, List.map (fun Us -> Whnf.whnf (f (EClo Us), id)) UsL)
  (* appSum (f, m + M1 + ...) = ()     and appMon (f, Mi) for_sml each i *)

  let rec appSum (f, Sum (m, monL)) = List.app (fun mon -> appMon (f, mon)) monL
  and appMon (f, Mon (n, UsL)) = List.app (fun Us -> f (EClo Us)) UsL
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
  (* unifySum G sum1 sum2 = result

       Invariant:
       If   G |- sum1 : number     sum1 normal
       and  G |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by gaussian elimination.
    *)

  let rec unifySum G sum1 sum2 =
    let rec invertMon = function
      | G, Mon (n, [ (LHS, s) ]), sum ->
          if Whnf.isPatSub s then
            let ss = Whnf.invert s in
            let RHS = toFgn (timesSum (Sum (~-(inverse n), []), sum)) in
            if Unify.invertible (G, (RHS, id), ss, r) then Some (G, LHS, RHS, ss)
            else None
          else None
      | _ -> None
    in
    match minusSum sum2 sum1 with
    | Sum (m, []) -> if m = zero then Succeed [] else Fail
    | sum -> (
        match findMon invertMon (G, sum) with
        | Some assignment -> Succeed [ Assign assignment ]
        | None ->
            let U = toFgn sum in
            let cnstr = ref (Eqn (G, U, numberExp zero)) in
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
        match minusSum (normalizeSum sum, fromExp (U2, id)) with
        | Sum (m, []) -> m = zero
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
      | E, n -> Lam (Dec (None, number ()), makeLam E (Int).-(n, 1))
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

  let rec arrow U V = Pi ((Dec (None, U), No), V)
  (* init cs installFunction = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)

  let rec init cs installF =
    myID := cs;
    numberID :=
      installF
        ( ConDec
            ( Field.name,
              None,
              0,
              Constraint (!myID, solveNumber),
              Uni Type,
              Kind ),
          None,
          [ MS.Mnil ] );
    unaryMinusID :=
      installF
        ( ConDec
            ( "~",
              None,
              0,
              Foreign (!myID, makeFgnUnary unaryMinusSum),
              arrow (number (), number ()),
              Type ),
          Some (FX.Prefix FX.maxPrec),
          [] );
    plusID :=
      installF
        ( ConDec
            ( "+",
              None,
              0,
              Foreign (!myID, makeFgnBinary plusSum),
              arrow (number (), arrow (number (), number ())),
              Type ),
          Some (FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
          [] );
    minusID :=
      installF
        ( ConDec
            ( "-",
              None,
              0,
              Foreign (!myID, makeFgnBinary minusSum),
              arrow (number (), arrow (number (), number ())),
              Type ),
          Some (FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
          [] );
    timesID :=
      installF
        ( ConDec
            ( "*",
              None,
              0,
              Foreign (!myID, makeFgnBinary timesSum),
              arrow (number (), arrow (number (), number ())),
              Type ),
          Some (FX.Infix (FX.dec FX.maxPrec, FX.Left)),
          [] );
    installFgnExpOps ();
    ()

  let solver =
    {
      name = "equality/" ^ Field.name ^ "s";
      keywords = "arithmetic,equality";
      needs = [ "Unify" ];
      fgnConst = Some { parse = parseNumber };
      init;
      reset = (fun () -> ());
      mark = (fun () -> ());
      unwind = (fun () -> ());
    }

  let fromExp = fromExp
  let toExp = toExp
  let normalize = normalizeSum
  let compatibleMon = compatibleMon
  let number = number
  let rec unaryMinus U = toFgn (unaryMinusSum (fromExp (U, id)))
  let rec plus U V = toFgn (plusSum (fromExp (U, id), fromExp (V, id)))
  let rec minus U V = toFgn (minusSum (fromExp (U, id), fromExp (V, id)))
  let rec times U V = toFgn (timesSum (fromExp (U, id), fromExp (V, id)))
  let constant = numberExp
  (* local *)
end

(* functor Cs.CSEqField *)
