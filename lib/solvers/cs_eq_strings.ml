(* String Equation Solver *)

(* Author: Roberto Virga *)

module CSEqStrings (Whnf : WHNF) (Unify : UNIFY) : CS = struct
  (*! structure CSManager = CSManager !*)

  open IntSyn
  module FX = CSManagerFixity
  module MS = ModeSyn
  (* CSManager.ModeSyn *)

  let myID = (ref - 1 : IntSyn.csid ref)
  let stringID = (ref - 1 : IntSyn.cid ref)
  let rec string () = Root (Const !stringID, Nil)
  let concatID = (ref - 1 : IntSyn.cid ref)
  let rec concatExp (U, V) = Root (Const !concatID, App (U, App (V, Nil)))
  let rec toString s = "\"" ^ s ^ "\""

  let rec stringConDec str =
    ConDec (toString str, None, 0, Normal, string (), Type)

  let rec stringExp str = Root (FgnConst (!myID, stringConDec str), Nil)
  (* fromString string =
         SOME(str)  if string parses to the string str
         NONE       otherwise
    *)

  let rec fromString string =
    let len = String.size string in
    if String.sub (string, 0) = '"' && String.sub (string, len - 1) = '"' then
      Some (String.substring (string, 1, len - 2))
    else None
  (* parseString string = SOME(conDec) or NONE

       Invariant:
       If str parses to the string str
       then conDec is the (foreign) constant declaration of str
    *)

  let rec parseString string =
    match fromString string with
    | Some str -> Some (stringConDec str)
    | None -> None
  (* solveString str = SOME(U)

       Invariant:
       U is the term obtained applying the foreign constant
       corresponding to the string str to an empty spine
    *)

  let rec solveString (G, S, k) = Some (stringExp (Int.toString k))

  type concat = Concat of atom list
  and atom = String of string | Exp of IntSyn.eclo
  (*        | (U,s)             *)

  exception MyIntsynRep of concat
  (* Internal syntax representation of this module *)

  let rec extractConcat = function
    | MyIntsynRep concat -> concat
    | fe -> raise (UnexpectedFgnExp fe)
  (* A concatenation is said to be normal if
         (a) it does not contain empty string atoms
         (b) it does not contain two consecutive string atoms
    *)

  (* ... and Exp atoms are in whnf?  - ak *)

  (* toExp concat = U

       Invariant:
       If concat is normal
       G |- U : V and U is the Twelf syntax conversion of concat
    *)

  let rec toExp = function
    | Concat [] -> stringExp ""
    | Concat [ String str ] -> stringExp str
    | Concat [ Exp (U, Shift 0) ] -> U
    | Concat [ Exp Us ] -> EClo Us
    | Concat (A :: AL) -> concatExp (toExp (Concat [ A ]), toExp (Concat AL))
  (* catConcat (concat1, concat2) = concat3

       Invariant:
       If   concat1 normal
       and  concat2 normal
       then concat3 normal
       and  concat3 = concat1 ++ concat2
    *)

  let rec catConcat = function
    | Concat [], concat2 -> concat2
    | concat1, Concat [] -> concat1
    | Concat AL1, Concat AL2 -> (
        match (List.rev AL1, AL2) with
        | String str1 :: revAL1', String str2 :: AL2' ->
            Concat (List.rev revAL1' @ (String (str1 ^ str2) :: AL2'))
        | _, _ -> Concat (AL1 @ AL2))
  (* fromExpW (U, s) = concat

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then concat is the representation of U[s] as concatenation of atoms
       and  concat is normal
    *)

  let rec fromExpW = function
    | Us ->
        if cs = !myID then normalize (extractConcat fe) else Concat [ Exp Us ]
    | Us ->
        if cs = !myID then
          match fromString (conDecName conDec) with
          | Some str -> if str = "" then Concat [] else Concat [ String str ]
        else Concat [ Exp Us ]
    | Us -> Concat [ Exp Us ]

  and fromExp Us = fromExpW (Whnf.whnf Us)

  and normalize = function
    | concat -> concat
    | concat -> concat
    | Concat [ Exp Us ] -> fromExp Us
    | Concat (A :: AL) ->
        catConcat (normalize (Concat [ A ]), normalize (Concat AL))
  (* mapSum (f, A1 + ...) = f(A1) ++ ... *)

  let rec mapConcat (f, Concat AL) =
    let rec mapConcat' = function
      | [] -> []
      | Exp Us :: AL -> Exp (f (EClo Us), id) :: mapConcat' AL
      | String str :: AL -> String str :: mapConcat' AL
    in
    Concat (mapConcat' AL)
  (* appConcat (f, A1 + ... ) = ()  and f(Ui) for_sml Ai = Exp Ui *)

  let rec appConcat (f, Concat AL) =
    let rec appAtom = function Exp Us -> f (EClo Us) | String _ -> () in
    List.app appAtom AL
  (* Split:                                         *)

  (* Split ::= str1 ++ str2                         *)

  type split = Split of string * string
  (* Decomposition:                                 *)

  (* Decomp ::= toParse | [parsed1, ..., parsedn]   *)

  type decomp = Decomp of string * string list
  (* index (str1, str2) = [idx1, ..., idxn]
       where the idxk are all the positions in str2 where str1 appear.
    *)

  let rec index (str1, str2) =
    let max = String.size str2 - String.size str1 in
    let rec index' i =
      if i <= max then
        if String.isPrefix str1 (String.extract (str2, i, None)) then
          i :: index' (i + 1)
        else index' (i + 1)
      else []
    in
    index' 0
  (* split (str1, str2) = [Split(l1,r1), ..., Split(ln,rn)]
       where, for_sml each k, str2 = lk ++ str1 ++ rk.
    *)

  let rec split (str1, str2) =
    let len = String.size str1 in
    let rec split' i =
      Split
        (String.extract (str2, 0, Some i), String.extract (str2, i + len, None))
    in
    List.map split' (index (str1, str2))
  (* sameConcat (concat1, concat2) =
         true only if concat1 = concat2 (as concatenations)
    *)

  let rec sameConcat (Concat AL1, Concat AL2) =
    let rec sameConcat' = function
      | [], [] -> true
      | String str1 :: AL1, String str2 :: AL2 ->
          str1 = str2 && sameConcat' (AL1, AL2)
      | Exp Us1 :: AL1, Exp Us2 :: AL2 ->
          sameExp (Us1, Us2) && sameConcat' (AL1, AL2)
      | _ -> false
    in
    sameConcat' (AL1, AL2)

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
  (* Unification Result:
       StringUnify ::= {G1 |- X1 := U1[s1], ..., Gn |- Xn := Un[sn]}
                     | {delay U1 on cnstr1, ..., delay Un on cnstrn}
                     | Failure
    *)

  type stringUnify =
    | MultAssign of dec ctx * exp * exp * sub list
    | MultDelay of exp list * cnstr ref
    | Failure
  (* toFgnUnify stringUnify = result
       where result is obtained translating stringUnify.
    *)

  let rec toFgnUnify = function
    | MultAssign L ->
        IntSyn.Succeed (List.map (function GXUss -> Assign GXUss) L)
    | MultDelay (UL, cnstr) ->
        IntSyn.Succeed (List.map (function U -> Delay (U, cnstr)) UL)
    | Failure -> Fail

  and unifyRigid (G, Concat AL1, Concat AL2) =
    let rec unifyRigid' = function
      | [], [] -> MultAssign []
      | String str1 :: AL1, String str2 :: AL2 ->
          if str1 = str2 then unifyRigid' (AL1, AL2) else Failure
      | Exp (U1, s) :: AL1, Exp (U2, _) :: AL2 ->
          let ss = Whnf.invert s in
          if Unify.invertible (G, (U2, id), ss, r) then
            match unifyRigid' (AL1, AL2) with
            | MultAssign l -> MultAssign ((G, U1, U2, ss) :: l)
            | Failure -> Failure
          else Failure
      | Exp (U1, _) :: AL1, Exp (U2, s) :: AL2 ->
          let ss = Whnf.invert s in
          if Unify.invertible (G, (U1, id), ss, r) then
            match unifyRigid' (AL1, AL2) with
            | MultAssign l -> MultAssign ((G, U2, U1, ss) :: l)
            | Failure -> Failure
          else Failure
      | Exp Us1 :: AL1, Exp Us2 :: AL2 ->
          if sameExpW (Us1, Us2) then unifyRigid' (AL1, AL2) else Failure
      | Exp Us1 :: AL1, Exp Us2 :: AL2 ->
          if sameExpW (Us1, Us2) then unifyRigid' (AL1, AL2) else Failure
      | _ -> Failure
    in
    unifyRigid' (AL1, AL2)
  (* unifyString (G, concat, str, cnstr) = stringUnify

       Invariant:
       If   G |- concat : string    concat1 normal
       then if there is an instantiation I :
               s.t. G |- concat <I> == str
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [U1, ..., Un] cnstr
                   where U1, ..., Un are expression to be delayed on cnstr
    *)

  let rec unifyString = function
    | G, Concat (String prefix :: AL), str, cnstr ->
        if String.isPrefix prefix str then
          let suffix = String.extract (str, String.size prefix, None) in
          unifyString (G, Concat AL, suffix, cnstr)
        else Failure
    | G, Concat AL, str, cnstr -> (
        let rec unifyString' = function
          | AL, [] -> (Failure, [])
          | [], [ Decomp (parse, parsedL) ] -> (MultAssign [], parse :: parsedL)
          | [], candidates -> (MultDelay ([], cnstr), [])
          | Exp Us1 :: Exp Us2 :: AL, _ ->
              (MultDelay ([ EClo Us1; EClo Us2 ], cnstr), [])
          | Exp (U, s) :: AL, candidates ->
              if Whnf.isPatSub s then
                let rec assign = function
                  | r, [] -> None
                  | ( r,
                      ( _,
                        EVar (r', _, _, _),
                        Root (FgnConst (cs, conDec), Nil),
                        _ )
                      :: L ) ->
                      if r = r' then fromString (conDecName conDec)
                      else assign r L
                  | r, _ :: L -> assign r L
                in
                match unifyString' (AL, candidates) with
                | MultAssign L, parsed :: parsedL -> (
                    match assign r L with
                    | None ->
                        let ss = Whnf.invert s in
                        let W = stringExp parsed in
                        (MultAssign ((G, U, W, ss) :: L), parsedL)
                    | Some parsed' ->
                        if parsed = parsed' then (MultAssign L, parsedL)
                        else (Failure, []))
                | MultDelay (UL, cnstr), _ ->
                    (MultDelay (EClo (U, s) :: UL, cnstr), [])
                | Failure, _ -> (Failure, [])
              else (MultDelay ([ EClo (U, s) ], cnstr), [])
          | Exp Us :: AL, _ -> (MultDelay ([ EClo Us ], cnstr), [])
          | [ String str ], candidates ->
              let rec successors (Decomp (parse, parsedL)) =
                List.mapPartial
                  (function
                    | Split (prefix, "") -> Some (Decomp (prefix, parsedL))
                    | Split (prefix, suffix) -> None)
                  (split (str, parse))
              in
              let candidates' =
                List.foldr @ [] (List.map successors candidates)
              in
              unifyString' ([], candidates')
          | String str :: AL, candidates ->
              let rec successors (Decomp (parse, parsedL)) =
                List.map
                  (function
                    | Split (prefix, suffix) ->
                        Decomp (suffix, prefix :: parsedL))
                  (split (str, parse))
              in
              let candidates' =
                List.foldr @ [] (List.map successors candidates)
              in
              unifyString' (AL, candidates')
        in
        match unifyString' (AL, [ Decomp (str, []) ]) with
        | result, [] -> result
        | result, [ "" ] -> result
        | result, parsedL -> Failure)
  (* unifyConcat (G, concat1, concat2) = stringUnify

       Invariant:
       If   G |- concat1 : string    concat1 normal
       and  G |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. G |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [U1, ..., Un] cnstr
                   where U1, ..., Un are expression to be delayed on cnstr
    *)

  let rec unifyConcat (G, concat1, concat2) =
    let U1 = toFgn concat1 in
    let U2 = toFgn concat2 in
    let cnstr = ref (Eqn (G, U1, U2)) in
    match (AL1, AL2) with
    | [], [] -> MultAssign [] (* FIX: the next two cases are wrong -kw *)
    | [], _ -> Failure
    | _, [] -> Failure
    | [ String str1 ], [ String str2 ] ->
        if str1 = str2 then MultAssign [] else Failure
    | [ Exp (U, s) ], _ ->
        if Whnf.isPatSub s then
          let ss = Whnf.invert s in
          if Unify.invertible (G, (U2, id), ss, r) then
            MultAssign [ (G, U, U2, ss) ]
          else MultDelay ([ U1; U2 ], cnstr)
        else MultDelay ([ U1; U2 ], cnstr)
    | _, [ Exp (U, s) ] ->
        if Whnf.isPatSub s then
          let ss = Whnf.invert s in
          if Unify.invertible (G, (U1, id), ss, r) then
            MultAssign [ (G, U, U1, ss) ]
          else MultDelay ([ U1; U2 ], cnstr)
        else MultDelay ([ U1; U2 ], cnstr)
    | [ String str ], _ -> unifyString (G, concat2, str, cnstr)
    | _, [ String str ] -> unifyString (G, concat1, str, cnstr)
    | _ -> (
        match unifyRigid (G, concat1, concat2) with
        | result -> result
        | Failure ->
            if sameConcat (concat1, concat2) then MultAssign []
            else MultDelay ([ U1; U2 ], cnstr))

  and toFgn = function
    | concat -> stringExp str
    | concat -> U
    | concat -> FgnExp (!myID, MyIntsynRep concat)
  (* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep concat) and concat : normal
       then U is the Twelf syntax conversion of concat
    *)

  let rec toInternal = function
    | MyIntsynRep concat, () -> toExp (normalize concat)
    | fe, () -> raise (UnexpectedFgnExp fe)
  (* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep concat)   concat : normal
       and
         f concat = f (A1 ++ ... ++ AN )
                  = f (A1) ++ ... ++ f (AN)
                  = concat'           concat' : normal
       then
         U' is a foreign expression representing concat'
    *)

  let rec map = function
    | MyIntsynRep concat, f -> toFgn (normalize (mapConcat (f, concat)))
    | fe, _ -> raise (UnexpectedFgnExp fe)
  (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep concat)     concat : normal
       and
          concat = A1 ++ ... ++ AN
          where some Ai are (Exp Usi)
       then f is applied to each Usi
       (since concat : normal, each Usij is in whnf)
    *)

  let rec app = function
    | MyIntsynRep concat, f -> appConcat (f, concat)
    | fe, _ -> raise (UnexpectedFgnExp fe)

  let rec equalTo = function
    | MyIntsynRep concat, U2 -> sameConcat (normalize concat, fromExp (U2, id))
    | fe, _ -> raise (UnexpectedFgnExp fe)

  let rec unifyWith = function
    | MyIntsynRep concat, (G, U2) ->
        toFgnUnify (unifyConcat (G, normalize concat, fromExp (U2, id)))
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
      | n -> App (Root (BVar n, Nil), makeParams (n - 1))
    in
    let rec makeLam = function
      | E, 0 -> E
      | E, n -> Lam (Dec (None, string ()), makeLam E (n - 1))
    in
    let rec expand = function
      | (Nil, s), arity -> (makeParams arity, arity)
      | (App (U, S), s), arity ->
          let S', arity' = expand ((S, s), arity - 1) in
          (App (EClo (U, comp (s, Shift arity')), S'), arity')
      | (SClo (S, s'), s), arity -> expand ((S, comp (s, s')), arity)
    in
    let S', arity' = expand ((S, id), arity) in
    makeLam (toFgn (opExp S')) arity'

  let rec makeFgnBinary opConcat =
    makeFgn
      ( 2,
        function
        | App (U1, App (U2, Nil)) ->
            opConcat (fromExp (U1, id), fromExp (U2, id)) )

  let rec arrow (U, V) = Pi ((Dec (None, U), No), V)
  (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)

  let rec init (cs, installF) =
    myID := cs;
    stringID :=
      installF
        ( ConDec
            ("string", None, 0, Constraint (!myID, solveString), Uni Type, Kind),
          None,
          [ MS.Mnil ] );
    concatID :=
      installF
        ( ConDec
            ( "++",
              None,
              0,
              Foreign (!myID, makeFgnBinary catConcat),
              arrow (string (), arrow (string (), string ())),
              Type ),
          Some (FX.Infix (FX.maxPrec, FX.Right)),
          [] );
    installFgnExpOps ();
    ()

  let solver =
    ({
       name = "equality/strings";
       keywords = "strings,equality";
       needs = [ "Unify" ];
       fgnConst = Some { parse = parseString };
       init;
       reset = (function () -> ());
       mark = (function () -> ());
       unwind = (function () -> ());
     }
      : CSManager.solver)
end

(* functor CSEqStrings *)
