(* String Equation Solver *)
(* Author: Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) CSEqStrings ((*! structure IntSyn : INTSYN !*)
                     structure Whnf : WHNF
                     (*! sharing Whnf.IntSyn = IntSyn !*)
                     structure Unify : UNIFY
                     (*! sharing Unify.IntSyn = IntSyn !*)
                     (*! structure CSManager : CS_MANAGER !*)
                     (*! sharing CSManager.IntSyn = IntSyn !*)
                       )
 : CS =
struct
  (*! structure CSManager = CSManager !*)

  local
    open IntSyn

    structure FX = CSManager.Fixity
    structure MS = ModeSyn (* CSManager.ModeSyn *)

    (* GEN BEGIN TAG OUTSIDE LET *) val myID = ref ~1 : IntSyn.csid ref (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val stringID = ref ~1 : IntSyn.cid ref (* GEN END TAG OUTSIDE LET *)

    fun string () = Root (Const (!stringID), Nil)

    (* GEN BEGIN TAG OUTSIDE LET *) val concatID = ref ~1 : IntSyn.cid ref (* GEN END TAG OUTSIDE LET *)

    fun concatExp (U, V) = Root (Const (!concatID), App (U, App (V, Nil)))

    fun toString s = ("\"" ^ s ^ "\"")

    fun stringConDec (str) = ConDec (toString (str), NONE, 0, Normal,
                                     string (), Type)

    fun stringExp (str) = Root (FgnConst (!myID, stringConDec (str)), Nil)

    (* fromString string =
         SOME(str)  if string parses to the string str
         NONE       otherwise
    *)
    fun fromString string =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val len = String.size string (* GEN END TAG OUTSIDE LET *)
          in
            if (String.sub (string, 0) = #"\"")
              andalso (String.sub (string, len-1) = #"\"")
            then
              SOME (String.substring (string, 1, len-2))
            else
              NONE
          end

    (* parseString string = SOME(conDec) or NONE

       Invariant:
       If str parses to the string str
       then conDec is the (foreign) constant declaration of str
    *)
    fun parseString string =
          (case fromString (string)
             of SOME(str) => SOME(stringConDec (str))
              | NONE => NONE)

    (* solveString str = SOME(U)

       Invariant:
       U is the term obtained applying the foreign constant
       corresponding to the string str to an empty spine
    *)
    fun solveString (G, S, k) = SOME(stringExp (Int.toString k))

    datatype concat =
      Concat of atom list                  (* Concatenation:             *)
                                           (* Concat::= A1 ++ A2 ++ ...  *)

    and atom =                             (* Atoms:                     *)
      String of string                     (* Atom ::= "str"             *)
    | Exp of IntSyn.eclo                   (*        | (U,s)             *)

    exception MyIntsynRep of concat        (* Internal syntax representation of this module *)

    fun (* GEN BEGIN FUN FIRST *) extractConcat (MyIntsynRep concat) = concat (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) extractConcat fe = raise (UnexpectedFgnExp fe) (* GEN END FUN BRANCH *)

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
    fun (* GEN BEGIN FUN FIRST *) toExp (Concat nil) = stringExp "" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) toExp (Concat [String str]) = stringExp str (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) toExp (Concat [Exp (U, Shift(0))]) = U (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) toExp (Concat [Exp Us]) = EClo Us (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) toExp (Concat (A :: AL)) =
          concatExp (toExp (Concat [A]), toExp (Concat AL)) (* GEN END FUN BRANCH *)

    (* catConcat (concat1, concat2) = concat3

       Invariant:
       If   concat1 normal
       and  concat2 normal
       then concat3 normal
       and  concat3 = concat1 ++ concat2
    *)
    fun (* GEN BEGIN FUN FIRST *) catConcat (Concat nil, concat2) = concat2 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) catConcat (concat1, Concat nil) = concat1 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) catConcat (Concat AL1, Concat AL2) =
          (case (List.rev AL1, AL2)
             of ((String str1) :: revAL1', (String str2) :: AL2') =>
               Concat ((List.rev revAL1') @ ((String (str1 ^ str2)) :: AL2'))
              | (_, _) => Concat (AL1 @ AL2)) (* GEN END FUN BRANCH *)

    (* fromExpW (U, s) = concat

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then concat is the representation of U[s] as concatenation of atoms
       and  concat is normal
    *)
    fun (* GEN BEGIN FUN FIRST *) fromExpW (Us as (FgnExp (cs, fe), _)) =
          if (cs = !myID)
          then normalize (extractConcat fe)
          else Concat [Exp Us] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fromExpW (Us as (Root (FgnConst (cs, conDec), _), _)) =
          if (cs = !myID)
          then (case fromString (conDecName (conDec))
                  of SOME(str) => if (str = "") then Concat nil
                                  else Concat [String str])
          else Concat [Exp Us] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) fromExpW Us =
          Concat [Exp Us] (* GEN END FUN BRANCH *)

    (* fromExp (U, s) = concat

       Invariant:
       If   G' |- s : G    G |- U : V
       then concat is the representation of U[s] as concatenation of atoms
       and  concat is normal
    *)
    and fromExp Us =
          fromExpW (Whnf.whnf Us)

    (* normalize concat = concat', where concat' normal and concat' = concat *)
    and (* GEN BEGIN FUN FIRST *) normalize (concat as (Concat nil)) = concat (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) normalize (concat as (Concat [String str])) = concat (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalize (Concat [Exp Us]) = fromExp Us (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalize (Concat (A :: AL)) =
          catConcat (normalize (Concat [A]), normalize(Concat AL)) (* GEN END FUN BRANCH *)

    (* mapSum (f, A1 + ...) = f(A1) ++ ... *)
    fun mapConcat (f, Concat AL) =
          let
            fun (* GEN BEGIN FUN FIRST *) mapConcat' nil = nil (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) mapConcat' ((Exp Us) :: AL) =
                  (Exp (f (EClo Us), id)) :: mapConcat' AL (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) mapConcat' ((String str) :: AL) =
                  (String str) :: mapConcat' AL (* GEN END FUN BRANCH *)
          in
            Concat (mapConcat' AL)
          end

    (* appConcat (f, A1 + ... ) = ()  and f(Ui) for Ai = Exp Ui *)
    fun appConcat (f, Concat AL) =
        let
            fun (* GEN BEGIN FUN FIRST *) appAtom (Exp Us) = f (EClo Us) (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) appAtom (String _) = () (* GEN END FUN BRANCH *)
        in
            List.app appAtom AL
        end

    (* Split:                                         *)
    (* Split ::= str1 ++ str2                         *)
    datatype split = Split of string * string

    (* Decomposition:                                 *)
    (* Decomp ::= toParse | [parsed1, ..., parsedn]   *)
    datatype decomp = Decomp of string * string list

    (* index (str1, str2) = [idx1, ..., idxn]
       where the idxk are all the positions in str2 where str1 appear.
    *)
    fun index (str1, str2) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val max = (String.size str2) - (String.size str1) (* GEN END TAG OUTSIDE LET *)
            fun index' i =
                  if (i <= max)
                  then
                    if String.isPrefix str1 (String.extract (str2, i, NONE))
                    then i :: index' (i+1)
                    else index' (i+1)
                  else
                    nil
          in
            index' 0
          end

    (* split (str1, str2) = [Split(l1,r1), ..., Split(ln,rn)]
       where, for each k, str2 = lk ++ str1 ++ rk.
    *)
    fun split (str1, str2) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val len = String.size str1 (* GEN END TAG OUTSIDE LET *)
            fun split' i =
                  Split (String.extract (str2, 0, SOME(i)),
                         String.extract (str2, i+len, NONE))
          in
            List.map split' (index (str1, str2))
          end

    (* sameConcat (concat1, concat2) =
         true only if concat1 = concat2 (as concatenations)
    *)
    fun sameConcat (Concat AL1, Concat AL2) =
          let
            fun (* GEN BEGIN FUN FIRST *) sameConcat' (nil, nil) = true (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) sameConcat' ((String str1) :: AL1, (String str2) :: AL2) =
                  (str1 = str2) andalso sameConcat' (AL1, AL2) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) sameConcat' ((Exp Us1) :: AL1, (Exp Us2) :: AL2) =
                  sameExp(Us1, Us2) andalso sameConcat' (AL1, AL2) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) sameConcat' _ = false (* GEN END FUN BRANCH *)
          in
            sameConcat' (AL1, AL2)
          end

    (* sameExpW ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1)  in whnf
       and  G |- s2 : G2    G2 |- U2 : V2    (U2,s2)  in whnf
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
    and (* GEN BEGIN FUN FIRST *) sameExpW (Us1 as (Root (H1, S1), s1), Us2 as (Root (H2, S2), s2)) =
          (case (H1, H2) of
             (BVar(k1), BVar(k2)) =>
               (k1 = k2) andalso sameSpine ((S1, s1), (S2, s2))
           | (FVar (n1,_,_), FVar (n2,_,_)) =>
               (n1 = n2) andalso sameSpine ((S1, s1), (S2, s2))
           | _ => false) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) sameExpW (Us1 as (U1 as EVar(r1, G1, V1, cnstrs1), s1),
                  Us2 as (U2 as EVar(r2, G2, V2, cnstrs2), s2)) =
         (r1 = r2) andalso sameSub (s1, s2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) sameExpW _ = false (* GEN END FUN BRANCH *)

    (* sameExp ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1
       and  G |- s2 : G2    G2 |- U2 : V2
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
    and sameExp (Us1, Us2) = sameExpW (Whnf.whnf Us1, Whnf.whnf Us2)

    (* sameSpine (S1, S2) = T

       Invariant:
       If   G |- S1 : V > W
       and  G |- S2 : V > W
       then T only if S1 = S2 (as spines)
    *)
    and (* GEN BEGIN FUN FIRST *) sameSpine ((Nil, s1), (Nil, s2)) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) sameSpine ((SClo (S1, s1'), s1), Ss2) =
          sameSpine ((S1, comp (s1', s1)), Ss2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) sameSpine (Ss1, (SClo (S2, s2'), s2)) =
          sameSpine (Ss1, (S2, comp (s2', s2))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) sameSpine ((App (U1, S1), s1), (App (U2, S2), s2)) =
          sameExp ((U1, s1), (U2, s2))
            andalso sameSpine ((S1, s1), (S2, s2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) sameSpine _ = false (* GEN END FUN BRANCH *)

    (* sameSub (s1, s2) = T

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then T only if s1 = s2 (as substitutions)
    *)
    and (* GEN BEGIN FUN FIRST *) sameSub (Shift _, Shift _) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) sameSub (Dot (Idx (k1), s1), Dot (Idx (k2), s2)) =
          (k1 = k2) andalso sameSub (s1, s2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) sameSub (s1 as Dot (Idx _, _), Shift (k2)) =
          sameSub (s1, Dot (Idx (Int.+(k2,1)), Shift (Int.+(k2,1)))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) sameSub (Shift (k1), s2 as Dot (Idx _, _)) =
          sameSub (Dot (Idx (Int.+(k1,1)), Shift (Int.+(k1,1))), s2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) sameSub _ = false (* GEN END FUN BRANCH *)

    (* Unification Result:
       StringUnify ::= {G1 |- X1 := U1[s1], ..., Gn |- Xn := Un[sn]}
                     | {delay U1 on cnstr1, ..., delay Un on cnstrn}
                     | Failure
    *)
    datatype string_unify =
      MultAssign of (dec ctx * exp * exp * sub) list
    | MultDelay of exp list * cnstr ref
    | Failure

    (* toFgnUnify stringUnify = result
       where result is obtained translating stringUnify.
    *)
    fun (* GEN BEGIN FUN FIRST *) toFgnUnify (MultAssign L) =
          IntSyn.Succeed (List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn GXUss => Assign GXUss (* GEN END FUNCTION EXPRESSION *)) L) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) toFgnUnify (MultDelay (UL, cnstr)) =
          IntSyn.Succeed (List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn U => Delay (U, cnstr) (* GEN END FUNCTION EXPRESSION *)) UL) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) toFgnUnify (Failure) = Fail (* GEN END FUN BRANCH *)

    (* unifyRigid (G, concat1, concat2) = stringUnify

       Invariant:
       If   G |- concat1 : string    concat1 normal
       and  G |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. G |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else stringUnify = Failure
    *)
    and unifyRigid (G, Concat AL1, Concat AL2) =
          let
            fun (* GEN BEGIN FUN FIRST *) unifyRigid' (nil, nil) = MultAssign nil (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) unifyRigid' ((String str1) :: AL1, (String str2) :: AL2) =
                  if (str1 = str2) then unifyRigid' (AL1, AL2)
                  else Failure (* GEN END FUN BRANCH *)
                (* FIX: the next two cases are wrong -kw *)
              | (* GEN BEGIN FUN BRANCH *) unifyRigid' ((Exp (U1 as (EVar (r, _, _, _)), s)) :: AL1,
                             (Exp (U2 as (Root (FVar _, _)), _)) :: AL2) =
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val ss = Whnf.invert s (* GEN END TAG OUTSIDE LET *)
                  in
                    if Unify.invertible (G, (U2, id), ss, r)
                    then (case (unifyRigid' (AL1, AL2))
                            of MultAssign l =>
                                 MultAssign ((G, U1, U2, ss) :: l)
                             | Failure => Failure)
                    else Failure
                  end (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) unifyRigid' ((Exp (U1 as (Root (FVar _, _)), _)) :: AL1,
                             (Exp (U2 as (EVar (r, _, _, _)), s)) :: AL2) =
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val ss = Whnf.invert s (* GEN END TAG OUTSIDE LET *)
                  in
                    if Unify.invertible (G, (U1, id), ss, r)
                    then (case (unifyRigid' (AL1, AL2))
                            of MultAssign l =>
                                 MultAssign ((G, U2, U1, ss) :: l)
                             | Failure => Failure)
                    else Failure
                  end (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) unifyRigid'((Exp (Us1 as (Root (FVar _, _), _))) :: AL1,
                            (Exp (Us2 as (Root (FVar _, _), _))) :: AL2) =
                  if (sameExpW (Us1, Us2))
                  then unifyRigid' (AL1, AL2)
                  else Failure (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) unifyRigid'((Exp (Us1 as (EVar (_, _, _, _), _))) :: AL1,
                            (Exp (Us2 as (EVar (_, _, _, _), _))) :: AL2) =
                  if (sameExpW (Us1, Us2))
                  then unifyRigid' (AL1, AL2)
                  else Failure (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) unifyRigid' _ = Failure (* GEN END FUN BRANCH *)
          in
            unifyRigid' (AL1, AL2)
          end

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
    fun (* GEN BEGIN FUN FIRST *) unifyString (G, Concat (String prefix :: AL), str, cnstr) =
          if (String.isPrefix prefix str)
          then
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val suffix = String.extract (str, String.size prefix, NONE) (* GEN END TAG OUTSIDE LET *)
            in
              unifyString (G, Concat AL, suffix, cnstr)
            end
          else Failure (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) unifyString (G, Concat AL, str, cnstr) =
          let
            fun (* GEN BEGIN FUN FIRST *) unifyString' (AL, nil) =
                  (Failure, nil) (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) unifyString' (nil, [Decomp (parse, parsedL)]) =
                  (MultAssign nil, parse :: parsedL) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) unifyString' (nil, candidates) =
                  (MultDelay (nil, cnstr), nil) (* GEN END FUN BRANCH *)
             | (* GEN BEGIN FUN BRANCH *) unifyString' ((Exp Us1) :: (Exp Us2) :: AL, _) =
                  (MultDelay ([EClo Us1, EClo Us2], cnstr), nil) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) unifyString' ((Exp (U as (EVar (r, _, _, _)), s)) :: AL, candidates) =
                  if (Whnf.isPatSub s)
                  then
                    let
                      fun (* GEN BEGIN FUN FIRST *) assign r nil = NONE (* GEN END FUN FIRST *)
                        | (* GEN BEGIN FUN BRANCH *) assign r ((_, EVar (r', _, _, _),
                                        Root (FgnConst (cs, conDec), Nil), _) :: L) =
                            if (r = r') then fromString (conDecName (conDec))
                            else assign r L (* GEN END FUN BRANCH *)
                        | (* GEN BEGIN FUN BRANCH *) assign r (_ :: L) = assign r L (* GEN END FUN BRANCH *)
                    in
                      (case unifyString' (AL, candidates)
                         of (MultAssign L, parsed :: parsedL) =>
                               (case (assign r L)
                                  of NONE =>
                                       let
                                         (* GEN BEGIN TAG OUTSIDE LET *) val ss = Whnf.invert s (* GEN END TAG OUTSIDE LET *)
                                         (* GEN BEGIN TAG OUTSIDE LET *) val W = stringExp(parsed) (* GEN END TAG OUTSIDE LET *)
                                       in
                                         (MultAssign ((G, U, W, ss) :: L), parsedL)
                                       end
                                   | SOME(parsed') =>
                                       if (parsed = parsed')
                                       then (MultAssign L, parsedL)
                                       else (Failure, nil))
                          | (MultDelay (UL, cnstr), _) =>
                               (MultDelay ((EClo (U, s)) :: UL, cnstr), nil)
                          | (Failure, _) => (Failure, nil))
                    end
                  else (MultDelay ([EClo (U, s)], cnstr), nil) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) unifyString' ((Exp Us) :: AL, _) =
                  (MultDelay ([EClo Us], cnstr), nil) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) unifyString' ([String str], candidates) =
                  let
                    fun successors (Decomp (parse, parsedL)) =
                          List.mapPartial ((* GEN BEGIN FUNCTION EXPRESSION *) fn (Split (prefix, "")) =>
                                                 SOME (Decomp (prefix, parsedL))
                                            | (Split (prefix, suffix)) => NONE (* GEN END FUNCTION EXPRESSION *))
                                          (split (str, parse))
                    (* GEN BEGIN TAG OUTSIDE LET *) val candidates' =
                          List.foldr op@ nil (List.map successors candidates) (* GEN END TAG OUTSIDE LET *)
                  in
                    unifyString' (nil, candidates')
                  end (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) unifyString' ((String str) :: AL, candidates) =
                  let
                    fun successors (Decomp (parse, parsedL)) =
                          List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (Split (prefix, suffix)) =>
                                          Decomp (suffix, prefix :: parsedL) (* GEN END FUNCTION EXPRESSION *))
                                   (split (str, parse))
                    (* GEN BEGIN TAG OUTSIDE LET *) val candidates' =
                          List.foldr op@ nil (List.map successors candidates) (* GEN END TAG OUTSIDE LET *)
                  in
                    unifyString' (AL, candidates')
                  end (* GEN END FUN BRANCH *)
          in
            (case unifyString' (AL, [Decomp(str, nil)])
               of (result, nil) => result
                | (result, [""]) => result
                | (result, parsedL) => Failure)
          end (* GEN END FUN BRANCH *)

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
    fun unifyConcat (G, concat1 as (Concat AL1), concat2 as (Concat AL2)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val U1 = toFgn concat1 (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val U2 = toFgn concat2 (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val cnstr = ref (Eqn (G, U1, U2)) (* GEN END TAG OUTSIDE LET *)
          in
            case (AL1, AL2)
              of (nil, nil) => MultAssign nil
                 (* FIX: the next two cases are wrong -kw *)
               | (nil, _) => Failure
               | (_, nil) => Failure
               | ([String str1], [String str2]) =>
                   if (str1 = str2) then (MultAssign nil) else Failure
               | ([Exp (U as (EVar(r, _, _, _)), s)], _) =>
                   if (Whnf.isPatSub s)
                   then
                     let
                       (* GEN BEGIN TAG OUTSIDE LET *) val ss = Whnf.invert s (* GEN END TAG OUTSIDE LET *)
                     in
                       if Unify.invertible (G, (U2, id), ss, r)
                       then (MultAssign [(G, U, U2, ss)])
                       else MultDelay ([U1, U2], cnstr)
                     end
                   else
                     MultDelay ([U1, U2], cnstr)
               | (_, [Exp (U as (EVar(r, _, _, _)), s)]) =>
                   if (Whnf.isPatSub s)
                   then
                     let
                       (* GEN BEGIN TAG OUTSIDE LET *) val ss = Whnf.invert s (* GEN END TAG OUTSIDE LET *)
                     in
                       if Unify.invertible (G, (U1, id), ss, r)
                       then (MultAssign [(G, U, U1, ss)])
                       else MultDelay ([U1, U2], cnstr)
                     end
                   else
                     MultDelay ([U1, U2], cnstr)
               | ([String str], _) =>
                   unifyString (G, concat2, str, cnstr)
               | (_, [String str]) =>
                   unifyString (G, concat1, str, cnstr)
               | _ =>
                   (case (unifyRigid (G, concat1, concat2))
                      of (result as (MultAssign _)) => result
                       | Failure => if (sameConcat (concat1, concat2))
                                    then MultAssign nil
                                    else MultDelay ([U1, U2], cnstr))
          end

    (* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *)
    and (* GEN BEGIN FUN FIRST *) toFgn (concat as (Concat [String str])) = stringExp (str) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) toFgn (concat as (Concat [Exp (U, id)])) = U (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) toFgn (concat) =
        FgnExp (!myID, MyIntsynRep concat) (* GEN END FUN BRANCH *)

    (* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep concat) and concat : normal
       then U is the Twelf syntax conversion of concat
    *)
    fun (* GEN BEGIN FUN FIRST *) toInternal (MyIntsynRep concat) () = toExp (normalize concat) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) toInternal fe () = raise (UnexpectedFgnExp fe) (* GEN END FUN BRANCH *)

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
    fun (* GEN BEGIN FUN FIRST *) map (MyIntsynRep concat) f = toFgn (normalize (mapConcat (f,concat))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) map fe _ = raise (UnexpectedFgnExp fe) (* GEN END FUN BRANCH *)

    (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep concat)     concat : normal
       and
          concat = A1 ++ ... ++ AN
          where some Ai are (Exp Usi)
       then f is applied to each Usi
       (since concat : normal, each Usij is in whnf)
    *)
    fun (* GEN BEGIN FUN FIRST *) app (MyIntsynRep concat) f = appConcat (f, concat) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) app fe _ = raise (UnexpectedFgnExp fe) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) equalTo (MyIntsynRep concat) U2 =
        sameConcat (normalize (concat),
                    fromExp (U2, id)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalTo fe _ = raise (UnexpectedFgnExp fe) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) unifyWith (MyIntsynRep concat) (G, U2) =
        toFgnUnify (unifyConcat (G, normalize (concat),
                                 fromExp (U2, id))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) unifyWith fe _ = raise (UnexpectedFgnExp fe) (* GEN END FUN BRANCH *)

    fun installFgnExpOps () = let
        (* GEN BEGIN TAG OUTSIDE LET *) val csid = !myID (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = FgnExpStd.ToInternal.install (csid, toInternal) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = FgnExpStd.Map.install (csid, map) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = FgnExpStd.App.install (csid, app) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = FgnExpStd.UnifyWith.install (csid, unifyWith) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = FgnExpStd.EqualTo.install (csid, equalTo) (* GEN END TAG OUTSIDE LET *)
    in
        ()
    end

    fun makeFgn (arity, opExp) (S) =
          let
            fun (* GEN BEGIN FUN FIRST *) makeParams 0 = Nil (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) makeParams n =
                  App (Root(BVar (n), Nil), makeParams (n-1)) (* GEN END FUN BRANCH *)
            fun (* GEN BEGIN FUN FIRST *) makeLam E 0 = E (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) makeLam E n =
                  Lam (Dec (NONE, string()), makeLam E (n-1)) (* GEN END FUN BRANCH *)
            fun (* GEN BEGIN FUN FIRST *) expand ((Nil, s), arity) =
                  (makeParams arity, arity) (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) expand ((App (U, S), s), arity) =
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val (S', arity') = expand ((S, s), arity-1) (* GEN END TAG OUTSIDE LET *)
                  in
                    (App (EClo (U, comp (s, Shift (arity'))), S'), arity')
                  end (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) expand ((SClo (S, s'), s), arity) =
                  expand ((S, comp (s, s')), arity) (* GEN END FUN BRANCH *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (S', arity') = expand ((S, id), arity) (* GEN END TAG OUTSIDE LET *)
          in
            makeLam (toFgn (opExp S')) arity'
          end

    fun makeFgnBinary opConcat =
          makeFgn (2,
            (* GEN BEGIN FUNCTION EXPRESSION *) fn (App (U1, App (U2, Nil))) =>
              opConcat (fromExp (U1, id), fromExp (U2, id)) (* GEN END FUNCTION EXPRESSION *))

    fun arrow (U, V) = Pi ((Dec (NONE, U), No), V)

    (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
    fun init (cs, installF) =
          (
            myID := cs;
    
            stringID :=
              installF (ConDec ("string", NONE, 0, Constraint (!myID, solveString),
                                Uni (Type), Kind),
                        NONE, [MS.Mnil]);
    
            concatID :=
              installF (ConDec ("++", NONE, 0,
                                Foreign (!myID, makeFgnBinary catConcat),
                                arrow (string (), arrow (string (), string ())),
                                Type),
                        SOME(FX.Infix (FX.maxPrec, FX.Right)), nil);
            installFgnExpOps ();
            ()
          )
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val solver =
          {
            name = "equality/strings",
            keywords = "strings,equality",
            needs = ["Unify"],
    
            fgnConst = SOME({parse = parseString}),
    
            init = init,
    
            reset  = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *)),
            mark   = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *)),
            unwind = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *))
          } : CSManager.solver (* GEN END TAG OUTSIDE LET *)

  end
end (* GEN END FUNCTOR DECL *)  (* functor CSEqStrings *)
