(* Type Checking *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) TypeCheck ((*! structure IntSyn' : INTSYN !*)
                   structure Conv : CONV
                   (*! sharing Conv.IntSyn = IntSyn' !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn'  !*)
                   structure Names : NAMES
                   (*! sharing Names.IntSyn = IntSyn' !*)
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = IntSyn' !*)
                       )
  : TYPECHECK =
struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error of string

  local
    structure I = IntSyn

    (* for debugging purposes *)
    fun (* GEN BEGIN FUN FIRST *) subToString (G, I.Dot (I.Idx (n), s)) =
          Int.toString (n) ^ "." ^ subToString (G, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) subToString (G, I.Dot (I.Exp (U), s)) =
          "(" ^ Print.expToString (G, U) ^ ")." ^ subToString (G, s) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) subToString (G, I.Dot (I.Block (L as I.LVar _), s)) =
          LVarToString (G, L) ^ "." ^ subToString (G, s) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) subToString (G, I.Shift(n)) = "^" ^ Int.toString (n) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) LVarToString (G, I.LVar (ref (SOME B), sk, (l, t))) =
          LVarToString (G, I.blockSub (B, sk)) (* GEN END FUN FIRST *)
                                        (* whnf for Blocks ? Sun Dec  1 11:38:17 2002 -cs *)
      | (* GEN BEGIN FUN BRANCH *) LVarToString (G, I.LVar (ref NONE, sk, (cid, t))) =
          "#" ^ I.conDecName (I.sgnLookup cid) ^ "["
          ^ subToString (G, t) ^ "]" (* GEN END FUN BRANCH *)

    (* some well-formedness conditions are assumed for input expressions *)
    (* e.g. don't contain "Kind", Evar's are consistently instantiated, ... *)

    (* checkExp (G, (U, s1), (V2, s2)) = ()

       Invariant:
       If   G |- s1 : G1
       and  G |- s2 : G2    G2 |- V2 : L
       returns () if there is a V1 s.t.
            G1 |- U : V1
       and  G  |- V1 [s1] = V2 [s2] : L
       otherwise exception Error is raised
    *)
    fun checkExp (G, Us, Vs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Us' = inferExp (G, Us) (* GEN END TAG OUTSIDE LET *)
        in
          if Conv.conv (Us', Vs) then ()
          else raise Error ("Type mismatch")
        end

    and inferUni (I.Type) = I.Kind
        (* impossible: Kind *)

    (* inferExp (G, (U, s)) = (V', s')

       Invariant:
       If   G  |- s : G1
       then if G1 |- U : V   (U doesn't contain EVAR's, FVAR's)
            then  G  |- s' : G'     G' |- V' : L
            and   G  |- V [s] = V'[s'] : L
            else exception Error is raised.
     *)
    and (* GEN BEGIN FUN FIRST *) inferExpW (G, (I.Uni (L), _)) = (I.Uni (inferUni L), I.id) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inferExpW (G, (I.Pi ((D, _) , V), s)) =
          (checkDec (G, (D, s));
           inferExp (I.Decl (G, I.decSub (D, s)), (V, I.dot1 s))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExpW (G, (I.Root (C, S), s)) =
          inferSpine (G, (S, s), Whnf.whnf (inferCon (G, C), I.id)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferExpW (G, (I.Lam (D, U), s)) =
          (checkDec (G, (D, s));
           (I.Pi ((I.decSub (D, s), I.Maybe),
                  I.EClo (inferExp (I.Decl (G, I.decSub (D, s)), (U, I.dot1 s)))), I.id)) (* GEN END FUN BRANCH *)
      (* no cases for Redex, EVars and EClo's *)
      | (* GEN BEGIN FUN BRANCH *) inferExpW (G, (I.FgnExp csfe, s)) =
          inferExp (G, (I.FgnExpStd.ToInternal.apply csfe (), s)) (* GEN END FUN BRANCH *)    (* AK: typecheck a representative -- presumably if one rep checks, they all do *)

    (* inferExp (G, Us) = (V', s')

       Invariant: same as inferExp, argument is not in whnf
    *)
    and inferExp (G, Us) = inferExpW (G, Whnf.whnf Us)

    (* inferSpine (G, (S, s1), (V, s2)) = (V', s')

       Invariant:
       If   G |- s1 : G1
       and  G |- s2 : G2  and  G2 |- V : L ,   (V, s2) in whnf
       and  (S,V  don't contain EVAR's, FVAR's)
       then if   there ex V1, V1'  G1 |- S : V1 > V1'
            then G |- s' : G'    and  G' |- V' : L
            and  G |- V1 [s1]   = V [s2] : L
            and  G |- V1'[s1]   = V' [s'] : L
    *)
    and (* GEN BEGIN FUN FIRST *) inferSpine (G, (I.Nil, _), Vs) = Vs (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inferSpine (G, (I.SClo (S, s'), s), Vs) =
          inferSpine (G, (S, I.comp (s', s)), Vs) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferSpine (G, (I.App (U, S), s1), (I.Pi ((I.Dec (_, V1), _), V2), s2)) =
          (checkExp(G, (U, s1), (V1, s2));
           inferSpine (G, (S, s1), Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2)))) (* GEN END FUN BRANCH *)
          (* G |- Pi (x:V1, V2) [s2] = Pi (x: V1 [s2], V2 [1.s2 o ^1] : L
             G |- U [s1] : V1 [s2]
             Hence
             G |- S [s1] : V2 [1. s2 o ^1] [U [s1], id] > V' [s']
             which is equal to
             G |- S [s1] : V2 [U[s1], s2] > V' [s']

             Note that G |- U[s1] : V1 [s2]
             and hence V2 must be under the substitution    U[s1]: V1, s2
          *)
      | (* GEN BEGIN FUN BRANCH *) inferSpine (G, Ss as (I.App _, _), Vs as (I.Root (I.Def _, _), _)) =
          inferSpine (G, Ss, Whnf.expandDef Vs) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferSpine (G, (I.App (U , S), _), (V, s)) = (* V <> (Pi x:V1. V2, s) *)
          raise  Error ("Expression is applied, but not a function") (* GEN END FUN BRANCH *)

    (* inferCon (G, C) = V'

       Invariant:
       If    G |- C : V
       and  (C  doesn't contain FVars)
       then  G' |- V' : L      (for some level L)
       and   G |- V = V' : L
       else exception Error is raised.
    *)
    and (* GEN BEGIN FUN FIRST *) inferCon (G, I.BVar (k')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V) = I.ctxDec (G, k') (* GEN END TAG OUTSIDE LET *)
        in
          V
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inferCon (G, I.Proj (B,  i)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V) = I.blockDec (G, B, i) (* GEN END TAG OUTSIDE LET *)
        in
          V
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferCon (G, I.Const(c)) = I.constType (c) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferCon (G, I.Def(d))  = I.constType (d) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inferCon (G, I.Skonst(c)) = I.constType (c) (* GEN END FUN BRANCH *) (* this is just a hack. --cs
                                                       must be extended to handle arbitrary
                                                       Skolem constants in the right way *)
      (* no case for FVar *)
      | (* GEN BEGIN FUN BRANCH *) inferCon (G, I.FgnConst(cs, conDec)) = I.conDecType(conDec) (* GEN END FUN BRANCH *)


    and typeCheck (G, (U, V)) =
          (checkCtx G; checkExp (G, (U, I.id), (V, I.id)))


    (* checkSub (G1, s, G2) = ()

       Invariant:
       The function terminates
       iff  G1 |- s : G2
    *)
    and (* GEN BEGIN FUN FIRST *) checkSub (I.Null, I.Shift 0, I.Null) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (I.Decl (G, D), I.Shift k, I.Null) =
        if k>0 then checkSub (G, I.Shift (k-1), I.Null)
        else raise Error "Substitution not well-typed" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (G', I.Shift k, G) =
          checkSub (G', I.Dot (I.Idx (k+1), I.Shift (k+1)), G) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (G', I.Dot (I.Idx k, s'), I.Decl (G, (I.Dec (_, V2)))) =
        (* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkSub (G', s', G) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V1) = I.ctxDec (G', k) (* GEN END TAG OUTSIDE LET *)
        in
          if Conv.conv ((V1, I.id), (V2, s')) then ()
          else raise Error ("Substitution not well-typed \n  found: " ^
                            Print.expToString (G', V1) ^ "\n  expected: " ^
                            Print.expToString (G', I.EClo (V2, s')))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (G', I.Dot (I.Exp (U), s'), I.Decl (G, (I.Dec (_, V2)))) =
        (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkSub (G', s', G) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = typeCheck (G', (U, I.EClo (V2, s'))) (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (G', I.Dot (I.Idx w, t), I.Decl (G, (I.BDec (_, (l, s))))) =
        (* Front of the substitution cannot be a I.Bidx or LVar *)
        (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkSub (G', t, G) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val I.BDec (_, (l', s')) = I.ctxDec (G', w) (* GEN END TAG OUTSIDE LET *)
          (* G' |- s' : GSOME *)
          (* G  |- s  : GSOME *)
          (* G' |- t  : G       (verified below) *)
        in
          if (l <> l')
            then raise Error "Incompatible block labels found"
          else
            if Conv.convSub (I.comp (s, t), s')
              then ()
            else raise Error "Substitution in block declaration not well-typed"
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (G', I.Dot (I.Block (I.Inst I), t), I.Decl (G, (I.BDec (_, (l, s))))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkSub (G', t, G) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (G, L) = I.constBlock l (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkBlock (G', I, (I.comp (s, t), L)) (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (G', s as I.Dot (_, _), I.Null) =
        raise Error ("Long substitution" ^ "\n" ^ subToString (G', s)) (* GEN END FUN BRANCH *)
      (*
      | checkSub (G', I.Dot (I.Block (I.Bidx _), t), G) =
        raise Error "Unexpected block index in substitution"
      | checkSub (G', I.Dot (I.Block (I.LVar _), t), G) =
        raise Error "Unexpected LVar in substitution after abstraction"
      *)

    and (* GEN BEGIN FUN FIRST *) checkBlock (G, nil, (_, nil)) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkBlock (G, U :: I, (t, I.Dec (_, V) :: L)) =
        (checkExp (G, (U, I.id), (V, t)); checkBlock (G, I, (I.Dot (I.Exp U, t), L))) (* GEN END FUN BRANCH *)

    (* checkDec (G, (x:V, s)) = B

       Invariant:
       If G |- s : G1
       then B iff G |- V[s] : type
    *)
    and (* GEN BEGIN FUN FIRST *) checkDec (G, (I.Dec (_, V) ,s)) =
          checkExp (G, (V, s), (I.Uni (I.Type), I.id)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkDec (G, (I.BDec (_, (c, t)), s)) =
          let
            (* G1 |- t : GSOME *)
            (* G  |- s : G1 *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (Gsome, piDecs) = I.constBlock c (* GEN END TAG OUTSIDE LET *)
          in
            checkSub (G, I.comp (t, s), Gsome)
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkDec (G, (NDec, _)) = () (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) checkCtx (I.Null) =  () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkCtx (I.Decl (G, D)) =
          (checkCtx G; checkDec (G, (D, I.id))) (* GEN END FUN BRANCH *)


    fun check (U, V) = checkExp (I.Null, (U, I.id), (V, I.id))
    fun infer U = I.EClo (inferExp (I.Null, (U, I.id)))
    fun infer' (G, U) = I.EClo (inferExp (G, (U, I.id)))



    fun checkConv (U1, U2) =
          if Conv.conv ((U1, I.id), (U2, I.id)) then ()
          else raise Error ("Terms not equal\n  left: " ^
                            Print.expToString (I.Null, U1) ^ "\n  right:" ^
                            Print.expToString (I.Null, U2))


  in
      (* GEN BEGIN TAG OUTSIDE LET *) val check = check (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val checkDec = checkDec (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val checkConv = checkConv (* GEN END TAG OUTSIDE LET *)

      (* GEN BEGIN TAG OUTSIDE LET *) val infer = infer (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val infer' = infer' (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val typeCheck = typeCheck (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val typeCheckCtx = checkCtx (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val typeCheckSub = checkSub (* GEN END TAG OUTSIDE LET *)
  end  (* local ... *)
end (* GEN END FUNCTOR DECL *); (* functor TypeCheck *)
