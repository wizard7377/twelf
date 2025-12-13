(* Redundancy remover (factoring) *)
(* Author: Adam Poswolsky (ABP) *)

functor (* GEN BEGIN FUNCTOR DECL *) Redundant (structure Opsem : OPSEM) : REDUNDANT  =
  struct
    exception Error of string

    (*
     convert:  Tomega.Prg -> Tomega.Prg
     Attempts to eliminate *redundant* cases.
     *)
    structure T = Tomega
    structure I = IntSyn

    fun optionRefEqual (r1, r2, func) =
      if (r1 = r2) then
        true
      else
        (case (r1, r2)
           of (ref NONE, ref NONE) => true
           |  (ref (SOME (P1)), ref (SOME (P2))) => func(P1, P2)
           |  _ => false
        )

    fun (* GEN BEGIN FUN FIRST *) convert (T.Lam (D, P)) = T.Lam (D, convert P) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.New P) = T.New (convert P) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.Choose P) = T.Choose (convert P) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.PairExp (M, P)) = T.PairExp (M, convert P) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.PairBlock (rho, P)) = T.PairBlock (rho, convert P) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.PairPrg (P1, P2)) = T.PairPrg (convert P1, convert P2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.Unit) = T.Unit (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.Var x) = T.Var x (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.Const x) = T.Const x (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.Redex (P, S)) = T.Redex (convert P, convertSpine S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.Rec (D, P)) = T.Rec (D, convert P) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.Case (T.Cases O)) = T.Case (T.Cases (convertCases O)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convert (T.Let (D,P1,P2)) = T.Let (D, convert P1, convert P2) (* GEN END FUN BRANCH *)
    (* No EVARs will occur
      | convert (T.PClo (P,t)) = raise Error "No PClo should exist" (* T.PClo (convert P, t) *)
      | convert (T.EVar (D, P as ref NONE, F)) = T.EVar (D, P, F)
      | convert (T.EVar (D, ref (SOME P), F)) = convert P (* some opsem here *)
    *)


    and (* GEN BEGIN FUN FIRST *) convertSpine (T.Nil) = T.Nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) convertSpine (T.AppExp (I, S)) = (T.AppExp (I, convertSpine S)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convertSpine (T.AppBlock (I, S)) = (T.AppBlock (I, convertSpine S)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convertSpine (T.AppPrg (P, S)) = (T.AppPrg (convert P, convertSpine S)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convertSpine (T.SClo (S, t)) = raise Error "SClo should not exist" (* GEN END FUN BRANCH *)
                             (* (T.SClo (convertSpine S, t)) *)


    and expEqual (E1, E2) = Conv.conv ( (E1, I.id), (E2, I.id) )


    and IsubEqual (sub1, sub2) = Conv.convSub(sub1, sub2) (* Note that it doesn't handle blocks *)


    and (* GEN BEGIN FUN FIRST *) blockEqual (I.Bidx x, I.Bidx x') = (x=x') (* GEN END FUN FIRST *)
      (* Should not occur -- ap 2/18/03 *)
      | (* GEN BEGIN FUN BRANCH *) blockEqual (I.LVar (r, sub1, (cid, sub2)), I.LVar (r', sub1', (cid', sub2'))) =
          optionRefEqual(r,r',blockEqual) andalso IsubEqual(sub1, sub1') andalso (cid = cid') andalso IsubEqual(sub1', sub2') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) blockEqual _ = false (* GEN END FUN BRANCH *)


    and (* GEN BEGIN FUN FIRST *) decEqual ( T.UDec (D1), (T.UDec (D2), t2) ) = Conv.convDec ((D1, I.id),(D2, T.coerceSub(t2))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decEqual ( T.PDec (_, F1, _, _), (T.PDec (_, F2, _, _), t2) ) = T.convFor ((F1, T.id), (F2, t2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) decEqual _ = false (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) caseEqual (((Psi1, t1, P1)::O1), (((Psi2, t2, P2)::O2), tAfter)) =
            (* Recall that we (Psi2, t2, P2)[tAfter] = (Psi2, (tAfterInv \circ t2), P2) *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val t2' = T.comp(T.invertSub(tAfter),t2) (* GEN END TAG OUTSIDE LET *)
              (* Note:  (Psi1 |- t1: Psi0) *)
              (* GEN BEGIN TAG OUTSIDE LET *) val t = Opsem.createVarSub(Psi1, Psi2) (* GEN END TAG OUTSIDE LET *) (* Psi1 |- t: Psi2 *)
              (* GEN BEGIN TAG OUTSIDE LET *) val t' = T.comp(t2', t) (* GEN END TAG OUTSIDE LET *) (* Psi1 |- t' : Psi_0 *)
              (* GEN BEGIN TAG OUTSIDE LET *) val doMatch = (Opsem.matchSub (Psi1, t1, t') ; true)
                handle NoMatch => false (* GEN END TAG OUTSIDE LET *)
            in
              if (doMatch) then
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val newT = T.normalizeSub t (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val stillMatch = IsSubRenamingOnly(newT) (* GEN END TAG OUTSIDE LET *)
                in
                  (stillMatch andalso prgEqual(P1, (P2, cleanSub(newT))))
                end
              else
                false
            end (* GEN END FUN FIRST *)


      | (* GEN BEGIN FUN BRANCH *) caseEqual (nil, (nil, t2)) = true (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) caseEqual _ = false (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) spineEqual ( (T.Nil), (T.Nil, t2) ) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) spineEqual ( (T.AppExp(E1,S1)), (T.AppExp(E2,S2), t2) ) = (Conv.conv( (E1,I.id), (E2, T.coerceSub(t2)) ) andalso spineEqual(S1,(S2,t2))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) spineEqual ( (T.AppBlock (B1,S1)), (T.AppBlock(B2,S2), t2) ) = (blockEqual( B1, I.blockSub (B2, T.coerceSub t2)) andalso spineEqual(S1,(S2,t2))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) spineEqual ( (T.AppPrg (P1,S1)), (T.AppPrg(P2,S2), t2) ) = (prgEqual(P1, (P2, t2)) andalso spineEqual(S1, (S2,t2))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) spineEqual ( T.SClo(S,t1), (T.SClo(s,t2a), t2) ) =
      (* there are no SClo created in converter *) raise Error "SClo should not exist!" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) spineEqual _ = false (* GEN END FUN BRANCH *)


    and (* GEN BEGIN FUN FIRST *) prgEqual ((T.Lam (D1, P1)), (T.Lam (D2, P2), t2)) = (decEqual(D1, (D2,t2)) andalso prgEqual(P1, (P2, T.dot1 t2))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.New P1), (T.New P2, t2)) = prgEqual(P1, (P2, t2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.Choose P1), (T.Choose P2, t2)) = prgEqual(P1, (P2, t2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.PairExp (U1, P1)), (T.PairExp (U2, P2), t2)) = (Conv.conv((U1, I.id),(U2,(T.coerceSub t2))) andalso prgEqual((P1), (P2, t2))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.PairBlock (B1, P1)), (T.PairBlock (B2, P2), t2)) = (blockEqual(B1, (I.blockSub(B2, T.coerceSub t2))) andalso prgEqual(P1,(P2,t2))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.PairPrg (P1a, P1b)), (T.PairPrg (P2a, P2b), t2)) = (prgEqual(P1a, (P2a, t2)) andalso prgEqual(P1b, (P2b, t2))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.Unit), (T.Unit, t2)) = true (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual (T.Const lemma1, (T.Const lemma2, _)) = (lemma1=lemma2) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual (T.Var x1, (T.Var x2, t2)) =
                     (case getFrontIndex(T.varSub(x2,t2)) of
                           NONE => false
                         | SOME i => (x1 = i)) (* GEN END FUN BRANCH *)

(*      | prgEqual ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) => ((lemma1=lemma2) andalso (spineEqual(S1, (S2,t2))))
                 |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => false
                            | SOME i => ((x1 = i) andalso (spineEqual(S1, (S2,t2)))))
                 |  _ => false)
*)
      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.Redex (P1, S1)), (T.Redex (P2, S2), t2)) = (prgEqual(P1, (P2,t2)) andalso spineEqual(S1, (S2,t2))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.Rec (D1, P1)), (T.Rec (D2, P2), t2)) = (decEqual(D1, (D2,t2)) andalso prgEqual(P1, (P2,T.dot1 t2))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.Case (T.Cases O1)), (T.Case (T.Cases O2), t2)) = caseEqual(O1, (O2, t2)) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.Let (D1, P1a, P1b)), (T.Let (D2, P2a, P2b), t2)) = (decEqual(D1, (D2, t2)) andalso prgEqual(P1a, (P2a, t2))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.PClo (P1, t1)), (T.PClo (P2, t2a), t2b)) = (* there are no PClo created in converter *) raise Error "PClo should not exist!" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual ((T.EVar (Psi1, P1optRef, F1, _, _, _)), (T.EVar (Psi2, P2optref, F2, _, _, _), t2)) = raise Error "No EVARs should exist!" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) prgEqual _ = false (* GEN END FUN BRANCH *)


    (* convertCases is where the real work comes in *)
    (* will attempt to merge cases together and call convert
     * on what happens in each case
     *)
    and (* GEN BEGIN FUN FIRST *) convertCases (A::C) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val ((Psi,t,P),C') = removeRedundancy(A,C) (* GEN END TAG OUTSIDE LET *)
      in
        ((Psi,t,convert(P))::convertCases(C'))
      end (* GEN END FUN FIRST *)

      | (* GEN BEGIN FUN BRANCH *) convertCases C = C (* GEN END FUN BRANCH *) (* will be T.Cases nil *)


    (* Returns a list with C (merged with redundant cases) as the head followed by the rest *)
    and (* GEN BEGIN FUN FIRST *) removeRedundancy (C, []) = (C, []) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) removeRedundancy ( C, C'::rest) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (C''::Cs) = mergeIfNecessary(C, C') (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (C''', rest') = removeRedundancy(C'', rest) (* GEN END TAG OUTSIDE LET *)
             in
              (C''', Cs @ rest')
            end (* GEN END FUN BRANCH *)

    (* returns NONE if not found *)
    and (* GEN BEGIN FUN FIRST *) getFrontIndex (T.Idx k) = SOME(k) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) getFrontIndex (T.Prg P) = getPrgIndex(P) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) getFrontIndex (T.Exp U) = getExpIndex(U) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) getFrontIndex (T.Block B) = getBlockIndex(B) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) getFrontIndex (T.Undef) = NONE (* GEN END FUN BRANCH *)


    (* getPrgIndex returns NONE if it is not an index *)
    and (* GEN BEGIN FUN FIRST *) getPrgIndex (T.Var k) = SOME(k) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) getPrgIndex (T.Redex(P, T.Nil) ) = getPrgIndex(P) (* GEN END FUN BRANCH *)

      (* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
      | (* GEN BEGIN FUN BRANCH *) getPrgIndex (T.PClo (P,t)) =
            (case getPrgIndex(P) of
              NONE => NONE
            | SOME i => getFrontIndex (T.varSub (i, t))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) getPrgIndex _ = NONE (* GEN END FUN BRANCH *)

    (* getExpIndex returns NONE if it is not an index *)
    and (* GEN BEGIN FUN FIRST *) getExpIndex (I.Root (I.BVar k, I.Nil)) = SOME(k) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) getExpIndex (I.Redex (U, I.Nil)) = getExpIndex(U) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) getExpIndex (I.EClo (U, t)) =
            (case getExpIndex(U) of
               NONE => NONE
             | SOME i => getFrontIndex (T.revCoerceFront(I.bvarSub(i, t)))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) getExpIndex (U as I.Lam (I.Dec (_, U1), U2)) = (SOME ( Whnf.etaContract(U) )  handle Whnf.Eta => NONE) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) getExpIndex _ = NONE (* GEN END FUN BRANCH *)

    (* getBlockIndex returns NONE if it is not an index *)
    and (* GEN BEGIN FUN FIRST *) getBlockIndex (I.Bidx k) = SOME(k) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) getBlockIndex _ = NONE (* GEN END FUN BRANCH *)



    (* clean up the renaming substitution,
       this is to allow T.invertSub to appropriately
       think it is a pattern substitution
       *)
    and (* GEN BEGIN FUN FIRST *) cleanSub (S as T.Shift _) = S (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) cleanSub (T.Dot(Ft1,s1)) =
         (case getFrontIndex(Ft1) of
            NONE => T.Dot(Ft1, cleanSub(s1))
          | SOME index =>  T.Dot(T.Idx index, cleanSub(s1))) (* GEN END FUN BRANCH *)


    (* determine if t is simply a renaming substitution *)
    and (* GEN BEGIN FUN FIRST *) IsSubRenamingOnly (T.Shift(n)) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) IsSubRenamingOnly (T.Dot(Ft1,s1)) =
          (case getFrontIndex(Ft1) of
             NONE => false
           | SOME _ => true)
      
          andalso IsSubRenamingOnly (s1) (* GEN END FUN BRANCH *)

    (* Note that what we are merging it with will need to go under an extra renaming substitution *)

    and (* GEN BEGIN FUN FIRST *) mergeSpines ( (T.Nil), (T.Nil, t2) ) = T.Nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) mergeSpines ( (T.AppExp(E1,S1)), (T.AppExp(E2,S2), t2) ) =
            if Conv.conv( (E1,I.id), (E2, T.coerceSub(t2)) ) then
              T.AppExp(E1, mergeSpines(S1,(S2,t2)))
            else
              raise Error "Spine not equal (AppExp)" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergeSpines ( (T.AppBlock (B1,S1)), (T.AppBlock(B2,S2), t2) ) =
            if blockEqual( B1, I.blockSub (B2, T.coerceSub t2))  then
              T.AppBlock(B1, mergeSpines(S1,(S2,t2)))
            else
              raise Error "Spine not equal (AppBlock)" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergeSpines ( (T.AppPrg (P1,S1)), (T.AppPrg(P2,S2), t2) ) =
                if (prgEqual(P1, (P2, t2))) then
                  T.AppPrg(P1, mergeSpines(S1, (S2,t2)))
                else
                  raise Error "Prg (in App) not equal" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergeSpines ( T.SClo(S,t1), (T.SClo(s,t2a), t2) ) =
      (* there are no SClo created in converter *) raise Error "SClo should not exist!" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergeSpines _ = raise Error "Spine are not equivalent" (* GEN END FUN BRANCH *)


    and (* GEN BEGIN FUN FIRST *) mergePrgs ((T.Lam (D1, P1)), (T.Lam (D2, P2), t2)) =
                                if (decEqual(D1, (D2,t2)) andalso prgEqual(P1, (P2, T.dot1 t2)))  then
                                   T.Lam(D1, P1)
                                else
                                    raise Error "Lambda don't match" (* GEN END FUN FIRST *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.New P1), (T.New P2, t2)) = if (prgEqual(P1, (P2, t2))) then T.New P1 else
                                      raise Error "New don't match" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.Choose P1), (T.Choose P2, t2)) = if (prgEqual(P1, (P2, t2))) then T.Choose P1 else
                                      raise Error "Choose don't match" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.PairExp (U1, P1)), (T.PairExp (U2, P2), t2)) =
                        let
                          (* GEN BEGIN TAG OUTSIDE LET *) val t2' = T.coerceSub t2 (* GEN END TAG OUTSIDE LET *)
                        in
                             if (Conv.conv((U1, I.id),(U2,t2'))) then
                                T.PairExp (U1, mergePrgs((P1), (P2, t2)))
                             else
                                raise Error "cannot merge PairExp"
                        end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.PairBlock (B1, P1)), (T.PairBlock (B2, P2), t2)) =
                        let
                          (* GEN BEGIN TAG OUTSIDE LET *) val B2' = I.blockSub (B2, T.coerceSub t2) (* GEN END TAG OUTSIDE LET *)
                        in
                          if (blockEqual (B1, B2')) then
                                T.PairBlock (B1, mergePrgs((P1),(P2, t2)))
                          else
                                raise Error "cannot merge PairBlock"
                        end (* GEN END FUN BRANCH *)


      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.PairPrg (P1a, P1b)), (T.PairPrg (P2a, P2b), t2)) =
                        if (prgEqual(P1a, (P2a, t2))) then
                          T.PairPrg (P1a, (mergePrgs( (P1b),(P2b, t2) )))
                        else
                          raise Error "cannot merge PairPrg" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.Unit), (T.Unit, t2)) = T.Unit (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs (T.Const lemma1, (T.Const lemma2, _)) =
                   if (lemma1=lemma2) then T.Const lemma1
                   else raise Error "Constants do not match." (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs (T.Var x1, (T.Var x2, t2)) =
                     (case getFrontIndex(T.varSub(x2,t2)) of
                           NONE => raise Error "Variables do not match."
                         | SOME i =>
                             (if (x1 = i) then T.Var x1
                              else raise Error "Variables do not match.")) (* GEN END FUN BRANCH *)

(*      | mergePrgs ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) =>
                     if (lemma1=lemma2) then
                        T.Root (H1, mergeSpines((S1),(S2,t2)))
                     else raise Error "Roots do not match"
                   |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => raise Error "Root does not match."
                            | SOME i =>
                                (if (x1 = i) then
                                   T.Root (T.Var x1, mergeSpines((S1),(S2,t2)))
                                 else
                                   raise Error "Root does not match."))
                   |  _ => raise Error "Root does not match.")
*)
      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.Redex (P1, S1)), (T.Redex (P2, S2), t2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val newS = mergeSpines(S1, (S2, t2)) (* GEN END TAG OUTSIDE LET *)
        in
          if (prgEqual (P1, (P2, t2))) then
            T.Redex(P1, newS)
          else
            raise Error "Redex Prgs don't match"
        end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.Rec (D1, P1)), (T.Rec (D2, P2), t2)) =
        if (decEqual(D1, (D2,t2)) andalso prgEqual(P1, (P2,T.dot1 t2)))  then
            T.Rec(D1, P1)
        else
          raise Error "Rec's don't match" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs ( (T.Case (T.Cases O1)), (T.Case (T.Cases [C]), t2)) =
                (* check the case now *)
                (* three possible outcomes -
                   (1) We merge the cases together
                   (2) Cases are incompatible (duplicated)
                   (3) Cases are duplicate but all results are the same
                       which means we need to continue merging
                 *)
                T.Case (T.Cases (mergeCase(O1, (C,t2)))) (* GEN END FUN BRANCH *)


      (* By invariant the second case should be a list of one *)
      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.Case O1), (T.Case O2, t2)) = raise Error "Invariant Violated" (* GEN END FUN BRANCH *)


      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.PClo (P1, t1)), (T.PClo (P2, t2a), t2b)) = (* there are no PClo created in converter *) raise Error "PClo should not exist!" (* GEN END FUN BRANCH *)


      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.Let (D1, P1a, P1b)), (T.Let (D2, P2a, P2b), t2)) =
                if (decEqual(D1, (D2, t2)) andalso prgEqual(P1a, (P2a, t2))) then
                  T.Let(D1, P1a, mergePrgs((P1b), (P2b,T.dot1 t2)))
                else
                  raise Error "Let don't match" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs ((T.EVar (Psi1, P1optRef, F1, _, _, _)), (T.EVar (Psi2, P2optref, F2, _, _, _), t2)) = raise Error "No EVARs should exist!" (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) mergePrgs _ = raise Error "Redundancy in cases could not automatically be removed." (* GEN END FUN BRANCH *)

(*
    (* For debug purposes *)
    and printCtx(Psi) =
      let
        fun printDec ( T.UDec (I.Dec (SOME(s), E)) ) =  (print s ; print ": "; print (Print.expToString (T.coerceCtx Psi, E)); print "\n" )
          | printDec ( T.UDec (I.BDec (SOME(s), (cid, sub)))) = (print s ; print ":\n")
          | printDec ( T.UDec (I.ADec (SOME(s), i))) = (print s ; print ":(ADec\n")
          | printDec ( T.UDec (I.NDec) ) = (print "(NDec)\n")
          | printDec ( T.PDec (SOME(s), F)) = (print s ; print ":(PDec)\n")
      in
        case Psi of
          (I.Null) => (print "Null\n")
          | (I.Decl (G, D)) =>  (printCtx(G) ; printDec(D))
      end
*)

    (* invertSub s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)
    and invertSub s =
      let
        fun (* GEN BEGIN FUN FIRST *) lookup (n, T.Shift _, p) = NONE (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) lookup (n, T.Dot (T.Undef, s'), p) = lookup (n+1, s', p) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) lookup (n, T.Dot (Ft, s'), p) =
              (case getFrontIndex(Ft) of
                 NONE => lookup (n+1, s', p)
               | SOME k => if (k=p) then SOME n else lookup (n+1, s', p)) (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) invertSub'' (0, si) = si (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) invertSub'' (p, si) =
            (case (lookup (1, s, p))
               of SOME k => invertSub'' (p-1, T.Dot (T.Idx k, si))
                | NONE => invertSub'' (p-1, T.Dot (T.Undef, si))) (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) invertSub' (n, T.Shift p) = invertSub'' (p, T.Shift n) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) invertSub' (n, T.Dot (_, s')) = invertSub' (n+1, s') (* GEN END FUN BRANCH *)
      in
        invertSub' (0, s)
      end



(* debug *)
    and (* GEN BEGIN FUN FIRST *) printSub (T.Shift k) = print ("Shift " ^ Int.toString(k) ^ "\n") (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) printSub (T.Dot (T.Idx k, s)) = (print ("Idx " ^ Int.toString(k) ^ " (DOT) " ) ; printSub(s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) printSub (T.Dot (T.Prg (T.EVar _), s)) = (print ("PRG_EVAR (DOT) " ) ; printSub(s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) printSub (T.Dot (T.Exp (I.EVar _), s)) = (print ("EXP_EVAR (DOT) " ) ; printSub(s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) printSub (T.Dot (T.Prg P, s)) = (print ("PRG (DOT) " ) ; printSub(s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) printSub (T.Dot (T.Exp E, s)) = (print ("EXP (DOT) " ) ; printSub(s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) printSub (T.Dot (T.Block B, s)) = (print ("BLOCK (DOT) " ) ; printSub(s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) printSub (T.Dot (T.Undef, s)) = (print ("UNDEF. (DOT) " ) ; printSub(s)) (* GEN END FUN BRANCH *)


    (* We need to return it in terms of the context of the first *)
    and (* GEN BEGIN FUN FIRST *) mergeCase ( [], C ) = raise Error "Case incompatible, cannot merge" (* GEN END FUN FIRST *)

      | (* GEN BEGIN FUN BRANCH *) mergeCase (L as (Psi1, t1, P1)::O,  C as ((Psi2, t2, P2), tAfter)) =
      let
      
        (*
        val _ = printCtx(Psi1)
        val _ = printCtx(Psi2)
          *)
      
        (* Psi1 |- P1 : F[t1] *)
        (* Psi2 |- P2 : F[t2] *)
      
        (* Psi1 |- t1 : Psi1' *)
        (* Psi2 |- t2 : Psi2' *)
      
        (* By invariant,we assume *)
        (* Psi1' |- tAfter: Psi2' *)
      
        (* Psi2' |- tAfterInv : Psi1' *)
      
        (* GEN BEGIN TAG OUTSIDE LET *) val tAfterInv = T.invertSub(tAfter) (* GEN END TAG OUTSIDE LET *)
      
      
        (* GEN BEGIN TAG OUTSIDE LET *) val t3 = T.comp(tAfterInv, t2) (* GEN END TAG OUTSIDE LET *)
      
        (* So now we have
         P1 makes sense in Psi1, t1 goes from Psi1' to Psi1.
      
         Psi1 |- t1 : Psi1'
         Psi2 |- t3 : Psi1'
         *)
      
        (* GEN BEGIN TAG OUTSIDE LET *) val t = Opsem.createVarSub (Psi1, Psi2) (* GEN END TAG OUTSIDE LET *) (* Psi1 |- t : Psi2 *)
        (* GEN BEGIN TAG OUTSIDE LET *) val t' = T.comp (t3, t) (* GEN END TAG OUTSIDE LET *) (* Psi1 |- t' : Psi1' *)
      
        (* If we can get this to match, then Psi1 |- P2[t] *)
        (* GEN BEGIN TAG OUTSIDE LET *) val doMatch = (Opsem.matchSub (Psi1, t1, t') ; true)
          handle NoMatch => false (* GEN END TAG OUTSIDE LET *)
      
      in
        if (doMatch) then
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val newT = T.normalizeSub t (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val stillMatch = IsSubRenamingOnly(newT) (* GEN END TAG OUTSIDE LET *)
          in
            if (stillMatch) then
          (* Since the case matches, lets continue the merge on P1 and P2
           * Note that removing the redundancy of other case statements
           * is handled recursively ... see convertCases
           *)
              (* Note that tAfter and newT are both renaming substitutions *)
              (Psi1, t1, mergePrgs(P1,(P2,cleanSub(newT))))::O
            else
              if (length(O) = 0) then
                (* We tried all the cases, and we can now add it *)
                (Psi2, t3, P2)::L
              else
                (* Try other cases *)
                (Psi1, t1, P1)::mergeCase(O,C)
          end
      
        else
          if (length(O) = 0) then
            (* We tried all the cases, and we can now add it *)
            (Psi2, t3, P2)::L
      
          else
            (* Try other cases *)
            (Psi1, t1, P1)::mergeCase(O,C)
      end (* GEN END FUN BRANCH *)

  (* mergeIfNecessary
   * Simply see if C is the same case as C'
   * If so, try to merge them together and return a list of just the case merged together,
   * otherwise, return a list of both elements.
   *)
    and mergeIfNecessary(C as (Psi1, s1, P1), C' as (Psi2, s2, P2)) =
      let
     (* Note that s1 is a substitution s.t.  Psi1 |- s1: Psi0
        and s2 is a substitution s.t.         Psi2 |- s2: Psi0
    
        It is possible that this property is lost when the case is executed
        with a different Psi0 which can happen during recursive calls
        (as the context grows).
    
        In that case:
          Psi, Psi1 |- X1...Xn, id{Psi} : Psi, Psi2
    
        Therefore, the X's are not dependent on the extra Psi introduced
        by recursive calls, which is why they are ignored in matchSub as well.
    
        We will generate a substitution t s.t. Psi1 |- t: Psi2
        Therefore  Psi1 |- (s2 o t) : Psi0
    
        And we are trying to match it with
                   Psi1 |- s1 : Psi0
    
      *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val t = Opsem.createVarSub (Psi1, Psi2) (* GEN END TAG OUTSIDE LET *) (* Psi1 |- t : Psi2 *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val t' = T.comp (s2, t) (* GEN END TAG OUTSIDE LET *)
     (* Now since s1 and t' go between the same contexts, we see
      * if we can unify them
      *)
        (* GEN BEGIN TAG OUTSIDE LET *) val doMatch = (Opsem.matchSub (Psi1, s1, t') ; true)
          handle NoMatch => false (* GEN END TAG OUTSIDE LET *)
    
      in
        if (not doMatch) then
          [C,C']
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val newT = T.normalizeSub t (* GEN END TAG OUTSIDE LET *)
          in
            if (IsSubRenamingOnly(newT)) then
              [(Psi1, s1, mergePrgs((P1), (P2, cleanSub(newT))))]
              (* In this case, C' is redundant and cannot be fixed, so C' will never be called
               * [C,C']
               *)
              handle Error s => (* (print ("***WARNING*** -- redundant case automatically ANNIHILATED:  " ^ s ^ "\n") ; [C]) *)
                raise Error  ("***WARNING*** -- redundant case automatically ANNIHILATED:  " ^ s ^ "\n")
            else
              [C,C']
    
          end
    
      end


  end (* GEN END FUNCTOR DECL *)