(* Redundancy remover (factoring) *)


(* Author: Adam Poswolsky (ABP) *)


module Redundant (Opsem : OPSEM) : REDUNDANT = struct exception Error of string
(*
     convert:  Tomega.Prg -> Tomega.Prg
     Attempts to eliminate *redundant* cases.
     *)

module T = Tomega
module I = IntSyn
let rec optionRefEqual (r1, r2, func)  = if (r1 = r2) then true else (match (r1, r2) with ({ contents = None }, { contents = None }) -> true | ({ contents = (Some (P1)) }, { contents = (Some (P2)) }) -> func (P1, P2) | _ -> false)
let rec convert = function (T.Lam (D, P)) -> T.Lam (D, convert P) | (T.New P) -> T.New (convert P) | (T.Choose P) -> T.Choose (convert P) | (T.PairExp (M, P)) -> T.PairExp (M, convert P) | (T.PairBlock (rho, P)) -> T.PairBlock (rho, convert P) | (T.PairPrg (P1, P2)) -> T.PairPrg (convert P1, convert P2) | (T.Unit) -> T.Unit | (T.Var x) -> T.Var x | (T.Const x) -> T.Const x | (T.Redex (P, S)) -> T.Redex (convert P, convertSpine S) | (T.Rec (D, P)) -> T.Rec (D, convert P) | (T.Case (T.Cases O)) -> T.Case (T.Cases (convertCases O)) | (T.Let (D, P1, P2)) -> T.Let (D, convert P1, convert P2)
and convertSpine = function (T.Nil) -> T.Nil | (T.AppExp (I, S)) -> (T.AppExp (I, convertSpine S)) | (T.AppBlock (I, S)) -> (T.AppBlock (I, convertSpine S)) | (T.AppPrg (P, S)) -> (T.AppPrg (convert P, convertSpine S)) | (T.SClo (S, t)) -> raise (Error "SClo should not exist")
and expEqual (E1, E2)  = Conv.conv ((E1, I.id), (E2, I.id))
and IsubEqual (sub1, sub2)  = Conv.convSub (sub1, sub2)
and blockEqual = function (I.Bidx x, I.Bidx x') -> (x = x') | (I.LVar (r, sub1, (cid, sub2)), I.LVar (r', sub1', (cid', sub2'))) -> optionRefEqual (r, r', blockEqual) && IsubEqual (sub1, sub1') && (cid = cid') && IsubEqual (sub1', sub2') | _ -> false
and decEqual = function (T.UDec (D1), (T.UDec (D2), t2)) -> Conv.convDec ((D1, I.id), (D2, T.coerceSub (t2))) | (T.PDec (_, F1, _, _), (T.PDec (_, F2, _, _), t2)) -> T.convFor ((F1, T.id), (F2, t2)) | _ -> false
and caseEqual = function (((Psi1, t1, P1) :: O1), (((Psi2, t2, P2) :: O2), tAfter)) -> ( (* Note:  (Psi1 |- t1: Psi0) *)
(* Psi1 |- t: Psi2 *)
(* Psi1 |- t' : Psi_0 *)
let t2' = T.comp (T.invertSub (tAfter), t2) in let t = Opsem.createVarSub (Psi1, Psi2) in let t' = T.comp (t2', t) in let doMatch = try (Opsem.matchSub (Psi1, t1, t'); true) with NoMatch -> false in  if (doMatch) then ( let newT = T.normalizeSub t in let stillMatch = IsSubRenamingOnly (newT) in  (stillMatch && prgEqual (P1, (P2, cleanSub (newT)))) ) else false ) | ([], ([], t2)) -> true | _ -> false
and spineEqual = function ((T.Nil), (T.Nil, t2)) -> true | ((T.AppExp (E1, S1)), (T.AppExp (E2, S2), t2)) -> (Conv.conv ((E1, I.id), (E2, T.coerceSub (t2))) && spineEqual (S1, (S2, t2))) | ((T.AppBlock (B1, S1)), (T.AppBlock (B2, S2), t2)) -> (blockEqual (B1, I.blockSub (B2, T.coerceSub t2)) && spineEqual (S1, (S2, t2))) | ((T.AppPrg (P1, S1)), (T.AppPrg (P2, S2), t2)) -> (prgEqual (P1, (P2, t2)) && spineEqual (S1, (S2, t2))) | (T.SClo (S, t1), (T.SClo (s, t2a), t2)) -> raise (Error "SClo should not exist!") | _ -> false
and prgEqual = function ((T.Lam (D1, P1)), (T.Lam (D2, P2), t2)) -> (decEqual (D1, (D2, t2)) && prgEqual (P1, (P2, T.dot1 t2))) | ((T.New P1), (T.New P2, t2)) -> prgEqual (P1, (P2, t2)) | ((T.Choose P1), (T.Choose P2, t2)) -> prgEqual (P1, (P2, t2)) | ((T.PairExp (U1, P1)), (T.PairExp (U2, P2), t2)) -> (Conv.conv ((U1, I.id), (U2, (T.coerceSub t2))) && prgEqual ((P1), (P2, t2))) | ((T.PairBlock (B1, P1)), (T.PairBlock (B2, P2), t2)) -> (blockEqual (B1, (I.blockSub (B2, T.coerceSub t2))) && prgEqual (P1, (P2, t2))) | ((T.PairPrg (P1a, P1b)), (T.PairPrg (P2a, P2b), t2)) -> (prgEqual (P1a, (P2a, t2)) && prgEqual (P1b, (P2b, t2))) | ((T.Unit), (T.Unit, t2)) -> true | (T.Const lemma1, (T.Const lemma2, _)) -> (lemma1 = lemma2) | (T.Var x1, (T.Var x2, t2)) -> (match getFrontIndex (T.varSub (x2, t2)) with None -> false | Some i -> (x1 = i)) | ((T.Redex (P1, S1)), (T.Redex (P2, S2), t2)) -> (prgEqual (P1, (P2, t2)) && spineEqual (S1, (S2, t2))) | ((T.Rec (D1, P1)), (T.Rec (D2, P2), t2)) -> (decEqual (D1, (D2, t2)) && prgEqual (P1, (P2, T.dot1 t2))) | ((T.Case (T.Cases O1)), (T.Case (T.Cases O2), t2)) -> caseEqual (O1, (O2, t2)) | ((T.Let (D1, P1a, P1b)), (T.Let (D2, P2a, P2b), t2)) -> (decEqual (D1, (D2, t2)) && prgEqual (P1a, (P2a, t2))) | ((T.PClo (P1, t1)), (T.PClo (P2, t2a), t2b)) -> raise (Error "PClo should not exist!") | ((T.EVar (Psi1, P1optRef, F1, _, _, _)), (T.EVar (Psi2, P2optref, F2, _, _, _), t2)) -> raise (Error "No EVARs should exist!") | _ -> false
and convertCases = function (A :: C) -> ( let ((Psi, t, P), C') = removeRedundancy (A, C) in  ((Psi, t, convert (P)) :: convertCases (C')) ) | C -> C
and removeRedundancy = function (C, []) -> (C, []) | (C, C' :: rest) -> ( let (C'' :: Cs) = mergeIfNecessary (C, C') in let (C''', rest') = removeRedundancy (C'', rest) in  (C''', Cs @ rest') )
and getFrontIndex = function (T.Idx k) -> Some (k) | (T.Prg P) -> getPrgIndex (P) | (T.Exp U) -> getExpIndex (U) | (T.Block B) -> getBlockIndex (B) | (T.Undef) -> None
and getPrgIndex = function (T.Var k) -> Some (k) | (T.Redex (P, T.Nil)) -> getPrgIndex (P) | (T.PClo (P, t)) -> (match getPrgIndex (P) with None -> None | Some i -> getFrontIndex (T.varSub (i, t))) | _ -> None
and getExpIndex = function (I.Root (I.BVar k, I.Nil)) -> Some (k) | (I.Redex (U, I.Nil)) -> getExpIndex (U) | (I.EClo (U, t)) -> (match getExpIndex (U) with None -> None | Some i -> getFrontIndex (T.revCoerceFront (I.bvarSub (i, t)))) | (U) -> (try Some (Whnf.etaContract (U)) with Whnf.Eta -> None) | _ -> None
and getBlockIndex = function (I.Bidx k) -> Some (k) | _ -> None
and cleanSub = function (S) -> S | (T.Dot (Ft1, s1)) -> (match getFrontIndex (Ft1) with None -> T.Dot (Ft1, cleanSub (s1)) | Some index -> T.Dot (T.Idx index, cleanSub (s1)))
and IsSubRenamingOnly = function (T.Shift (n)) -> true | (T.Dot (Ft1, s1)) -> (match getFrontIndex (Ft1) with None -> false | Some _ -> true) && IsSubRenamingOnly (s1)
and mergeSpines = function ((T.Nil), (T.Nil, t2)) -> T.Nil | ((T.AppExp (E1, S1)), (T.AppExp (E2, S2), t2)) -> if Conv.conv ((E1, I.id), (E2, T.coerceSub (t2))) then T.AppExp (E1, mergeSpines (S1, (S2, t2))) else raise (Error "Spine not equal (AppExp)") | ((T.AppBlock (B1, S1)), (T.AppBlock (B2, S2), t2)) -> if blockEqual (B1, I.blockSub (B2, T.coerceSub t2)) then T.AppBlock (B1, mergeSpines (S1, (S2, t2))) else raise (Error "Spine not equal (AppBlock)") | ((T.AppPrg (P1, S1)), (T.AppPrg (P2, S2), t2)) -> if (prgEqual (P1, (P2, t2))) then T.AppPrg (P1, mergeSpines (S1, (S2, t2))) else raise (Error "Prg (in App) not equal") | (T.SClo (S, t1), (T.SClo (s, t2a), t2)) -> raise (Error "SClo should not exist!") | _ -> raise (Error "Spine are not equivalent")
and mergePrgs = function ((T.Lam (D1, P1)), (T.Lam (D2, P2), t2)) -> if (decEqual (D1, (D2, t2)) && prgEqual (P1, (P2, T.dot1 t2))) then T.Lam (D1, P1) else raise (Error "Lambda don't match") | ((T.New P1), (T.New P2, t2)) -> if (prgEqual (P1, (P2, t2))) then T.New P1 else raise (Error "New don't match") | ((T.Choose P1), (T.Choose P2, t2)) -> if (prgEqual (P1, (P2, t2))) then T.Choose P1 else raise (Error "Choose don't match") | ((T.PairExp (U1, P1)), (T.PairExp (U2, P2), t2)) -> ( let t2' = T.coerceSub t2 in  if (Conv.conv ((U1, I.id), (U2, t2'))) then T.PairExp (U1, mergePrgs ((P1), (P2, t2))) else raise (Error "cannot merge PairExp") ) | ((T.PairBlock (B1, P1)), (T.PairBlock (B2, P2), t2)) -> ( let B2' = I.blockSub (B2, T.coerceSub t2) in  if (blockEqual (B1, B2')) then T.PairBlock (B1, mergePrgs ((P1), (P2, t2))) else raise (Error "cannot merge PairBlock") ) | ((T.PairPrg (P1a, P1b)), (T.PairPrg (P2a, P2b), t2)) -> if (prgEqual (P1a, (P2a, t2))) then T.PairPrg (P1a, (mergePrgs ((P1b), (P2b, t2)))) else raise (Error "cannot merge PairPrg") | ((T.Unit), (T.Unit, t2)) -> T.Unit | (T.Const lemma1, (T.Const lemma2, _)) -> if (lemma1 = lemma2) then T.Const lemma1 else raise (Error "Constants do not match.") | (T.Var x1, (T.Var x2, t2)) -> (match getFrontIndex (T.varSub (x2, t2)) with None -> raise (Error "Variables do not match.") | Some i -> (if (x1 = i) then T.Var x1 else raise (Error "Variables do not match."))) | ((T.Redex (P1, S1)), (T.Redex (P2, S2), t2)) -> ( let newS = mergeSpines (S1, (S2, t2)) in  if (prgEqual (P1, (P2, t2))) then T.Redex (P1, newS) else raise (Error "Redex Prgs don't match") ) | ((T.Rec (D1, P1)), (T.Rec (D2, P2), t2)) -> if (decEqual (D1, (D2, t2)) && prgEqual (P1, (P2, T.dot1 t2))) then T.Rec (D1, P1) else raise (Error "Rec's don't match") | ((T.Case (T.Cases O1)), (T.Case (T.Cases [C]), t2)) -> T.Case (T.Cases (mergeCase (O1, (C, t2)))) | ((T.Case O1), (T.Case O2, t2)) -> raise (Error "Invariant Violated") | ((T.PClo (P1, t1)), (T.PClo (P2, t2a), t2b)) -> raise (Error "PClo should not exist!") | ((T.Let (D1, P1a, P1b)), (T.Let (D2, P2a, P2b), t2)) -> if (decEqual (D1, (D2, t2)) && prgEqual (P1a, (P2a, t2))) then T.Let (D1, P1a, mergePrgs ((P1b), (P2b, T.dot1 t2))) else raise (Error "Let don't match") | ((T.EVar (Psi1, P1optRef, F1, _, _, _)), (T.EVar (Psi2, P2optref, F2, _, _, _), t2)) -> raise (Error "No EVARs should exist!") | _ -> raise (Error "Redundancy in cases could not automatically be removed.")
and invertSub s  = ( let rec lookup = function (n, T.Shift _, p) -> None | (n, T.Dot (T.Undef, s'), p) -> lookup (n + 1, s', p) | (n, T.Dot (Ft, s'), p) -> (match getFrontIndex (Ft) with None -> lookup (n + 1, s', p) | Some k -> if (k = p) then Some n else lookup (n + 1, s', p)) in let rec invertSub'' = function (0, si) -> si | (p, si) -> (match (lookup (1, s, p)) with Some k -> invertSub'' (p - 1, T.Dot (T.Idx k, si)) | None -> invertSub'' (p - 1, T.Dot (T.Undef, si))) in let rec invertSub' = function (n, T.Shift p) -> invertSub'' (p, T.Shift n) | (n, T.Dot (_, s')) -> invertSub' (n + 1, s') in  invertSub' (0, s) )
and printSub = function (T.Shift k) -> print ("Shift " ^ Int.toString (k) ^ "\n") | (T.Dot (T.Idx k, s)) -> (print ("Idx " ^ Int.toString (k) ^ " (DOT) "); printSub (s)) | (T.Dot (T.Prg (T.EVar _), s)) -> (print ("PRG_EVAR (DOT) "); printSub (s)) | (T.Dot (T.Exp (I.EVar _), s)) -> (print ("EXP_EVAR (DOT) "); printSub (s)) | (T.Dot (T.Prg P, s)) -> (print ("PRG (DOT) "); printSub (s)) | (T.Dot (T.Exp E, s)) -> (print ("EXP (DOT) "); printSub (s)) | (T.Dot (T.Block B, s)) -> (print ("BLOCK (DOT) "); printSub (s)) | (T.Dot (T.Undef, s)) -> (print ("UNDEF. (DOT) "); printSub (s))
and mergeCase = function ([], C) -> raise (Error "Case incompatible, cannot merge") | (L, C) -> ( (*
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
(* So now we have
         P1 makes sense in Psi1, t1 goes from Psi1' to Psi1.

         Psi1 |- t1 : Psi1'
         Psi2 |- t3 : Psi1'
         *)
(* Psi1 |- t : Psi2 *)
(* Psi1 |- t' : Psi1' *)
(* If we can get this to match, then Psi1 |- P2[t] *)
let tAfterInv = T.invertSub (tAfter) in let t3 = T.comp (tAfterInv, t2) in let t = Opsem.createVarSub (Psi1, Psi2) in let t' = T.comp (t3, t) in let doMatch = try (Opsem.matchSub (Psi1, t1, t'); true) with NoMatch -> false in  if (doMatch) then ( let newT = T.normalizeSub t in let stillMatch = IsSubRenamingOnly (newT) in  if (stillMatch) then (* Since the case matches, lets continue the merge on P1 and P2
           * Note that removing the redundancy of other case statements
           * is handled recursively ... see convertCases
           *)
(* Note that tAfter and newT are both renaming substitutions *)
(Psi1, t1, mergePrgs (P1, (P2, cleanSub (newT)))) :: O else if (length (O) = 0) then (* We tried all the cases, and we can now add it *)
(Psi2, t3, P2) :: L else (* Try other cases *)
(Psi1, t1, P1) :: mergeCase (O, C) ) else if (length (O) = 0) then (* We tried all the cases, and we can now add it *)
(Psi2, t3, P2) :: L else (* Try other cases *)
(Psi1, t1, P1) :: mergeCase (O, C) )
and mergeIfNecessary (C, C')  = ( (* Note that s1 is a substitution s.t.  Psi1 |- s1: Psi0
        and s2 is a substitution s.t.         Psi2 |- s2: Psi0

        It is possible that this property is lost when the case is executed
        with a different Psi0 which can happen during recursive calls
        (as the context grows).

        In that case:
          Psi, Psi1 |- X1...Xn, id{Psi} : Psi, Psi2

        Therefore, the X's are not dependent on the extra Psi introduced
        by recursive calls, which is why they are ignored in well.

        We will generate a substitution t s.t. Psi1 |- t: Psi2
        Therefore  Psi1 |- (s2 o t) : Psi0

        And we are trying to match it with
                   Psi1 |- s1 : Psi0

      *)
(* Psi1 |- t : Psi2 *)
(* Now since s1 and t' go between the same contexts, we see
      * if we can unify them
      *)
let t = Opsem.createVarSub (Psi1, Psi2) in let t' = T.comp (s2, t) in let doMatch = try (Opsem.matchSub (Psi1, s1, t'); true) with NoMatch -> false in  if (not doMatch) then [C; C'] else ( let newT = T.normalizeSub t in  if (IsSubRenamingOnly (newT)) then try [(Psi1, s1, mergePrgs ((P1), (P2, cleanSub (newT))))](* In this case, C' is redundant and cannot be fixed, so C' will never be called
               * [C,C']
               *)
 with Error s -> (* (print ("***WARNING*** -- redundant case automatically ANNIHILATED:  " ^ s ^ "\n") ; [C]) *)
raise (Error ("***WARNING*** -- redundant case automatically ANNIHILATED:  " ^ s ^ "\n")) else [C; C'] ) )
 end
