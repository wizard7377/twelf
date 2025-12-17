Redundant  Opsem OPSEM     REDUNDANT  struct exception (*
     convert:  Tomega.Prg -> Tomega.Prg
     Attempts to eliminate *redundant* cases.
     *)
module module let rec optionRefEqual(r1,  , r2,  , func) if (r1 = r2) then true else (match (r1,  , r2) with (ref nONE,  , ref nONE) -> true (ref (sOME (p1)),  , ref (sOME (p2))) -> func (p1,  , p2) _ -> false)let rec convert(lam (d,  , p)) lam (d,  , convert p) convert(new p) new (convert p) convert(choose p) choose (convert p) convert(pairExp (m,  , p)) pairExp (m,  , convert p) convert(pairBlock (rho,  , p)) pairBlock (rho,  , convert p) convert(pairPrg (p1,  , p2)) pairPrg (convert p1,  , convert p2) convert(unit) unit convert(var x) var x convert(const x) const x convert(redex (p,  , s)) redex (convert p,  , convertSpine s) convert(rec (d,  , p)) rec (d,  , convert p) convert(case (cases o)) case (cases (convertCases o)) convert(let (d,  , p1,  , p2)) let (d,  , convert p1,  , convert p2)(* No EVARs will occur
      | convert (T.PClo (P,t)) = raise Error "No PClo should exist" (* T.PClo (convert P, t) *)
      | convert (T.EVar (D, P as ref NONE, F)) = T.EVar (D, P, F)
      | convert (T.EVar (D, ref (SOME P), F)) = convert P (* some opsem here *)
    *)
 convertSpine(nil) nil convertSpine(appExp (i,  , s)) (appExp (i,  , convertSpine s)) convertSpine(appBlock (i,  , s)) (appBlock (i,  , convertSpine s)) convertSpine(appPrg (p,  , s)) (appPrg (convert p,  , convertSpine s)) convertSpine(sClo (s,  , t)) raise (error "SClo should not exist")(* (T.SClo (convertSpine S, t)) *)
 expEqual(e1,  , e2) conv ((e1,  , id),  , (e2,  , id)) isubEqual(sub1,  , sub2) convSub (sub1,  , sub2)(* Note that it doesn't handle blocks *)
 blockEqual(bidx x,  , bidx x') (x = x') blockEqual(lVar (r,  , sub1,  , (cid,  , sub2)),  , lVar (r',  , sub1',  , (cid',  , sub2'))) optionRefEqual (r,  , r',  , blockEqual) && isubEqual (sub1,  , sub1') && (cid = cid') && isubEqual (sub1',  , sub2') blockEqual_ false decEqual(uDec (d1),  , (uDec (d2),  , t2)) convDec ((d1,  , id),  , (d2,  , coerceSub (t2))) decEqual(pDec (_,  , f1,  , _,  , _),  , (pDec (_,  , f2,  , _,  , _),  , t2)) convFor ((f1,  , id),  , (f2,  , t2)) decEqual_ false caseEqual(((psi1,  , t1,  , p1) :: o1),  , (((psi2,  , t2,  , p2) :: o2),  , tAfter)) let let  in(* Note:  (Psi1 |- t1: Psi0) *)
let  in(* Psi1 |- t: Psi2 *)
let  in(* Psi1 |- t' : Psi_0 *)
let  in in if (doMatch) then let let  inlet  in in (stillMatch && prgEqual (p1,  , (p2,  , cleanSub (newT)))) else false caseEqual(nil,  , (nil,  , t2)) true caseEqual_ false spineEqual((nil),  , (nil,  , t2)) true spineEqual((appExp (e1,  , s1)),  , (appExp (e2,  , s2),  , t2)) (conv ((e1,  , id),  , (e2,  , coerceSub (t2))) && spineEqual (s1,  , (s2,  , t2))) spineEqual((appBlock (b1,  , s1)),  , (appBlock (b2,  , s2),  , t2)) (blockEqual (b1,  , blockSub (b2,  , coerceSub t2)) && spineEqual (s1,  , (s2,  , t2))) spineEqual((appPrg (p1,  , s1)),  , (appPrg (p2,  , s2),  , t2)) (prgEqual (p1,  , (p2,  , t2)) && spineEqual (s1,  , (s2,  , t2))) spineEqual(sClo (s,  , t1),  , (sClo (s,  , t2a),  , t2)) raise (error "SClo should not exist!") spineEqual_ false prgEqual((lam (d1,  , p1)),  , (lam (d2,  , p2),  , t2)) (decEqual (d1,  , (d2,  , t2)) && prgEqual (p1,  , (p2,  , dot1 t2))) prgEqual((new p1),  , (new p2,  , t2)) prgEqual (p1,  , (p2,  , t2)) prgEqual((choose p1),  , (choose p2,  , t2)) prgEqual (p1,  , (p2,  , t2)) prgEqual((pairExp (u1,  , p1)),  , (pairExp (u2,  , p2),  , t2)) (conv ((u1,  , id),  , (u2,  , (coerceSub t2))) && prgEqual ((p1),  , (p2,  , t2))) prgEqual((pairBlock (b1,  , p1)),  , (pairBlock (b2,  , p2),  , t2)) (blockEqual (b1,  , (blockSub (b2,  , coerceSub t2))) && prgEqual (p1,  , (p2,  , t2))) prgEqual((pairPrg (p1a,  , p1b)),  , (pairPrg (p2a,  , p2b),  , t2)) (prgEqual (p1a,  , (p2a,  , t2)) && prgEqual (p1b,  , (p2b,  , t2))) prgEqual((unit),  , (unit,  , t2)) true prgEqual(const lemma1,  , (const lemma2,  , _)) (lemma1 = lemma2) prgEqual(var x1,  , (var x2,  , t2)) (match getFrontIndex (varSub (x2,  , t2)) with nONE -> false sOME i -> (x1 = i)) prgEqual((redex (p1,  , s1)),  , (redex (p2,  , s2),  , t2)) (prgEqual (p1,  , (p2,  , t2)) && spineEqual (s1,  , (s2,  , t2))) prgEqual((rec (d1,  , p1)),  , (rec (d2,  , p2),  , t2)) (decEqual (d1,  , (d2,  , t2)) && prgEqual (p1,  , (p2,  , dot1 t2))) prgEqual((case (cases o1)),  , (case (cases o2),  , t2)) caseEqual (o1,  , (o2,  , t2)) prgEqual((let (d1,  , p1a,  , p1b)),  , (let (d2,  , p2a,  , p2b),  , t2)) (decEqual (d1,  , (d2,  , t2)) && prgEqual (p1a,  , (p2a,  , t2))) prgEqual((pClo (p1,  , t1)),  , (pClo (p2,  , t2a),  , t2b)) raise (error "PClo should not exist!") prgEqual((eVar (psi1,  , p1optRef,  , f1,  , _,  , _,  , _)),  , (eVar (psi2,  , p2optref,  , f2,  , _,  , _,  , _),  , t2)) raise (error "No EVARs should exist!") prgEqual_ false(* convertCases is where the real work comes in *)
(* will attempt to merge cases together and call convert
     * on what happens in each case
     *)
 convertCases(a :: c) let let  in in ((psi,  , t,  , convert (p)) :: convertCases (c')) convertCasesc c(* will be T.Cases nil *)
(* Returns a list with C (merged with redundant cases) as the head followed by the rest *)
 removeRedundancy(c,  , []) (c,  , []) removeRedundancy(c,  , c' :: rest) let let  inlet  in in (c''',  , cs @ rest')(* returns NONE if not found *)
 getFrontIndex(idx k) sOME (k) getFrontIndex(prg p) getPrgIndex (p) getFrontIndex(exp u) getExpIndex (u) getFrontIndex(block b) getBlockIndex (b) getFrontIndex(undef) nONE(* getPrgIndex returns NONE if it is not an index *)
 getPrgIndex(var k) sOME (k) getPrgIndex(redex (p,  , nil)) getPrgIndex (p) getPrgIndex(pClo (p,  , t)) (match getPrgIndex (p) with nONE -> nONE sOME i -> getFrontIndex (varSub (i,  , t))) getPrgIndex_ nONE(* getExpIndex returns NONE if it is not an index *)
 getExpIndex(root (bVar k,  , nil)) sOME (k) getExpIndex(redex (u,  , nil)) getExpIndex (u) getExpIndex(eClo (u,  , t)) (match getExpIndex (u) with nONE -> nONE sOME i -> getFrontIndex (revCoerceFront (bvarSub (i,  , t)))) getExpIndex(u as lam (dec (_,  , u1),  , u2)) (try  with ) getExpIndex_ nONE(* getBlockIndex returns NONE if it is not an index *)
 getBlockIndex(bidx k) sOME (k) getBlockIndex_ nONE(* clean up the renaming substitution,
       this is to allow T.invertSub to appropriately
       think it is a pattern substitution
       *)
 cleanSub(s as shift _) s cleanSub(dot (ft1,  , s1)) (match getFrontIndex (ft1) with nONE -> dot (ft1,  , cleanSub (s1)) sOME index -> dot (idx index,  , cleanSub (s1)))(* determine if t is simply a renaming substitution *)
 isSubRenamingOnly(shift (n)) true isSubRenamingOnly(dot (ft1,  , s1)) (match getFrontIndex (ft1) with nONE -> false sOME _ -> true) && isSubRenamingOnly (s1)(* Note that what we are merging it with will need to go under an extra renaming substitution *)
 mergeSpines((nil),  , (nil,  , t2)) nil mergeSpines((appExp (e1,  , s1)),  , (appExp (e2,  , s2),  , t2)) if conv ((e1,  , id),  , (e2,  , coerceSub (t2))) then appExp (e1,  , mergeSpines (s1,  , (s2,  , t2))) else raise (error "Spine not equal (AppExp)") mergeSpines((appBlock (b1,  , s1)),  , (appBlock (b2,  , s2),  , t2)) if blockEqual (b1,  , blockSub (b2,  , coerceSub t2)) then appBlock (b1,  , mergeSpines (s1,  , (s2,  , t2))) else raise (error "Spine not equal (AppBlock)") mergeSpines((appPrg (p1,  , s1)),  , (appPrg (p2,  , s2),  , t2)) if (prgEqual (p1,  , (p2,  , t2))) then appPrg (p1,  , mergeSpines (s1,  , (s2,  , t2))) else raise (error "Prg (in App) not equal") mergeSpines(sClo (s,  , t1),  , (sClo (s,  , t2a),  , t2)) raise (error "SClo should not exist!") mergeSpines_ raise (error "Spine are not equivalent") mergePrgs((lam (d1,  , p1)),  , (lam (d2,  , p2),  , t2)) if (decEqual (d1,  , (d2,  , t2)) && prgEqual (p1,  , (p2,  , dot1 t2))) then lam (d1,  , p1) else raise (error "Lambda don't match") mergePrgs((new p1),  , (new p2,  , t2)) if (prgEqual (p1,  , (p2,  , t2))) then new p1 else raise (error "New don't match") mergePrgs((choose p1),  , (choose p2,  , t2)) if (prgEqual (p1,  , (p2,  , t2))) then choose p1 else raise (error "Choose don't match") mergePrgs((pairExp (u1,  , p1)),  , (pairExp (u2,  , p2),  , t2)) let let  in in if (conv ((u1,  , id),  , (u2,  , t2'))) then pairExp (u1,  , mergePrgs ((p1),  , (p2,  , t2))) else raise (error "cannot merge PairExp") mergePrgs((pairBlock (b1,  , p1)),  , (pairBlock (b2,  , p2),  , t2)) let let  in in if (blockEqual (b1,  , b2')) then pairBlock (b1,  , mergePrgs ((p1),  , (p2,  , t2))) else raise (error "cannot merge PairBlock") mergePrgs((pairPrg (p1a,  , p1b)),  , (pairPrg (p2a,  , p2b),  , t2)) if (prgEqual (p1a,  , (p2a,  , t2))) then pairPrg (p1a,  , (mergePrgs ((p1b),  , (p2b,  , t2)))) else raise (error "cannot merge PairPrg") mergePrgs((unit),  , (unit,  , t2)) unit mergePrgs(const lemma1,  , (const lemma2,  , _)) if (lemma1 = lemma2) then const lemma1 else raise (error "Constants do not match.") mergePrgs(var x1,  , (var x2,  , t2)) (match getFrontIndex (varSub (x2,  , t2)) with nONE -> raise (error "Variables do not match.") sOME i -> (if (x1 = i) then var x1 else raise (error "Variables do not match."))) mergePrgs((redex (p1,  , s1)),  , (redex (p2,  , s2),  , t2)) let let  in in if (prgEqual (p1,  , (p2,  , t2))) then redex (p1,  , newS) else raise (error "Redex Prgs don't match") mergePrgs((rec (d1,  , p1)),  , (rec (d2,  , p2),  , t2)) if (decEqual (d1,  , (d2,  , t2)) && prgEqual (p1,  , (p2,  , dot1 t2))) then rec (d1,  , p1) else raise (error "Rec's don't match") mergePrgs((case (cases o1)),  , (case (cases [c]),  , t2)) case (cases (mergeCase (o1,  , (c,  , t2)))) mergePrgs((case o1),  , (case o2,  , t2)) raise (error "Invariant Violated") mergePrgs((pClo (p1,  , t1)),  , (pClo (p2,  , t2a),  , t2b)) raise (error "PClo should not exist!") mergePrgs((let (d1,  , p1a,  , p1b)),  , (let (d2,  , p2a,  , p2b),  , t2)) if (decEqual (d1,  , (d2,  , t2)) && prgEqual (p1a,  , (p2a,  , t2))) then let (d1,  , p1a,  , mergePrgs ((p1b),  , (p2b,  , dot1 t2))) else raise (error "Let don't match") mergePrgs((eVar (psi1,  , p1optRef,  , f1,  , _,  , _,  , _)),  , (eVar (psi2,  , p2optref,  , f2,  , _,  , _,  , _),  , t2)) raise (error "No EVARs should exist!") mergePrgs_ raise (error "Redundancy in cases could not automatically be removed.")(*
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
 invertSubs let let rec lookup(n,  , shift _,  , p) nONE lookup(n,  , dot (undef,  , s'),  , p) lookup (n + 1,  , s',  , p) lookup(n,  , dot (ft,  , s'),  , p) (match getFrontIndex (ft) with nONE -> lookup (n + 1,  , s',  , p) sOME k -> if (k = p) then sOME n else lookup (n + 1,  , s',  , p))let rec invertSub''(0,  , si) si invertSub''(p,  , si) (match (lookup (1,  , s,  , p)) with sOME k -> invertSub'' (p - 1,  , dot (idx k,  , si)) nONE -> invertSub'' (p - 1,  , dot (undef,  , si)))let rec invertSub'(n,  , shift p) invertSub'' (p,  , shift n) invertSub'(n,  , dot (_,  , s')) invertSub' (n + 1,  , s') in invertSub' (0,  , s)(* debug *)
 printSub(shift k) print ("Shift " ^ toString (k) ^ "\n") printSub(dot (idx k,  , s)) (print ("Idx " ^ toString (k) ^ " (DOT) "); printSub (s)) printSub(dot (prg (eVar _),  , s)) (print ("PRG_EVAR (DOT) "); printSub (s)) printSub(dot (exp (eVar _),  , s)) (print ("EXP_EVAR (DOT) "); printSub (s)) printSub(dot (prg p,  , s)) (print ("PRG (DOT) "); printSub (s)) printSub(dot (exp e,  , s)) (print ("EXP (DOT) "); printSub (s)) printSub(dot (block b,  , s)) (print ("BLOCK (DOT) "); printSub (s)) printSub(dot (undef,  , s)) (print ("UNDEF. (DOT) "); printSub (s))(* We need to return it in terms of the context of the first *)
 mergeCase([],  , c) raise (error "Case incompatible, cannot merge") mergeCase(l as (psi1,  , t1,  , p1) :: o,  , c as ((psi2,  , t2,  , p2),  , tAfter)) let (*
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
let  inlet  in(* So now we have
         P1 makes sense in Psi1, t1 goes from Psi1' to Psi1.

         Psi1 |- t1 : Psi1'
         Psi2 |- t3 : Psi1'
         *)
let  in(* Psi1 |- t : Psi2 *)
let  in(* Psi1 |- t' : Psi1' *)
(* If we can get this to match, then Psi1 |- P2[t] *)
let  in in if (doMatch) then let let  inlet  in in if (stillMatch) then (* Since the case matches, lets continue the merge on P1 and P2
           * Note that removing the redundancy of other case statements
           * is handled recursively ... see convertCases
           *)
(* Note that tAfter and newT are both renaming substitutions *)
(psi1,  , t1,  , mergePrgs (p1,  , (p2,  , cleanSub (newT)))) :: o else if (length (o) = 0) then (* We tried all the cases, and we can now add it *)
(psi2,  , t3,  , p2) :: l else (* Try other cases *)
(psi1,  , t1,  , p1) :: mergeCase (o,  , c) else if (length (o) = 0) then (* We tried all the cases, and we can now add it *)
(psi2,  , t3,  , p2) :: l else (* Try other cases *)
(psi1,  , t1,  , p1) :: mergeCase (o,  , c)(* mergeIfNecessary
   * Simply see if C is the same case as C'
   * If so, try to merge them together and return a list of just the case merged together,
   * otherwise, return a list of both elements.
   *)
 mergeIfNecessary(c as (psi1,  , s1,  , p1),  , c' as (psi2,  , s2,  , p2)) let (* Note that s1 is a substitution s.t.  Psi1 |- s1: Psi0
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
let  in(* Psi1 |- t : Psi2 *)
let  in(* Now since s1 and t' go between the same contexts, we see
      * if we can unify them
      *)
let  in in if (not doMatch) then [c; c'] else let let  in in if (isSubRenamingOnly (newT)) then try  with  else [c; c']end