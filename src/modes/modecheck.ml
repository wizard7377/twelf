ModeCheck  ModeTable MODETABLE    Whnf WHNF    Index INDEX    Origins ORIGINS     MODECHECK  struct (*! structure IntSyn = IntSyn !*)
(*! structure ModeSyn = ModeSyn !*)
(*! structure Paths = Paths !*)
exception module module module type Uniqueness(*     | Ambig            *)
type Info(*     | Ground               *)
type Status(*     | Universal             *)
(* hack: if true, check freeness of output arguments in subgoals *)
let  in(* Representation invariant:

       Groundness information:
       T stands for ground, B stands for unknown
       Ex  for a named existential variable
       Par for a parameter

       Mode context   D ::= . | D, S

       If D contains Status information for variables in
       a context G, we write G ~ D
       We write D' >= D if for all i
         D(i) par iff D'(i) par
         D(i) bot implies D'(i) bot or D'(i) top
         D(i) top implies D'(i) top
    *)
(* copied from worldcheck/worldsyn.fun *)
let rec wrapMsg(c,  , occ,  , msg) (match originLookup c with (fileName,  , nONE) -> (fileName ^ ":" ^ msg) (fileName,  , sOME occDec) -> (wrapLoc' (loc (fileName,  , occToRegionClause occDec occ),  , linesInfoLookup (fileName),  , "Constant " ^ qidToString (constQid c) ^ "\n" ^ msg)))let rec wrapMsg'(fileName,  , r,  , msg) wrapLoc (loc (fileName,  , r),  , msg)exception exception (* lookup (a, occ) = mSs

       Invariant: mS are the argument modes for a
       Raises an error if no mode for a has declared.
       (occ is used in error message)
    *)
let rec lookup(a,  , occ) match mmodeLookup a with nil -> raise (error' (occ,  , "No mode declaration for " ^ conDecName (sgnLookup a))) sMs -> sMs(* nameOf S, selects a name for S *)
let rec nameOf(existential (_,  , nONE)) "?" nameOf(existential (_,  , sOME name)) name nameOf_ "?"(* unique (k, ks) = B

       Invariant:
       B iff k does not occur in ks
    *)
let rec unique(k,  , nil) true unique(k,  , k' :: ks) (k <> k') && unique (k,  , ks)(* isUniversal S = B

       Invariant:
       B iff S = Par
    *)
let rec isUniversaluniversal true isUniversal_ false(* isGround S = B

       Invariant:
       B iff S = Ex (T x)
    *)
let rec isGround(existential (ground _,  , _)) true isGround_ false(* uniqueness S = u
       where u is the uniqueness property of status S
    *)
let rec uniqueness(existential (ground (u),  , _)) u uniqueness(universal) unique(* ambiguate (mode) = mode'
       where mode' forgets uniqueness properties
    *)
let rec ambiguate(plus) plus ambiguate(minus) minus ambiguate(minus1) minus(* andUnique (u1, u2) = Unique if u1 = u2 = Unique
       = Ambig otherwise
    *)
let rec andUnique(unique,  , unique) unique andUnique_ ambig(* isFree S = b

       Invariant:
       b iff S = Ex (B x)
    *)
let rec isFree(existential (free,  , _)) true isFree_ falseexception (* etaContract (U, n) = k

       if lam V1... lam Vn. U =eta*=> k
       otherwise raise exception Eta

       Invariant: G, V1,..., Vn |- U : V for some G, Vi, V.
                  U in NF
    *)
let rec etaContract(root (bVar (k),  , s),  , n) if k > n then (etaSpine (s,  , n); k - n) else raise (eta) etaContract(lam (d,  , u),  , n) etaContract (u,  , n + 1) etaContract_ raise (eta)(* etaSpine (S, n) = ()
       if S =eta*=> n ; n-1 ; ... ; 1 ; Nil
       otherwise raise exception Eta

       Invariant: G |- S : V1 >> V2 for some G, V1, V2
                  S in NF
    *)
 etaSpine(nil,  , 0) () etaSpine(app (u,  , s),  , n) if etaContract (u,  , 0) = n then etaSpine (s,  , n - 1) else raise (eta)(* S[s] should be impossible *)
(* isPattern (D, k, mS) = B

       Invariant:
       B iff k > k' for all k' in mS
         and for all k in mS: k is parameter
         and for all k', k'' in mS: k' <> k''
    *)
let rec checkPattern(d,  , k,  , args,  , nil) () checkPattern(d,  , k,  , args,  , app (u,  , s)) (let let  in in if (k > k') && isUniversal (ctxLookup (d,  , k')) && unique (k',  , args) then checkPattern (d,  , k,  , k' :: args,  , s) else raise (eta))let rec isPattern(d,  , k,  , s) try  with (* ------------------------------------------- strictness check *)
(* This repeats some code from ../typecheck/strict.fun *)
(* Interface here is somewhat different *)
(* strictExpN (D, p, U) = B

       Invariant:
       If  D |- U : V
       and U is in nf (normal form)
       then B iff U is strict in p
    *)
let rec strictExpN(d,  , _,  , uni _) false strictExpN(d,  , p,  , lam (_,  , u)) strictExpN (decl (d,  , universal),  , p + 1,  , u) strictExpN(d,  , p,  , pi ((d',  , _),  , u)) strictDecN (d,  , p,  , d') || strictExpN (decl (d,  , universal),  , p + 1,  , u) strictExpN(d,  , p,  , root (h,  , s)) (match h with (bVar (k')) -> if (k' = p) then isPattern (d,  , k',  , s) else if isUniversal (ctxLookup (d,  , k')) then strictSpineN (d,  , p,  , s) else false(* equivalently: isUniversal .. andalso strictSpineN .. *)
 (const (c)) -> strictSpineN (d,  , p,  , s) (def (d)) -> strictSpineN (d,  , p,  , s) (fgnConst (cs,  , conDec)) -> strictSpineN (d,  , p,  , s)) strictExpN(d,  , p,  , fgnExp (cs,  , ops)) false(* this is a hack - until we investigate this further   -rv *)
(* no other cases possible *)
(* strictSpineN (D, S) = B

       Invariant:
       If  D |- S : V > W
       and S is in nf (normal form)
       then B iff S is strict in k
    *)
 strictSpineN(_,  , _,  , nil) false strictSpineN(d,  , p,  , app (u,  , s)) strictExpN (d,  , p,  , u) || strictSpineN (d,  , p,  , s) strictDecN(d,  , p,  , dec (_,  , v)) strictExpN (d,  , p,  , v)(*
    fun strictAtom (D, p, mode, I.Nil, (V, s), M.Mnil) = false
      | strictAtom (D, p, M.Minus, I.App (U, S), (I.Pi ((I.Dec (_, V1), _), V2), s),
                     M.Mapp (M.Marg (M.Minus, _), mS)) =
          strictExpN (D, p, Whnf.normalize (V1, s))
          orelse strictAtom (D, p, M.Minus, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)), mS)
      | strictAtom (D, p, mode, I.App (U, S), (I.Pi (_, V2), s), M.Mapp(_, mS)) =
          strictAtom (D, p, mode, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)), mS)
    *)
(* ------------------------------------------- freeness check *)
(* freeExpN (D, mode, U, occ = ()

       If G |- U : V  (U in nf)
       and G ~ D
       then freeExpN terminates with () if D |- U free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
let rec freeExpN(d,  , d,  , mode,  , root (bVar k,  , s),  , occ,  , strictFun) (freeVar (d,  , d,  , mode,  , k,  , head occ,  , strictFun); freeSpineN (d,  , d,  , mode,  , s,  , (1,  , occ),  , strictFun)) freeExpN(d,  , d,  , mode,  , root (const _,  , s),  , occ,  , strictFun) freeSpineN (d,  , d,  , mode,  , s,  , (1,  , occ),  , strictFun) freeExpN(d,  , d,  , mode,  , root (def _,  , s),  , occ,  , strictFun) freeSpineN (d,  , d,  , mode,  , s,  , (1,  , occ),  , strictFun) freeExpN(d,  , d,  , mode,  , root (fgnConst (cs,  , conDec),  , s),  , occ,  , strictFun) freeSpineN (d,  , d,  , mode,  , s,  , (1,  , occ),  , strictFun) freeExpN(d,  , d,  , mode,  , lam (_,  , u),  , occ,  , strictFun) freeExpN (decl (d,  , universal),  , d + 1,  , mode,  , u,  , body occ,  , strictFun) freeExpN(d,  , d,  , mode,  , fgnExp csfe,  , occ,  , strictFun) apply csfe (fun u -> freeExpN (d,  , d,  , mode,  , normalize (u,  , id),  , occ,  , strictFun))(* punting on the occ here  - ak *)
(* freeSpineN (D, mode, S, occ, strictFun)  = ()

       If   G |- S : V1  > V2   (S in nf)
       and  G ~ D
       then freeSpineN terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
 freeSpineN(d,  , d,  , mode,  , nil,  , _,  , strictFun) () freeSpineN(d,  , d,  , mode,  , app (u,  , s),  , (p,  , occ),  , strictFun) (freeExpN (d,  , d,  , mode,  , u,  , arg (p,  , occ),  , strictFun); freeSpineN (d,  , d,  , mode,  , s,  , (p + 1,  , occ),  , strictFun))(* freeVar (D, mode, k, occ, strictFun)  = ()

       If   G |- k : V1
       and  G ~ D
       then freeVar terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
 freeVar(d,  , d,  , mode,  , k,  , occ,  , strictFun) let let  in in if isFree status || isUniversal status || strictFun (k - d) then () else raise (modeError (occ,  , "Occurrence of variable " ^ (nameOf status) ^ " in " ^ (modeToString mode) ^ " argument not free"))(* -------------------------------- non-strict mode context update *)
(* nonStrictExpN (D, U) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Unknown for all existential variables k
            in U that are free in D
    *)
let rec nonStrictExpN(d,  , root (bVar (k),  , s)) nonStrictSpineN (nonStrictVarD (d,  , k),  , s) nonStrictExpN(d,  , root (const c,  , s)) nonStrictSpineN (d,  , s) nonStrictExpN(d,  , root (def d,  , s)) nonStrictSpineN (d,  , s) nonStrictExpN(d,  , root (fgnConst (cs,  , conDec),  , s)) nonStrictSpineN (d,  , s) nonStrictExpN(d,  , lam (_,  , u)) ctxPop (nonStrictExpN (decl (d,  , universal),  , u)) nonStrictExpN(d,  , fgnExp _) raise (error ("Foreign expressions not permitted when checking freeness"))(* nonStrictSpineN (D, S) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Unkown for all existential variables k
            in S that are Free in D
    *)
 nonStrictSpineN(d,  , nil) d nonStrictSpineN(d,  , app (u,  , s)) nonStrictSpineN (nonStrictExpN (d,  , u),  , s)(* nonStrictVarD (D, k) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is nonStrictd as described in  nonStrictExpN
    *)
 nonStrictVarD(decl (d,  , existential (free,  , name)),  , 1) decl (d,  , existential (unknown,  , name)) nonStrictVarD(d,  , 1) d nonStrictVarD(decl (d,  , status),  , k) decl (nonStrictVarD (d,  , k - 1),  , status)(* ------------------------------------------- mode context update *)
(* updateExpN (D, U, u) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Ground for all existential variables k
            with a strict occurrence in U
            and D'(k) Unkown for all existential variable k
            with a non-strict occurrence, but no strict occurrence in U
            (if !checkFree is true)

       u is the uniqueness property for the new ground assumptions
    *)
let rec updateExpN(d,  , root (bVar (k),  , s),  , u) if isUniversal (ctxLookup (d,  , k)) then updateSpineN (d,  , s,  , u) else if isPattern (d,  , k,  , s) then updateVarD (d,  , k,  , u) else if ! checkFree then nonStrictSpineN (nonStrictVarD (d,  , k),  , s) else d updateExpN(d,  , root (const c,  , s),  , u) updateSpineN (d,  , s,  , u) updateExpN(d,  , root (def d,  , s),  , u) updateSpineN (d,  , s,  , u) updateExpN(d,  , root (fgnConst (cs,  , conDec),  , s),  , u) updateSpineN (d,  , s,  , u) updateExpN(d,  , lam (_,  , u),  , u) ctxPop (updateExpN (decl (d,  , universal),  , u,  , u)) updateExpN(d,  , fgnExp _,  , u) d(* updateSpineN (D, S, u) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Ground for all existential variables k
            with a strict occurrence in S
    *)
 updateSpineN(d,  , nil,  , u) d updateSpineN(d,  , app (u,  , s),  , u) updateSpineN (updateExpN (d,  , u,  , u),  , s,  , u)(* updateVarD (D, k, u) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is updated as described in  updateExpN
    *)
 updateVarD(decl (d,  , existential (_,  , name)),  , 1,  , u) decl (d,  , existential (ground (u),  , name)) updateVarD(decl (d,  , status),  , k,  , u) decl (updateVarD (d,  , k - 1,  , u),  , status)(* ----------------------- mode context update by argument modes *)
(* updateAtom (D, m, S, mS, (p,occ)) = D'

       If   G |- S : V > V'   ( S = U1 ; .. ; Un)
       and  D ~ G
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode
       then D' >= D where
            all Ui are updated if mi = m (mod uniqueness)

       The new ground variables are marked Unique
         if m = (-1) and mi = (-1) (when updating from subgoals with unique inputs)
         or m = mi = (+) (when updating from the clause head)
       Otherwise they are marked Ambig.

       (p,occ) is used in error message if freeness is to be checked
    *)
let rec updateAtom'(d,  , mode,  , nil,  , mnil,  , _) d updateAtom'(d,  , plus,  , app (u,  , s),  , mapp (marg (plus,  , _),  , mS),  , (p,  , occ)) updateAtom' (updateExpN (d,  , u,  , unique),  , plus,  , s,  , mS,  , (p + 1,  , occ)) updateAtom'(d,  , minus,  , app (u,  , s),  , mapp (marg (minus,  , _),  , mS),  , (p,  , occ)) updateAtom' (updateExpN (d,  , u,  , ambig),  , minus,  , s,  , mS,  , (p + 1,  , occ)) updateAtom'(d,  , minus,  , app (u,  , s),  , mapp (marg (minus1,  , _),  , mS),  , (p,  , occ)) updateAtom' (updateExpN (d,  , u,  , ambig),  , minus,  , s,  , mS,  , (p + 1,  , occ)) updateAtom'(d,  , minus1,  , app (u,  , s),  , mapp (marg (minus,  , _),  , mS),  , (p,  , occ)) updateAtom' (updateExpN (d,  , u,  , ambig),  , minus1,  , s,  , mS,  , (p + 1,  , occ)) updateAtom'(d,  , minus1,  , app (u,  , s),  , mapp (marg (minus1,  , _),  , mS),  , (p,  , occ)) updateAtom' (updateExpN (d,  , u,  , unique),  , minus1,  , s,  , mS,  , (p + 1,  , occ)) updateAtom'(d,  , mode,  , app (u,  , s),  , mapp (_,  , mS),  , (p,  , occ)) updateAtom' (d,  , mode,  , s,  , mS,  , (p + 1,  , occ))(* freeAtom (D, m, S, (V,s), mS, (p, occ)) = ()

       checks if all output arguments in S according to mS are free.
       Invariant: G |- S : V[s] >> P for some G and P  (S in nf)
                  G ~ D
                  mode = (-) or (+); ( * ) or (-1) are excluded
    *)
let rec freeAtom(d,  , mode,  , nil,  , vs,  , mnil,  , _) () freeAtom(d,  , minus,  , app (u,  , s),  , (pi ((dec (_,  , v1),  , _),  , v2),  , s),  , mapp (marg (minus,  , _),  , mS),  , (p,  , occ)) (freeExpN (d,  , 0,  , minus,  , u,  , arg (p,  , occ),  , (fun q -> strictExpN (d,  , q,  , normalize (v1,  , s)))); freeAtom (d,  , minus,  , s,  , whnfExpandDef (v2,  , dot (exp u,  , s)),  , mS,  , (p + 1,  , occ))) freeAtom(d,  , mode,  , app (u,  , s),  , (pi (_,  , v2),  , s),  , mapp (_,  , mS),  , (p,  , occ)) freeAtom (d,  , mode,  , s,  , whnfExpandDef (v2,  , dot (exp u,  , s)),  , mS,  , (p + 1,  , occ))(* updateAtom (D, m, S, a, mS, (p, occ))
       see updateAtom', and performs additional freeness check if required
    *)
let rec updateAtom(d,  , mode,  , s,  , a,  , mS,  , (p,  , occ)) let let  in in updateAtom' (d,  , mode,  , s,  , mS,  , (p,  , occ))(* ------------------------------------------- groundness check *)
(* groundExpN (D, mode, U, occ)  = u

       If   G |- U : V    (U in nf)
       and  G ~ D
       then if mode = (+) or (-)
            then groundExpN terminates with u if  D |- U ground
                 else exception ModeError is raised
            if mode = (-1) then D |- U ground and U unique
                           else exception ModeError is raised

       u = Unique if all known variables in U are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *)
let rec groundExpN(d,  , mode,  , root (bVar k,  , s),  , occ) andUnique (groundVar (d,  , mode,  , k,  , head occ),  , groundSpineN (d,  , mode,  , s,  , (1,  , occ))) groundExpN(d,  , mode,  , root (const c,  , s),  , occ) groundSpineN (d,  , mode,  , s,  , (1,  , occ)) groundExpN(d,  , mode,  , root (def d,  , s),  , occ) groundSpineN (d,  , mode,  , s,  , (1,  , occ)) groundExpN(d,  , mode,  , root (fgnConst (cs,  , conDec),  , s),  , occ) groundSpineN (d,  , mode,  , s,  , (1,  , occ)) groundExpN(d,  , mode,  , lam (_,  , u),  , occ) groundExpN (decl (d,  , universal),  , mode,  , u,  , body occ) groundExpN(d,  , mode,  , fgnExp csfe,  , occ) fold csfe (fun (u,  , u) -> andUnique (groundExpN (d,  , mode,  , normalize (u,  , id),  , occ),  , u)) unique(* punting on occ here  - ak *)
(* groundSpineN (D, mode, S, occ)  = u

       If   G |- S : V1  > V2   (S in nf)
       and  G ~ D
       then if mode = (+) or (-)
            then groundSpineN terminates with u if  D |- S ground
                 else exception ModeError is raised
            if mode = (-1) then D |- S ground and S unique
                           else exception ModeError is raised

       u = Unique if all known variables in S are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *)
 groundSpineN(d,  , mode,  , nil,  , _) unique groundSpineN(d,  , mode,  , app (u,  , s),  , (p,  , occ)) andUnique (groundExpN (d,  , mode,  , u,  , arg (p,  , occ)),  , groundSpineN (d,  , mode,  , s,  , (p + 1,  , occ)))(* groundVar (D, mode, k, occ)  = u

       If   G |- k : V1
       and  G ~ D
       then if mode = (+) or (-)
            then groundVar terminates with u if  D |- k ground
                 else exception ModeError is raised
            if mode = (-1) then D |- k ground and k unique
                           else exception ModeError is raised

       u = Unique if k is known to be unique, Ambig otherwise

       (occ and mode are used in error messages)
    *)
 groundVar(d,  , minus1,  , k,  , occ) (match ctxLookup (d,  , k) with existential (ground (unique),  , _) -> unique universal -> unique s as existential (ground (ambig),  , x) -> raise (modeError (occ,  , "Occurrence of variable " ^ nameOf s ^ " in " ^ modeToString minus1 ^ " argument not necessarily unique")) s -> (* Existential (Free, _) or Existential (Unknown, _) *)
raise (modeError (occ,  , "Occurrence of variable " ^ (nameOf s) ^ " in " ^ (modeToString minus1) ^ " argument not necessarily ground"))) groundVar(d,  , mode,  , k,  , occ) let let  in in if isGround status || isUniversal status then uniqueness status else raise (modeError (occ,  , "Occurrence of variable " ^ (nameOf status) ^ " in " ^ (modeToString mode) ^ " argument not necessarily ground"))(* ------------------------------------------- groundness check by polarity *)
(* groundAtom (D, m, S, mS, (p,occ))  = u

       If   G |- S : V > V'   ( S = U1 ; .. ; Un)
       and  D ~ G
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode = (+) or (-1)
       then groundAtom returns u if  D |- Ui ground
            for all i s.t. mi = m (mod uniqueness)
            and checks that D |- Ui unique if mi = (-1) and m = (-)
       otherwise exception ModeError is raised

       u = Unique if all mi = m (mod uniqueness) are unique,
       u = Ambig otherwise

       ((p,occ) used in error messages)
    *)
let rec groundAtom(d,  , _,  , nil,  , mnil,  , _) unique groundAtom(d,  , plus,  , app (u,  , s),  , mapp (marg (plus,  , _),  , mS),  , (p,  , occ)) andUnique (groundExpN (d,  , plus,  , u,  , arg (p,  , occ)),  , groundAtom (d,  , plus,  , s,  , mS,  , (p + 1,  , occ))) groundAtom(d,  , minus,  , app (u,  , s),  , mapp (marg (minus,  , _),  , mS),  , (p,  , occ)) (groundExpN (d,  , minus,  , u,  , arg (p,  , occ)); (* ignore uniqueness result here *)
groundAtom (d,  , minus,  , s,  , mS,  , (p + 1,  , occ))) groundAtom(d,  , minus,  , app (u,  , s),  , mapp (marg (minus1,  , _),  , mS),  , (p,  , occ)) (groundExpN (d,  , minus1,  , u,  , arg (p,  , occ)); (* ignore uniqueness result here *)
groundAtom (d,  , minus,  , s,  , mS,  , (p + 1,  , occ))) groundAtom(d,  , mode,  , app (u,  , s),  , mapp (_,  , mS),  , (p,  , occ)) groundAtom (d,  , mode,  , s,  , mS,  , (p + 1,  , occ))(* ------------------------------------------- mode checking first phase *)
(* ctxPush (Ds, m) = Ds'
       raises the contexts Ds prepending m
    *)
let rec ctxPush(m,  , ds) map (fun d -> decl (d,  , m)) ds(* ctxPop Ds = Ds'
       lowers the contexts Ds
    *)
let rec ctxPopds map (fun decl (d,  , m) -> d) ds(* checkD1 (D, V, occ, k) = ()

       Invariant:
         if G |- V : L
         and  V does not contain Skolem constants
         and  D ~ G
         then
            for each  mode mS of the head of V
              exists  some Di s.t. all (-) evars of mS are ground
                where  D' ~ G, D' >= D is obtained by updating D
                  and  k D' = [D1, ..., Di, ..., Dn]
                  and  Di ~ G, Di >= D' is obtained by mode checking on the subgoals of V

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
    *)
let rec checkD1(d,  , pi ((dec (name,  , _),  , maybe),  , v),  , occ,  , k) checkD1 (decl (d,  , existential (free,  , name)),  , v,  , body occ,  , fun (decl (d',  , m)) -> ctxPush (m,  , k d')) checkD1(d,  , pi ((dec (name,  , v1),  , no),  , v2),  , occ,  , k) checkD1 (decl (d,  , existential (free,  , name)),  , v2,  , body occ,  , fun (decl (d',  , m)) -> ctxPush (m,  , checkG1 (d',  , v1,  , label occ,  , k))) checkD1(d,  , root (const a,  , s),  , occ,  , k) let (* for a declaration, all modes must be satisfied *)
let rec checkAllnil () checkAll(mS :: mSs) let let rec checkSome[d'] (groundAtom (d',  , minus,  , s,  , mS,  , (1,  , occ)); (* ignore return *)
checkAll mSs) checkSome(d' :: ds) ((try  with ); checkAll mSs) in checkSome (k (updateAtom (d,  , plus,  , s,  , a,  , mS,  , (1,  , occ)))) in checkAll (lookup (a,  , occ)) checkD1(d,  , root (def d,  , s),  , occ,  , k) let (* for a declaration, all modes must be satisfied *)
let rec checkAllnil () checkAll(mS :: mSs) let let rec checkSome[d'] (groundAtom (d',  , minus,  , s,  , mS,  , (1,  , occ)); (* ignore return *)
checkAll mSs) checkSome(d' :: ds) ((try  with ); checkAll mSs) in checkSome (k (updateAtom (d,  , plus,  , s,  , d,  , mS,  , (1,  , occ)))) in checkAll (lookup (d,  , occ))(* checkG1 (D, V, occ, k) = Ds

       Invariant:
         if G |- V : L
         and  V does not contain Skolem constants
         and  D ~ G
         then forall D' >= D that mode checks V, (k D') is a sublist of Ds
         and for each Di in Ds, Di ~ G and Di >= D'

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
     *)
 checkG1(d,  , pi ((_,  , maybe),  , v),  , occ,  , k) ctxPop (checkG1 (decl (d,  , universal),  , v,  , body occ,  , fun (decl (d',  , m)) -> ctxPush (m,  , k d'))) checkG1(d,  , pi ((dec (_,  , v1),  , no),  , v2),  , occ,  , k) ctxPop (checkD1 (d,  , v1,  , label occ,  , fun d' -> [d']); checkG1 (decl (d,  , universal),  , v2,  , body occ,  , fun (decl (d',  , m)) -> ctxPush (m,  , k d'))) checkG1(d,  , root (const a,  , s),  , occ,  , k) let (* for a goal, at least one mode must be satisfied *)
let rec checkListfoundnil nil checkListfalse[mS] (match groundAtom (d,  , plus,  , s,  , mS,  , (1,  , occ)) with unique -> k (updateAtom (d,  , minus1,  , s,  , a,  , mS,  , (1,  , occ))) ambig -> k (updateAtom (d,  , minus,  , s,  , a,  , mS,  , (1,  , occ)))) checkListfound(mS :: mSs) let (* found' is true iff D satisfies mS *)
let  in(* compute all other mode contexts *)
let  in in if found' then k (updateAtom (d,  , minus,  , s,  , a,  , mS,  , (1,  , occ))) @ ds' else ds' in checkList false (lookup (a,  , occ)) checkG1(d,  , root (def d,  , s),  , occ,  , k) let (* for a goal, at least one mode must be satisfied *)
let rec checkListfoundnil nil checkListfalse[mS] (match groundAtom (d,  , plus,  , s,  , mS,  , (1,  , occ)) with unique -> k (updateAtom (d,  , minus1,  , s,  , d,  , mS,  , (1,  , occ))) ambig -> k (updateAtom (d,  , minus,  , s,  , d,  , mS,  , (1,  , occ)))) checkListfound(mS :: mSs) let (* found' is true iff D satisfies mS *)
let  in(* compute all other mode contexts *)
let  in in if found' then k (updateAtom (d,  , minus,  , s,  , d,  , mS,  , (1,  , occ))) @ ds' else ds' in checkList false (lookup (d,  , occ))(* checkDlocal (D, V, occ) = ()

       Invariant:
       If   G |- V : L
       and  D ~ G
       then checkD terminates with ()  iff V is mode correct.

       otherwise exception ModeError is raised (occ used in error messages)
    *)
let rec checkDlocal(d,  , v,  , occ) (try  with )(* --------------------------------------------------------- mode checking *)
let rec cidFromHead(const a) a cidFromHead(def a) a(* checkD (ConDec, occOpt)  = ()

       checkD terminates with () if ConDec is mode correct
       otherwise exception Error is raised

       (occOpt is used in error messages)
    *)
let rec checkD(conDec,  , fileName,  , occOpt) let let  inlet rec checkable(root (ha,  , _)) (match (mmodeLookup (cidFromHead ha)) with nil -> false _ -> true) checkable(uni _) false checkable(pi (_,  , v)) checkable vlet  in in if (checkable v) then try  with  else ()let rec checkAll(nil) () checkAll(const (c) :: clist) (if ! chatter > 3 then print (qidToString (constQid c) ^ " ") else (); try  with ; checkAll clist) checkAll(def (d) :: clist) (if ! chatter > 3 then print (qidToString (constQid d) ^ " ") else (); try  with ; checkAll clist)let rec checkMode(a,  , ms) let let  inlet  inlet  inlet  inlet  in in ()let rec checkFreeOut(a,  , ms) let let  inlet  inlet  inlet  inlet  in in ()let  inlet  inlet  inend