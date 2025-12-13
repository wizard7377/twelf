(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) ModeCheck ((*! structure IntSyn : INTSYN !*)
                   structure ModeTable : MODETABLE
                   (*! sharing ModeSyn.IntSyn = IntSyn !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn !*)
                   structure Index : INDEX
                   (*! sharing Index.IntSyn = IntSyn !*)
                   (*! structure Paths : PATHS !*)
                   structure Origins : ORIGINS
                   (*! sharing Origins.Paths = Paths !*)
                     (*! sharing Origins.IntSyn = IntSyn !*)
                       )
  : MODECHECK =
struct
  (*! structure IntSyn = IntSyn !*)
  (*! structure ModeSyn = ModeSyn !*)
  (*! structure Paths = Paths !*)

  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn
    structure P = Paths

    datatype uniqueness =               (* Uniqueness information *)
        Unique                          (* u ::= Unique           *)
      | Ambig                           (*     | Ambig            *)

    datatype info =                     (* Groundedness information   *)
        Free                            (* I ::= Free                 *)
      | Unknown                         (*     | Unknown              *)
      | Ground of uniqueness            (*     | Ground               *)

    datatype status =                   (* Variable status             *)
        Existential of                  (* S ::= Existential (I, xOpt) *)
          info * string option
      | Universal                       (*     | Universal             *)


    (* hack: if true, check freeness of output arguments in subgoals *)
    (* GEN BEGIN TAG OUTSIDE LET *) val checkFree = ref false (* GEN END TAG OUTSIDE LET *)

    (* Representation invariant:

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
    fun wrapMsg (c, occ, msg) =
        (case Origins.originLookup c
           of (fileName, NONE) => (fileName ^ ":" ^ msg)
            | (fileName, SOME occDec) =>
                (P.wrapLoc' (P.Loc (fileName, P.occToRegionClause occDec occ),
                             Origins.linesInfoLookup (fileName),
                             "Constant " ^ Names.qidToString (Names.constQid c) ^ "\n" ^ msg)))

    fun wrapMsg' (fileName, r, msg) =
          P.wrapLoc (P.Loc (fileName, r), msg)

    exception ModeError of P.occ * string
    exception Error' of P.occ * string

    (* lookup (a, occ) = mSs

       Invariant: mS are the argument modes for a
       Raises an error if no mode for a has declared.
       (occ is used in error message)
    *)
    fun lookup (a, occ) =
        case ModeTable.mmodeLookup a
          of nil => raise Error' (occ, "No mode declaration for " ^ I.conDecName (I.sgnLookup a))
           | sMs => sMs

    (* nameOf S, selects a name for S *)
    fun (* GEN BEGIN FUN FIRST *) nameOf (Existential (_, NONE)) = "?" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nameOf (Existential (_, SOME name)) = name (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nameOf _ = "?" (* GEN END FUN BRANCH *)

    (* unique (k, ks) = B

       Invariant:
       B iff k does not occur in ks
    *)
    fun (* GEN BEGIN FUN FIRST *) unique (k, nil) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) unique (k, k'::ks) =
          (k <> k') andalso unique (k, ks) (* GEN END FUN BRANCH *)

    (* isUniversal S = B

       Invariant:
       B iff S = Par
    *)
    fun (* GEN BEGIN FUN FIRST *) isUniversal Universal = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isUniversal _ = false (* GEN END FUN BRANCH *)

    (* isGround S = B

       Invariant:
       B iff S = Ex (T x)
    *)
    fun (* GEN BEGIN FUN FIRST *) isGround (Existential (Ground _, _)) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isGround _ = false (* GEN END FUN BRANCH *)

    (* uniqueness S = u
       where u is the uniqueness property of status S
    *)
    fun (* GEN BEGIN FUN FIRST *) uniqueness (Existential (Ground (u), _)) = u (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) uniqueness (Universal) = Unique (* GEN END FUN BRANCH *)

    (* ambiguate (mode) = mode'
       where mode' forgets uniqueness properties
    *)
    fun (* GEN BEGIN FUN FIRST *) ambiguate (M.Plus) = M.Plus (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ambiguate (M.Minus) = M.Minus (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ambiguate (M.Minus1) = M.Minus (* GEN END FUN BRANCH *)

    (* andUnique (u1, u2) = Unique if u1 = u2 = Unique
       = Ambig otherwise
    *)
    fun (* GEN BEGIN FUN FIRST *) andUnique (Unique, Unique) = Unique (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) andUnique _ = Ambig (* GEN END FUN BRANCH *)

    (* isFree S = b

       Invariant:
       b iff S = Ex (B x)
    *)
    fun (* GEN BEGIN FUN FIRST *) isFree (Existential (Free, _)) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isFree _ = false (* GEN END FUN BRANCH *)

    exception Eta

    (* etaContract (U, n) = k

       if lam V1... lam Vn. U =eta*=> k
       otherwise raise exception Eta

       Invariant: G, V1,..., Vn |- U : V for some G, Vi, V.
                  U in NF
    *)
    fun (* GEN BEGIN FUN FIRST *) etaContract (I.Root (I.BVar(k), S),  n) =
        if k > n
          then ( etaSpine (S, n) ; k-n )
        else raise Eta (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) etaContract (I.Lam (D, U), n) =
          etaContract (U, n+1) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) etaContract _ = raise Eta (* GEN END FUN BRANCH *)

    (* etaSpine (S, n) = ()
       if S =eta*=> n ; n-1 ; ... ; 1 ; Nil
       otherwise raise exception Eta

       Invariant: G |- S : V1 >> V2 for some G, V1, V2
                  S in NF
    *)
    and (* GEN BEGIN FUN FIRST *) etaSpine (I.Nil, 0) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) etaSpine (I.App (U, S), n) =
        if etaContract (U, 0) = n
          then etaSpine (S, n-1)
        else raise Eta (* GEN END FUN BRANCH *)
      (* S[s] should be impossible *)

    (* isPattern (D, k, mS) = B

       Invariant:
       B iff k > k' for all k' in mS
         and for all k in mS: k is parameter
         and for all k', k'' in mS: k' <> k''
    *)
    fun (* GEN BEGIN FUN FIRST *) checkPattern (D, k, args, I.Nil) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkPattern (D, k, args, I.App (U, S)) =
        (let
           (* GEN BEGIN TAG OUTSIDE LET *) val k' = etaContract (U, 0) (* GEN END TAG OUTSIDE LET *)
         in
           if (k > k')
             andalso isUniversal (I.ctxLookup (D, k'))
             andalso unique (k', args)
             then checkPattern (D, k, k'::args, S)
           else raise Eta
         end) (* GEN END FUN BRANCH *)

    fun isPattern (D, k, S) =
        (checkPattern (D, k, nil, S); true)
        handle Eta => false

    (* ------------------------------------------- strictness check *)
    (* This repeats some code from ../typecheck/strict.fun *)
    (* Interface here is somewhat different *)

    (* strictExpN (D, p, U) = B

       Invariant:
       If  D |- U : V
       and U is in nf (normal form)
       then B iff U is strict in p
    *)
    fun (* GEN BEGIN FUN FIRST *) strictExpN (D, _, I.Uni _) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strictExpN (D, p, I.Lam (_, U)) =
          (* checking D in this case should be redundant -fp *)
          (* strictDecN (D, p, D) orelse *)
          strictExpN (I.Decl(D, Universal), p+1, U) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strictExpN (D, p, I.Pi ((D', _), U)) =
          strictDecN (D, p, D') orelse strictExpN (I.Decl(D, Universal), p+1, U) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strictExpN (D, p, I.Root (H, S)) =
          (case H
             of (I.BVar (k')) =>
                if (k' = p) then isPattern (D, k', S)
                else if isUniversal (I.ctxLookup (D, k')) then strictSpineN (D, p, S)
                     else false
                     (* equivalently: isUniversal .. andalso strictSpineN .. *)
              | (I.Const (c)) => strictSpineN (D, p, S)
              | (I.Def (d))  => strictSpineN (D, p, S)
              | (I.FgnConst (cs, conDec)) => strictSpineN (D, p, S)) (* GEN END FUN BRANCH *)
              (* no other cases possible *)
      | (* GEN BEGIN FUN BRANCH *) strictExpN (D, p, I.FgnExp (cs, ops)) = false (* GEN END FUN BRANCH *)
          (* this is a hack - until we investigate this further   -rv *)
    (* no other cases possible *)

    (* strictSpineN (D, S) = B

       Invariant:
       If  D |- S : V > W
       and S is in nf (normal form)
       then B iff S is strict in k
    *)
    and (* GEN BEGIN FUN FIRST *) strictSpineN (_, _, I.Nil) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strictSpineN (D, p, I.App (U, S)) =
          strictExpN (D, p, U) orelse strictSpineN (D, p, S) (* GEN END FUN BRANCH *)

    and strictDecN (D, p, I.Dec (_, V)) =
          strictExpN (D, p, V)

    (*
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
    fun (* GEN BEGIN FUN FIRST *) freeExpN (D, d, mode, I.Root (I.BVar k, S), occ, strictFun) =
          (freeVar (D, d, mode, k, P.head occ, strictFun);
           freeSpineN (D, d, mode, S, (1, occ), strictFun)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) freeExpN (D, d, mode, I.Root (I.Const _, S), occ, strictFun) =
          freeSpineN (D, d, mode, S, (1, occ), strictFun) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) freeExpN (D, d, mode, I.Root (I.Def _, S), occ, strictFun) =
          freeSpineN (D, d, mode, S, (1, occ), strictFun) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) freeExpN (D, d, mode, I.Root (I.FgnConst (cs, conDec), S), occ, strictFun) =
          freeSpineN (D, d, mode, S, (1, occ), strictFun) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) freeExpN (D, d, mode, I.Lam (_, U), occ, strictFun) =
          freeExpN (I.Decl (D, Universal), d+1, mode, U, P.body occ, strictFun) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) freeExpN (D, d, mode, I.FgnExp csfe, occ, strictFun) =
        I.FgnExpStd.App.apply csfe ((* GEN BEGIN FUNCTION EXPRESSION *) fn U => freeExpN (D, d, mode, Whnf.normalize (U, I.id), occ, strictFun) (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN BRANCH *)
        (* punting on the occ here  - ak *)

    (* freeSpineN (D, mode, S, occ, strictFun)  = ()

       If   G |- S : V1  > V2   (S in nf)
       and  G ~ D
       then freeSpineN terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
    and (* GEN BEGIN FUN FIRST *) freeSpineN (D, d, mode, I.Nil, _, strictFun) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) freeSpineN (D, d, mode, I.App (U, S), (p, occ), strictFun) =
          (freeExpN (D, d, mode, U, P.arg (p, occ), strictFun);
           freeSpineN (D, d, mode, S, (p+1, occ), strictFun)) (* GEN END FUN BRANCH *)

    (* freeVar (D, mode, k, occ, strictFun)  = ()

       If   G |- k : V1
       and  G ~ D
       then freeVar terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)

    and freeVar (D, d, mode, k, occ, strictFun) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val status = I.ctxLookup (D, k) (* GEN END TAG OUTSIDE LET *)
        in
          if isFree status orelse isUniversal status orelse strictFun (k-d)
            then ()
          else raise ModeError (occ, "Occurrence of variable " ^ (nameOf status) ^
                                " in " ^ (M.modeToString mode) ^ " argument not free")
        end


    (* -------------------------------- non-strict mode context update *)
    (* nonStrictExpN (D, U) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Unknown for all existential variables k
            in U that are free in D
    *)
    fun (* GEN BEGIN FUN FIRST *) nonStrictExpN (D, I.Root (I.BVar (k), S)) =
          nonStrictSpineN (nonStrictVarD (D, k), S) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nonStrictExpN (D, I.Root (I.Const c, S)) =
          nonStrictSpineN (D, S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nonStrictExpN (D, I.Root (I.Def d, S)) =
          nonStrictSpineN (D, S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nonStrictExpN (D, I.Root (I.FgnConst (cs, conDec), S)) =
          nonStrictSpineN (D, S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nonStrictExpN (D, I.Lam (_, U)) =
          I.ctxPop (nonStrictExpN (I.Decl (D, Universal), U)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nonStrictExpN (D, I.FgnExp _) =
          raise Error ("Foreign expressions not permitted when checking freeness") (* GEN END FUN BRANCH *)

    (* nonStrictSpineN (D, S) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Unkown for all existential variables k
            in S that are Free in D
    *)
    and (* GEN BEGIN FUN FIRST *) nonStrictSpineN (D, I.Nil) = D (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nonStrictSpineN (D, I.App (U, S)) =
          nonStrictSpineN (nonStrictExpN (D, U), S) (* GEN END FUN BRANCH *)

    (* nonStrictVarD (D, k) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is nonStrictd as described in  nonStrictExpN
    *)
    and (* GEN BEGIN FUN FIRST *) nonStrictVarD (I.Decl (D, Existential (Free, name)), 1) =
          I.Decl (D, Existential (Unknown, name)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nonStrictVarD (D, 1) = (* Universal, or already Unknown or Ground - leave unchanged *)
          D (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nonStrictVarD (I.Decl (D, status), k) =
          I.Decl (nonStrictVarD (D, k-1), status) (* GEN END FUN BRANCH *)

    (* ------------------------------------------- mode context update *)

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
    fun (* GEN BEGIN FUN FIRST *) updateExpN (D, I.Root (I.BVar (k), S), u) =
          if isUniversal (I.ctxLookup (D, k))
            then updateSpineN (D, S, u)
          else
            if isPattern (D, k, S)
              then updateVarD (D, k, u)
            else if !checkFree
                   then nonStrictSpineN (nonStrictVarD (D, k), S)
                 else D (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) updateExpN (D, I.Root (I.Const c, S), u) =
          updateSpineN (D, S, u) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) updateExpN (D, I.Root (I.Def d, S), u) =
          updateSpineN (D, S, u) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) updateExpN (D, I.Root (I.FgnConst (cs, conDec), S), u) =
          updateSpineN (D, S, u) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) updateExpN (D, I.Lam (_, U), u) =
          I.ctxPop (updateExpN (I.Decl (D, Universal), U, u)) (* GEN END FUN BRANCH *)
      (* no occurrence inside a FgnExp is considered strict *)
      | (* GEN BEGIN FUN BRANCH *) updateExpN (D, I.FgnExp _, u) = D (* GEN END FUN BRANCH *)

    (* updateSpineN (D, S, u) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Ground for all existential variables k
            with a strict occurrence in S
    *)
    and (* GEN BEGIN FUN FIRST *) updateSpineN (D, I.Nil, u) = D (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) updateSpineN (D, I.App (U, S), u) =
          updateSpineN (updateExpN (D, U, u), S, u) (* GEN END FUN BRANCH *)

    (* updateVarD (D, k, u) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is updated as described in  updateExpN
    *)
    and (* GEN BEGIN FUN FIRST *) updateVarD (I.Decl (D, Existential (_, name)), 1, u) =
          I.Decl (D, Existential (Ground (u), name)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) updateVarD (I.Decl (D, status), k, u) =
          I.Decl (updateVarD (D, k-1, u), status) (* GEN END FUN BRANCH *)

    (* ----------------------- mode context update by argument modes *)

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
    fun (* GEN BEGIN FUN FIRST *) updateAtom' (D, mode, I.Nil, M.Mnil, _) = D (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) updateAtom' (D, M.Plus, I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS), (p, occ)) =
          updateAtom' (updateExpN (D, U, Unique), M.Plus, S, mS, (p+1, occ)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) updateAtom' (D, M.Minus, I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ)) =
          updateAtom' (updateExpN (D, U, Ambig), M.Minus, S, mS, (p+1, occ)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) updateAtom' (D, M.Minus, I.App (U, S), M.Mapp (M.Marg (M.Minus1, _), mS), (p, occ)) =
          updateAtom' (updateExpN (D, U, Ambig), M.Minus, S, mS, (p+1, occ)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) updateAtom' (D, M.Minus1, I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ)) =
          updateAtom' (updateExpN (D, U, Ambig), M.Minus1, S, mS, (p+1, occ)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) updateAtom' (D, M.Minus1, I.App (U, S), M.Mapp (M.Marg (M.Minus1, _), mS), (p, occ)) =
          updateAtom' (updateExpN (D, U, Unique), M.Minus1, S, mS, (p+1, occ)) (* GEN END FUN BRANCH *)
      (* when checking freeness, all arguments must be input (+) or output (-) *)
      (* therefore, no case for M.Mapp (M.Marg (M.Minus, _), mS) is provided here *)
      | (* GEN BEGIN FUN BRANCH *) updateAtom' (D, mode, I.App (U, S), M.Mapp (_, mS), (p, occ)) =
          updateAtom' (D, mode, S, mS, (p+1, occ)) (* GEN END FUN BRANCH *)

    (* freeAtom (D, m, S, (V,s), mS, (p, occ)) = ()

       checks if all output arguments in S according to mS are free.
       Invariant: G |- S : V[s] >> P for some G and P  (S in nf)
                  G ~ D
                  mode = (-) or (+); ( * ) or (-1) are excluded
    *)
    fun (* GEN BEGIN FUN FIRST *) freeAtom (D, mode, I.Nil, Vs, M.Mnil, _) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) freeAtom (D, M.Minus, I.App (U, S), (I.Pi ((I.Dec (_, V1), _), V2), s),
                  M.Mapp (M.Marg (M.Minus, _), mS), (p, occ)) =
          (freeExpN (D, 0, M.Minus, U, P.arg(p, occ),
                     ((* GEN BEGIN FUNCTION EXPRESSION *) fn q => strictExpN (D, q, Whnf.normalize (V1, s)) (* GEN END FUNCTION EXPRESSION *)));
           freeAtom (D, M.Minus, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)), mS, (p+1, occ))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) freeAtom (D, mode, I.App (U, S), (I.Pi (_, V2), s), M.Mapp (_, mS), (p, occ)) =
          freeAtom (D, mode, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)), mS, (p+1, occ)) (* GEN END FUN BRANCH *)

    (* updateAtom (D, m, S, a, mS, (p, occ))
       see updateAtom', and performs additional freeness check if required
    *)
    fun updateAtom (D, mode, S, a, mS, (p, occ)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !checkFree
                    then freeAtom (D, ambiguate mode, S, (I.constType a, I.id), mS, (p, occ))
                  else () (* GEN END TAG OUTSIDE LET *)
        in
          updateAtom' (D, mode, S, mS, (p, occ))
        end

    (* ------------------------------------------- groundness check *)

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
    fun (* GEN BEGIN FUN FIRST *) groundExpN (D, mode, I.Root (I.BVar k, S), occ) =
          andUnique (groundVar (D, mode, k, P.head occ),
                     groundSpineN (D, mode, S, (1, occ))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) groundExpN (D, mode, I.Root (I.Const c, S), occ) =
          groundSpineN (D, mode, S, (1, occ)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) groundExpN (D, mode, I.Root (I.Def d, S), occ) =
          groundSpineN (D, mode, S, (1, occ)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) groundExpN (D, mode, I.Root (I.FgnConst (cs, conDec), S), occ) =
          groundSpineN (D, mode, S, (1, occ)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) groundExpN (D, mode, I.Lam (_, U), occ) =
          groundExpN (I.Decl (D, Universal), mode, U, P.body occ) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) groundExpN (D, mode, I.FgnExp csfe, occ) =
        I.FgnExpStd.fold csfe ((* GEN BEGIN FUNCTION EXPRESSION *) fn (U,u) => andUnique (groundExpN (D, mode, Whnf.normalize (U, I.id), occ), u) (* GEN END FUNCTION EXPRESSION *)) Unique (* GEN END FUN BRANCH *)
        (* punting on occ here  - ak *)

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
    and (* GEN BEGIN FUN FIRST *) groundSpineN (D, mode, I.Nil, _) = Unique (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) groundSpineN (D, mode, I.App (U, S), (p, occ)) =
          andUnique (groundExpN (D, mode, U, P.arg (p, occ)),
                     groundSpineN (D, mode, S, (p+1, occ))) (* GEN END FUN BRANCH *)

    (* groundVar (D, mode, k, occ)  = u

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
    and (* GEN BEGIN FUN FIRST *) groundVar (D, M.Minus1, k, occ) =
        (case I.ctxLookup (D, k)
           of Existential (Ground (Unique), _) => Unique
            | Universal => Unique
            | s as Existential (Ground (Ambig), x) =>
              raise ModeError (occ, "Occurrence of variable " ^ nameOf s
                               ^ " in " ^ M.modeToString M.Minus1
                               ^ " argument not necessarily unique")
            | s => (* Existential (Free, _) or Existential (Unknown, _) *)
                raise ModeError (occ, "Occurrence of variable " ^ (nameOf s)
                                 ^ " in " ^ (M.modeToString M.Minus1)
                                 ^ " argument not necessarily ground")) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) groundVar (D, mode, k, occ) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val status = I.ctxLookup (D, k) (* GEN END TAG OUTSIDE LET *)
        in
          if isGround status orelse isUniversal status
            then uniqueness status
          else raise ModeError (occ, "Occurrence of variable " ^ (nameOf status) ^
                                " in " ^ (M.modeToString mode)
                                ^ " argument not necessarily ground")
        end (* GEN END FUN BRANCH *)

    (* ------------------------------------------- groundness check by polarity *)

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
    fun (* GEN BEGIN FUN FIRST *) groundAtom (D, _, I.Nil, M.Mnil, _) = Unique (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) groundAtom (D, M.Plus, I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS), (p, occ)) =
          andUnique (groundExpN (D, M.Plus, U, P.arg (p, occ)),
                     groundAtom (D, M.Plus, S, mS, (p+1, occ))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) groundAtom (D, M.Minus, I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ)) =
          (groundExpN (D, M.Minus, U, P.arg (p, occ)); (* ignore uniqueness result here *)
           groundAtom (D, M.Minus, S, mS, (p+1, occ))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) groundAtom (D, M.Minus, I.App (U, S), M.Mapp (M.Marg (M.Minus1, _), mS), (p, occ)) =
          (groundExpN (D, M.Minus1, U, P.arg (p, occ)); (* ignore uniqueness result here *)
           groundAtom (D, M.Minus, S, mS, (p+1, occ))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) groundAtom (D, mode, I.App (U, S), M.Mapp (_, mS), (p, occ)) =
          groundAtom (D, mode, S, mS, (p+1, occ)) (* GEN END FUN BRANCH *)


    (* ------------------------------------------- mode checking first phase *)

    (* ctxPush (Ds, m) = Ds'
       raises the contexts Ds prepending m
    *)
    fun ctxPush (m, Ds) = List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn D => I.Decl (D, m) (* GEN END FUNCTION EXPRESSION *)) Ds

    (* ctxPop Ds = Ds'
       lowers the contexts Ds
    *)
    fun ctxPop Ds = List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn I.Decl (D, m) => D (* GEN END FUNCTION EXPRESSION *)) Ds

    (* checkD1 (D, V, occ, k) = ()

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
    fun (* GEN BEGIN FUN FIRST *) checkD1 (D, I.Pi ((I.Dec (name, _), I.Maybe), V), occ, k) =
          checkD1 (I.Decl (D, Existential (Free, name)), V, P.body occ,
                   (* GEN BEGIN FUNCTION EXPRESSION *) fn (I.Decl (D', m)) => ctxPush (m, k D') (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkD1 (D, I.Pi ((I.Dec (name, V1), I.No), V2), occ, k) =
          checkD1 (I.Decl (D, Existential (Free, name)), V2, P.body occ,
                   (* GEN BEGIN FUNCTION EXPRESSION *) fn (I.Decl (D', m)) => ctxPush (m, checkG1 (D', V1, P.label occ, k)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkD1 (D, I.Root (I.Const a, S), occ, k) =
          let
            (* for a declaration, all modes must be satisfied *)
            fun (* GEN BEGIN FUN FIRST *) checkAll nil = () (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) checkAll (mS :: mSs) =
                  let
                    fun (* GEN BEGIN FUN FIRST *) checkSome [D'] =
                          (* D' is the only (last) possibility; on failure, we raise ModeError *)
                          (
                            groundAtom (D', M.Minus, S, mS, (1, occ)); (* ignore return *)
                            checkAll mSs
                          ) (* GEN END FUN FIRST *)
                      | (* GEN BEGIN FUN BRANCH *) checkSome (D' :: Ds) =
                          (* try D', if it doesn't work, try another context in the Ds *)
                          (
                            ((groundAtom (D', M.Minus, S, mS, (1, occ));()) (* ignore return *)
                             handle ModeError _ => checkSome Ds);
                            checkAll mSs
                          ) (* GEN END FUN BRANCH *)
                  in
                    checkSome (k (updateAtom (D, M.Plus, S, a, mS, (1, occ))))
                  end (* GEN END FUN BRANCH *)
          in
            checkAll (lookup (a, occ))
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkD1 (D, I.Root (I.Def d, S), occ, k) =
          let
            (* for a declaration, all modes must be satisfied *)
            fun (* GEN BEGIN FUN FIRST *) checkAll nil = () (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) checkAll (mS :: mSs) =
                  let
                    fun (* GEN BEGIN FUN FIRST *) checkSome [D'] =
                          (* D' is the only (last) possibility; on failure, we raise ModeError *)
                          (
                            groundAtom (D', M.Minus, S, mS, (1, occ)); (* ignore return *)
                            checkAll mSs
                          ) (* GEN END FUN FIRST *)
                      | (* GEN BEGIN FUN BRANCH *) checkSome (D' :: Ds) =
                          (* try D', if it doesn't work, try another context in the Ds *)
                          (
                            ((groundAtom (D', M.Minus, S, mS, (1, occ)); ()) (* ignore return *)
                             handle ModeError _ => checkSome Ds);
                            checkAll mSs
                          ) (* GEN END FUN BRANCH *)
                  in
                    checkSome (k (updateAtom (D, M.Plus, S, d, mS, (1, occ))))
                  end (* GEN END FUN BRANCH *)
          in
            checkAll (lookup (d, occ))
          end (* GEN END FUN BRANCH *)

    (* checkG1 (D, V, occ, k) = Ds

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
    and (* GEN BEGIN FUN FIRST *) checkG1 (D, I.Pi ((_, I.Maybe), V), occ, k) =
          ctxPop (checkG1 (I.Decl (D, Universal), V, P.body occ,
                           (* GEN BEGIN FUNCTION EXPRESSION *) fn (I.Decl (D', m)) => ctxPush (m, k D') (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkG1 (D, I.Pi ((I.Dec (_, V1) , I.No), V2), occ, k) =
          ctxPop (checkD1 (D, V1, P.label occ, (* GEN BEGIN FUNCTION EXPRESSION *) fn D' => [D'] (* GEN END FUNCTION EXPRESSION *));
                  checkG1 (I.Decl (D, Universal), V2, P.body occ,
                           (* GEN BEGIN FUNCTION EXPRESSION *) fn (I.Decl (D', m)) => ctxPush (m, k D') (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkG1 (D, I.Root (I.Const a, S), occ, k) =
          let
            (* for a goal, at least one mode must be satisfied *)
            fun (* GEN BEGIN FUN FIRST *) checkList found nil = nil (* GEN END FUN FIRST *) (* found = true *)
              | (* GEN BEGIN FUN BRANCH *) checkList false [mS] =
                  (* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
                  (
                    case groundAtom (D, M.Plus, S, mS, (1, occ))
                      of Unique => k (updateAtom (D, M.Minus1, S, a, mS, (1, occ)))
                       | Ambig => k (updateAtom (D, M.Minus, S, a, mS, (1, occ)))
                  ) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) checkList found (mS :: mSs) =
                  (* uniqueness not permitted on multiple modes right now *)
                  (* Wed Aug 20 21:52:31 2003 -fp *)
                  let
                    (* found' is true iff D satisfies mS *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val found' = ((groundAtom (D, M.Plus, S, mS, (1, occ)); true) (* handler scope??? -fp *)
                                  handle ModeError _ => false) (* GEN END TAG OUTSIDE LET *)
                    (* compute all other mode contexts *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = checkList (found orelse found') mSs (* GEN END TAG OUTSIDE LET *)
                  in
                    if found'
                    then k (updateAtom (D, M.Minus, S, a, mS, (1, occ))) @ Ds'
                    else Ds'
                  end (* GEN END FUN BRANCH *)
          in
            checkList false (lookup (a, occ))
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkG1 (D, I.Root (I.Def d, S), occ, k) =
          let
            (* for a goal, at least one mode must be satisfied *)
            fun (* GEN BEGIN FUN FIRST *) checkList found nil = nil (* GEN END FUN FIRST *) (* found = true *)
              | (* GEN BEGIN FUN BRANCH *) checkList false [mS] =
                  (* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *)
                  (
                    case groundAtom (D, M.Plus, S, mS, (1, occ))
                      of Unique => k (updateAtom (D, M.Minus1, S, d, mS, (1, occ)))
                       | Ambig => k (updateAtom (D, M.Minus, S, d, mS, (1, occ)))
                  ) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) checkList found (mS :: mSs) =
                  (* uniqueness not permitted on multiple modes right now *)
                  (* Wed Aug 20 21:52:31 2003 -fp *)
                  let
                    (* found' is true iff D satisfies mS *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val found' = ((groundAtom (D, M.Plus, S, mS, (1, occ)); true)
                                  handle ModeError _ => false) (* GEN END TAG OUTSIDE LET *)
                    (* compute all other mode contexts *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = checkList (found orelse found') mSs (* GEN END TAG OUTSIDE LET *)
                  in
                    if found'
                    then k (updateAtom (D, M.Minus, S, d, mS, (1, occ))) @ Ds'
                    else Ds'
                  end (* GEN END FUN BRANCH *)
          in
            checkList false (lookup (d, occ))
          end (* GEN END FUN BRANCH *)

    (* checkDlocal (D, V, occ) = ()

       Invariant:
       If   G |- V : L
       and  D ~ G
       then checkD terminates with ()  iff V is mode correct.

       otherwise exception ModeError is raised (occ used in error messages)
    *)
    fun checkDlocal (D, V, occ) =
          (checkD1 (D, V, occ, (* GEN BEGIN FUNCTION EXPRESSION *) fn D' => [D'] (* GEN END FUNCTION EXPRESSION *))
           handle ModeError (occ, msg) => raise Error' (occ, msg))

    (* --------------------------------------------------------- mode checking *)


    fun (* GEN BEGIN FUN FIRST *) cidFromHead (I.Const a) = a (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) cidFromHead (I.Def a) = a (* GEN END FUN BRANCH *)

    (* checkD (ConDec, occOpt)  = ()

       checkD terminates with () if ConDec is mode correct
       otherwise exception Error is raised

       (occOpt is used in error messages)
    *)
    fun checkD (conDec, fileName, occOpt) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = (checkFree := false) (* GEN END TAG OUTSIDE LET *)
          fun (* GEN BEGIN FUN FIRST *) checkable (I.Root (Ha, _)) =
              (case (ModeTable.mmodeLookup (cidFromHead Ha))
                 of nil => false
                  | _ => true) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) checkable (I.Uni _) = false (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) checkable (I.Pi (_, V)) = checkable V (* GEN END FUN BRANCH *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V = I.conDecType conDec (* GEN END TAG OUTSIDE LET *)
        in
          if (checkable V)
            then checkDlocal (I.Null, V, P.top)
                 handle Error' (occ, msg) =>
                   (case occOpt
                      of NONE => raise Error (msg)
                       | SOME occTree =>
                           raise Error (wrapMsg' (fileName, P.occToRegionClause occTree occ, msg)))
          else ()
        end

    fun (* GEN BEGIN FUN FIRST *) checkAll (nil) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkAll (I.Const(c) :: clist) =
        (if !Global.chatter > 3
           then print (Names.qidToString (Names.constQid c) ^ " ")
         else ();
         checkDlocal (I.Null, I.constType c, P.top)
           handle Error' (occ, msg) => raise Error (wrapMsg (c, occ, msg));
         checkAll clist) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkAll (I.Def(d) :: clist) =
        (if !Global.chatter > 3
           then print (Names.qidToString (Names.constQid d) ^ " ")
         else ();
         checkDlocal (I.Null, I.constType d, P.top)
           handle Error' (occ, msg) => raise Error (wrapMsg (d, occ, msg));
         checkAll clist) (* GEN END FUN BRANCH *)

    fun checkMode (a, ms) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter > 3
                    then print ("Mode checking family " ^ Names.qidToString (Names.constQid a) ^ ":\n")
                  else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val clist = Index.lookup a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = (checkFree := false) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkAll clist (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter > 3 then print "\n" else () (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end

    fun checkFreeOut (a, ms) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter > 3
                    then print ("Checking output freeness of " ^ Names.qidToString (Names.constQid a) ^ ":\n")
                  else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val clist = Index.lookup a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = (checkFree := true) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkAll clist (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter > 3 then print "\n" else () (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val checkD = checkD (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val checkMode = checkMode (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val checkFreeOut = checkFreeOut (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *);  (* functor ModeCheck *)

