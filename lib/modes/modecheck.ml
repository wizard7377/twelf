(* Mode Checking *)

(* Author: Carsten Schuermann *)

(* Modified: Frank Pfenning, Roberto Virga *)

module ModeCheck
    (ModeTable : MODETABLE)
    (Whnf : WHNF)
    (Index : INDEX)
    (Origins : ORIGINS) : MODECHECK = struct
  (*! structure IntSyn = IntSyn !*)

  (*! structure ModeSyn = ModeSyn !*)

  (*! structure Paths = Paths !*)

  exception Error of string

  module I = IntSyn
  module M = ModeSyn
  module P = Paths

  type uniqueness = Unique | Ambig
  (*     | Ambig            *)

  type info = Free | Unknown | Ground of uniqueness
  (*     | Ground               *)

  type status =
    | Existential of
        (* S ::= Existential (I, xOpt) *)
        info
        * string option
    | Universal
  (*     | Universal             *)

  (* hack: if true, check freeness of output arguments in subgoals *)

  let checkFree = ref false
  (* Representation invariant:

       Groundness information:
       T stands for_sml ground, B stands for_sml unknown
       Ex  for_sml a named existential variable
       Par for_sml a parameter

       Mode context   D ::= . | D, S

       If D contains Status information for_sml variables in
       a context G, we write G ~ D
       We write D' >= D if for_sml all i
         D(i) par iff D'(i) par
         D(i) bot implies D'(i) bot or D'(i) top
         D(i) top implies D'(i) top
    *)

  (* copied from worldcheck/worldsyn.fun *)

  let rec wrapMsg (c, occ, msg) =
    match Origins.originLookup c with
    | fileName, None -> fileName ^ ":" ^ msg
    | fileName, Some occDec ->
        P.wrapLoc'
          ( P.Loc (fileName, P.occToRegionClause occDec occ),
            Origins.linesInfoLookup fileName,
            "Constant " ^ Names.qidToString (Names.constQid c) ^ "\n" ^ msg )

  let rec wrapMsg' (fileName, r, msg) = P.wrapLoc (P.Loc (fileName, r), msg)

  exception ModeError of P.occ * string
  exception Error' of P.occ * string
  (* lookup (a, occ) = mSs

       Invariant: mS are the argument modes for_sml a
       Raises an error if no mode for_sml a has declared.
       (occ is used in error message)
    *)

  let rec lookup (a, occ) =
    match ModeTable.mmodeLookup a with
    | [] ->
        raise
          (Error'
             (occ, "No mode declaration for_sml " ^ I.conDecName (I.sgnLookup a)))
    | sMs -> sMs
  (* nameOf S, selects a name for_sml S *)

  let rec nameOf = function
    | Existential (_, None) -> "?"
    | Existential (_, Some name) -> name
    | _ -> "?"
  (* unique (k, ks) = B

       Invariant:
       B iff k does not occur in ks
    *)

  let rec unique = function
    | k, [] -> true
    | k, k' :: ks -> k <> k' && unique (k, ks)
  (* isUniversal S = B

       Invariant:
       B iff S = Par
    *)

  let rec isUniversal = function Universal -> true | _ -> false
  (* isGround S = B

       Invariant:
       B iff S = Ex (T x)
    *)

  let rec isGround = function Existential (Ground _, _) -> true | _ -> false
  (* uniqueness S = u
       where u is the uniqueness property of status S
    *)

  let rec uniqueness = function
    | Existential (Ground u, _) -> u
    | Universal -> Unique
  (* ambiguate (mode) = mode'
       where mode' forgets uniqueness properties
    *)

  let rec ambiguate = function
    | M.Plus -> M.Plus
    | M.Minus -> M.Minus
    | M.Minus1 -> M.Minus
  (* andUnique (u1, u2) = Unique if u1 = u2 = Unique
       = Ambig otherwise
    *)

  let rec andUnique = function Unique, Unique -> Unique | _ -> Ambig
  (* isFree S = b

       Invariant:
       b iff S = Ex (B x)
    *)

  let rec isFree = function Existential (Free, _) -> true | _ -> false

  exception Eta
  (* etaContract (U, n) = k

       if lam V1... lam Vn. U =eta*=> k
       otherwise raise exception Eta

       Invariant: G, V1,..., Vn |- U : V for_sml some G, Vi, V.
                  U in NF
    *)

  let rec etaContract = function
    | I.Root (I.BVar k, S), n ->
        if k > n then (
          etaSpine (S, n);
          k - n)
        else raise Eta
    | I.Lam (D, U), n -> etaContract (U, n + 1)
    | _ -> raise Eta

  and etaSpine = function
    | I.Nil, 0 -> ()
    | I.App (U, S), n ->
        if etaContract (U, 0) = n then etaSpine (S, n - 1) else raise Eta
  (* S[s] should be impossible *)

  (* isPattern (D, k, mS) = B

       Invariant:
       B iff k > k' for_sml all k' in mS
         and for_sml all k in mS: k is parameter
         and for_sml all k', k'' in mS: k' <> k''
    *)

  let rec checkPattern = function
    | D, k, args, I.Nil -> ()
    | D, k, args, I.App (U, S) ->
        let k' = etaContract (U, 0) in
        if k > k' && isUniversal (I.ctxLookup (D, k')) && unique (k', args) then
          checkPattern (D, k, k' :: args, S)
        else raise Eta

  let rec isPattern (D, k, S) =
    try
      checkPattern (D, k, [], S);
      true
    with Eta -> false
  (* ------------------------------------------- strictness check *)

  (* This repeats some code from ../typecheck/strict.fun *)

  (* Interface here is somewhat different *)

  (* strictExpN (D, p, U) = B

       Invariant:
       If  D |- U : V
       and U is in nf (normal form)
       then B iff U is strict in p
    *)

  let rec strictExpN = function
    | D, _, I.Uni _ -> false
    | D, p, I.Lam (_, U) -> strictExpN (I.Decl (D, Universal), p + 1, U)
    | D, p, I.Pi ((D', _), U) ->
        strictDecN (D, p, D') || strictExpN (I.Decl (D, Universal), p + 1, U)
    | D, p, I.Root (H, S) -> (
        match H with
        | I.BVar k' ->
            if k' = p then isPattern (D, k', S)
            else if isUniversal (I.ctxLookup (D, k')) then strictSpineN (D, p, S)
            else false
              (* equivalently: isUniversal .. andalso strictSpineN .. *)
        | I.Const c -> strictSpineN (D, p, S)
        | I.Def d -> strictSpineN (D, p, S)
        | I.FgnConst (cs, conDec) -> strictSpineN (D, p, S))
    | D, p, I.FgnExp (cs, ops) -> false

  and strictSpineN = function
    | _, _, I.Nil -> false
    | D, p, I.App (U, S) -> strictExpN (D, p, U) || strictSpineN (D, p, S)

  and strictDecN (D, p, I.Dec (_, V)) = strictExpN (D, p, V)
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

  let rec freeExpN = function
    | D, d, mode, I.Root (I.BVar k, S), occ, strictFun ->
        freeVar (D, d, mode, k, P.head occ, strictFun);
        freeSpineN (D, d, mode, S, (1, occ), strictFun)
    | D, d, mode, I.Root (I.Const _, S), occ, strictFun ->
        freeSpineN (D, d, mode, S, (1, occ), strictFun)
    | D, d, mode, I.Root (I.Def _, S), occ, strictFun ->
        freeSpineN (D, d, mode, S, (1, occ), strictFun)
    | D, d, mode, I.Root (I.FgnConst (cs, conDec), S), occ, strictFun ->
        freeSpineN (D, d, mode, S, (1, occ), strictFun)
    | D, d, mode, I.Lam (_, U), occ, strictFun ->
        freeExpN (I.Decl (D, Universal), d + 1, mode, U, P.body occ, strictFun)
    | D, d, mode, I.FgnExp csfe, occ, strictFun ->
        I.FgnExpStd.App.apply csfe (fun U ->
            freeExpN (D, d, mode, Whnf.normalize (U, I.id), occ, strictFun))

  and freeSpineN = function
    | D, d, mode, I.Nil, _, strictFun -> ()
    | D, d, mode, I.App (U, S), (p, occ), strictFun ->
        freeExpN (D, d, mode, U, P.arg (p, occ), strictFun);
        freeSpineN (D, d, mode, S, (p + 1, occ), strictFun)

  and freeVar (D, d, mode, k, occ, strictFun) =
    let status = I.ctxLookup (D, k) in
    if isFree status || isUniversal status || strictFun (k - d) then ()
    else
      raise
        (ModeError
           ( occ,
             "Occurrence of variable " ^ nameOf status ^ " in "
             ^ M.modeToString mode ^ " argument not free" ))
  (* -------------------------------- non-strict mode context update *)

  (* nonStrictExpN (D, U) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Unknown for_sml all existential variables k
            in U that are free in D
    *)

  let rec nonStrictExpN = function
    | D, I.Root (I.BVar k, S) -> nonStrictSpineN (nonStrictVarD (D, k), S)
    | D, I.Root (I.Const c, S) -> nonStrictSpineN (D, S)
    | D, I.Root (I.Def d, S) -> nonStrictSpineN (D, S)
    | D, I.Root (I.FgnConst (cs, conDec), S) -> nonStrictSpineN (D, S)
    | D, I.Lam (_, U) -> I.ctxPop (nonStrictExpN (I.Decl (D, Universal), U))
    | D, I.FgnExp _ ->
        raise (Error "Foreign expressions not permitted when checking freeness")

  and nonStrictSpineN = function
    | D, I.Nil -> D
    | D, I.App (U, S) -> nonStrictSpineN (nonStrictExpN (D, U), S)

  and nonStrictVarD = function
    | I.Decl (D, Existential (Free, name)), 1 ->
        I.Decl (D, Existential (Unknown, name))
    | D, 1 -> D
    | I.Decl (D, status), k -> I.Decl (nonStrictVarD (D, k - 1), status)
  (* ------------------------------------------- mode context update *)

  (* updateExpN (D, U, u) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Ground for_sml all existential variables k
            with a strict occurrence in U
            and D'(k) Unkown for_sml all existential variable k
            with a non-strict occurrence, but no strict occurrence in U
            (if !checkFree is true)

       u is the uniqueness property for_sml the new ground assumptions
    *)

  let rec updateExpN = function
    | D, I.Root (I.BVar k, S), u ->
        if isUniversal (I.ctxLookup (D, k)) then updateSpineN (D, S, u)
        else if isPattern (D, k, S) then updateVarD (D, k, u)
        else if !checkFree then nonStrictSpineN (nonStrictVarD (D, k), S)
        else D
    | D, I.Root (I.Const c, S), u -> updateSpineN (D, S, u)
    | D, I.Root (I.Def d, S), u -> updateSpineN (D, S, u)
    | D, I.Root (I.FgnConst (cs, conDec), S), u -> updateSpineN (D, S, u)
    | D, I.Lam (_, U), u -> I.ctxPop (updateExpN (I.Decl (D, Universal), U, u))
    | D, I.FgnExp _, u -> D

  and updateSpineN = function
    | D, I.Nil, u -> D
    | D, I.App (U, S), u -> updateSpineN (updateExpN (D, U, u), S, u)

  and updateVarD = function
    | I.Decl (D, Existential (_, name)), 1, u ->
        I.Decl (D, Existential (Ground u, name))
    | I.Decl (D, status), k, u -> I.Decl (updateVarD (D, k - 1, u), status)
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

  let rec updateAtom' = function
    | D, mode, I.Nil, M.Mnil, _ -> D
    | D, M.Plus, I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS), (p, occ) ->
        updateAtom' (updateExpN (D, U, Unique), M.Plus, S, mS, (p + 1, occ))
    | D, M.Minus, I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ) ->
        updateAtom' (updateExpN (D, U, Ambig), M.Minus, S, mS, (p + 1, occ))
    | D, M.Minus, I.App (U, S), M.Mapp (M.Marg (M.Minus1, _), mS), (p, occ) ->
        updateAtom' (updateExpN (D, U, Ambig), M.Minus, S, mS, (p + 1, occ))
    | D, M.Minus1, I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ) ->
        updateAtom' (updateExpN (D, U, Ambig), M.Minus1, S, mS, (p + 1, occ))
    | D, M.Minus1, I.App (U, S), M.Mapp (M.Marg (M.Minus1, _), mS), (p, occ) ->
        updateAtom' (updateExpN (D, U, Unique), M.Minus1, S, mS, (p + 1, occ))
    | D, mode, I.App (U, S), M.Mapp (_, mS), (p, occ) ->
        updateAtom' (D, mode, S, mS, (p + 1, occ))
  (* freeAtom (D, m, S, (V,s), mS, (p, occ)) = ()

       checks if all output arguments in S according to mS are free.
       Invariant: G |- S : V[s] >> P for_sml some G and P  (S in nf)
                  G ~ D
                  mode = (-) or (+); ( * ) or (-1) are excluded
    *)

  let rec freeAtom = function
    | D, mode, I.Nil, Vs, M.Mnil, _ -> ()
    | ( D,
        M.Minus,
        I.App (U, S),
        (I.Pi ((I.Dec (_, V1), _), V2), s),
        M.Mapp (M.Marg (M.Minus, _), mS),
        (p, occ) ) ->
        freeExpN
          ( D,
            0,
            M.Minus,
            U,
            P.arg (p, occ),
            fun q -> strictExpN (D, q, Whnf.normalize (V1, s)) );
        freeAtom
          ( D,
            M.Minus,
            S,
            Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)),
            mS,
            (p + 1, occ) )
    | D, mode, I.App (U, S), (I.Pi (_, V2), s), M.Mapp (_, mS), (p, occ) ->
        freeAtom
          ( D,
            mode,
            S,
            Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)),
            mS,
            (p + 1, occ) )
  (* updateAtom (D, m, S, a, mS, (p, occ))
       see updateAtom', and performs additional freeness check if required
    *)

  let rec updateAtom (D, mode, S, a, mS, (p, occ)) =
    let _ =
      if !checkFree then
        freeAtom (D, ambiguate mode, S, (I.constType a, I.id), mS, (p, occ))
      else ()
    in
    updateAtom' (D, mode, S, mS, (p, occ))
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

  let rec groundExpN = function
    | D, mode, I.Root (I.BVar k, S), occ ->
        andUnique
          ( groundVar (D, mode, k, P.head occ),
            groundSpineN (D, mode, S, (1, occ)) )
    | D, mode, I.Root (I.Const c, S), occ -> groundSpineN (D, mode, S, (1, occ))
    | D, mode, I.Root (I.Def d, S), occ -> groundSpineN (D, mode, S, (1, occ))
    | D, mode, I.Root (I.FgnConst (cs, conDec), S), occ ->
        groundSpineN (D, mode, S, (1, occ))
    | D, mode, I.Lam (_, U), occ ->
        groundExpN (I.Decl (D, Universal), mode, U, P.body occ)
    | D, mode, I.FgnExp csfe, occ ->
        I.FgnExpStd.fold csfe
          (fun (U, u) ->
            andUnique (groundExpN (D, mode, Whnf.normalize (U, I.id), occ), u))
          Unique

  and groundSpineN = function
    | D, mode, I.Nil, _ -> Unique
    | D, mode, I.App (U, S), (p, occ) ->
        andUnique
          ( groundExpN (D, mode, U, P.arg (p, occ)),
            groundSpineN (D, mode, S, (p + 1, occ)) )

  and groundVar = function
    | D, M.Minus1, k, occ -> (
        match I.ctxLookup (D, k) with
        | Existential (Ground Unique, _) -> Unique
        | Universal -> Unique
        | s ->
            raise
              (ModeError
                 ( occ,
                   "Occurrence of variable " ^ nameOf s ^ " in "
                   ^ M.modeToString M.Minus1
                   ^ " argument not necessarily unique" ))
        | s ->
            (* Existential (Free, _) or Existential (Unknown, _) *)
            raise
              (ModeError
                 ( occ,
                   "Occurrence of variable " ^ nameOf s ^ " in "
                   ^ M.modeToString M.Minus1
                   ^ " argument not necessarily ground" )))
    | D, mode, k, occ ->
        let status = I.ctxLookup (D, k) in
        if isGround status || isUniversal status then uniqueness status
        else
          raise
            (ModeError
               ( occ,
                 "Occurrence of variable " ^ nameOf status ^ " in "
                 ^ M.modeToString mode ^ " argument not necessarily ground" ))
  (* ------------------------------------------- groundness check by polarity *)

  (* groundAtom (D, m, S, mS, (p,occ))  = u

       If   G |- S : V > V'   ( S = U1 ; .. ; Un)
       and  D ~ G
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode = (+) or (-1)
       then groundAtom returns u if  D |- Ui ground
            for_sml all i s.t. mi = m (mod uniqueness)
            and checks that D |- Ui unique if mi = (-1) and m = (-)
       otherwise exception ModeError is raised

       u = Unique if all mi = m (mod uniqueness) are unique,
       u = Ambig otherwise

       ((p,occ) used in error messages)
    *)

  let rec groundAtom = function
    | D, _, I.Nil, M.Mnil, _ -> Unique
    | D, M.Plus, I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS), (p, occ) ->
        andUnique
          ( groundExpN (D, M.Plus, U, P.arg (p, occ)),
            groundAtom (D, M.Plus, S, mS, (p + 1, occ)) )
    | D, M.Minus, I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ) ->
        groundExpN (D, M.Minus, U, P.arg (p, occ));
        (* ignore uniqueness result here *)
        groundAtom (D, M.Minus, S, mS, (p + 1, occ))
    | D, M.Minus, I.App (U, S), M.Mapp (M.Marg (M.Minus1, _), mS), (p, occ) ->
        groundExpN (D, M.Minus1, U, P.arg (p, occ));
        (* ignore uniqueness result here *)
        groundAtom (D, M.Minus, S, mS, (p + 1, occ))
    | D, mode, I.App (U, S), M.Mapp (_, mS), (p, occ) ->
        groundAtom (D, mode, S, mS, (p + 1, occ))
  (* ------------------------------------------- mode checking first phase *)

  (* ctxPush (Ds, m) = Ds'
       raises the contexts Ds prepending m
    *)

  let rec ctxPush (m, Ds) = List.map (fun D -> I.Decl (D, m)) Ds
  (* ctxPop Ds = Ds'
       lowers the contexts Ds
    *)

  let rec ctxPop Ds = List.map (fun I.Decl (D, m) -> D) Ds
  (* checkD1 (D, V, occ, k) = ()

       Invariant:
         if G |- V : L
         and  V does not contain Skolem constants
         and  D ~ G
         then
            for_sml each  mode mS of the head of V
              exists  some Di s.t. all (-) evars of mS are ground
                where  D' ~ G, D' >= D is obtained by updating D
                  and  k D' = [D1, ..., Di, ..., Dn]
                  and  Di ~ G, Di >= D' is obtained by mode checking on the subgoals of V

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
    *)

  let rec checkD1 = function
    | D, I.Pi ((I.Dec (name, _), I.Maybe), V), occ, k ->
        checkD1
          ( I.Decl (D, Existential (Free, name)),
            V,
            P.body occ,
            fun (I.Decl (D', m)) -> ctxPush (m, k D') )
    | D, I.Pi ((I.Dec (name, V1), I.No), V2), occ, k ->
        checkD1
          ( I.Decl (D, Existential (Free, name)),
            V2,
            P.body occ,
            fun (I.Decl (D', m)) -> ctxPush (m, checkG1 (D', V1, P.label occ, k))
          )
    | D, I.Root (I.Const a, S), occ, k ->
        (* for_sml a declaration, all modes must be satisfied *)
        let rec checkAll = function
          | [] -> ()
          | mS :: mSs ->
              let rec checkSome = function
                | [ D' ] ->
                    groundAtom (D', M.Minus, S, mS, (1, occ));
                    (* ignore return *)
                    checkAll mSs
                | D' :: Ds ->
                    (try
                       groundAtom (D', M.Minus, S, mS, (1, occ));
                       () (* ignore return *)
                     with ModeError _ -> checkSome Ds);
                    checkAll mSs
              in
              checkSome (k (updateAtom (D, M.Plus, S, a, mS, (1, occ))))
        in
        checkAll (lookup (a, occ))
    | D, I.Root (I.Def d, S), occ, k ->
        (* for_sml a declaration, all modes must be satisfied *)
        let rec checkAll = function
          | [] -> ()
          | mS :: mSs ->
              let rec checkSome = function
                | [ D' ] ->
                    groundAtom (D', M.Minus, S, mS, (1, occ));
                    (* ignore return *)
                    checkAll mSs
                | D' :: Ds ->
                    (try
                       groundAtom (D', M.Minus, S, mS, (1, occ));
                       () (* ignore return *)
                     with ModeError _ -> checkSome Ds);
                    checkAll mSs
              in
              checkSome (k (updateAtom (D, M.Plus, S, d, mS, (1, occ))))
        in
        checkAll (lookup (d, occ))

  and checkG1 = function
    | D, I.Pi ((_, I.Maybe), V), occ, k ->
        ctxPop
          (checkG1
             ( I.Decl (D, Universal),
               V,
               P.body occ,
               fun (I.Decl (D', m)) -> ctxPush (m, k D') ))
    | D, I.Pi ((I.Dec (_, V1), I.No), V2), occ, k ->
        ctxPop
          (checkD1 (D, V1, P.label occ, fun D' -> [ D' ]);
           checkG1
             ( I.Decl (D, Universal),
               V2,
               P.body occ,
               fun (I.Decl (D', m)) -> ctxPush (m, k D') ))
    | D, I.Root (I.Const a, S), occ, k ->
        (* for_sml a goal, at least one mode must be satisfied *)
        let rec checkList = function
          | found, [] -> []
          | false, [ mS ] -> (
              match groundAtom (D, M.Plus, S, mS, (1, occ)) with
              | Unique -> k (updateAtom (D, M.Minus1, S, a, mS, (1, occ)))
              | Ambig -> k (updateAtom (D, M.Minus, S, a, mS, (1, occ))))
          | found, mS :: mSs ->
              (* found' is true iff D satisfies mS *)
              (* compute all other mode contexts *)
              let found' =
                try
                  groundAtom (D, M.Plus, S, mS, (1, occ));
                  true (* handler scope??? -fp *)
                with ModeError _ -> false
              in
              let Ds' = checkList (found || found') mSs in
              if found' then
                k (updateAtom (D, M.Minus, S, a, mS, (1, occ))) @ Ds'
              else Ds'
        in
        checkList false (lookup (a, occ))
    | D, I.Root (I.Def d, S), occ, k ->
        (* for_sml a goal, at least one mode must be satisfied *)
        let rec checkList = function
          | found, [] -> []
          | false, [ mS ] -> (
              match groundAtom (D, M.Plus, S, mS, (1, occ)) with
              | Unique -> k (updateAtom (D, M.Minus1, S, d, mS, (1, occ)))
              | Ambig -> k (updateAtom (D, M.Minus, S, d, mS, (1, occ))))
          | found, mS :: mSs ->
              (* found' is true iff D satisfies mS *)
              (* compute all other mode contexts *)
              let found' =
                try
                  groundAtom (D, M.Plus, S, mS, (1, occ));
                  true
                with ModeError _ -> false
              in
              let Ds' = checkList (found || found') mSs in
              if found' then
                k (updateAtom (D, M.Minus, S, d, mS, (1, occ))) @ Ds'
              else Ds'
        in
        checkList false (lookup (d, occ))
  (* checkDlocal (D, V, occ) = ()

       Invariant:
       If   G |- V : L
       and  D ~ G
       then checkD terminates with ()  iff V is mode correct.

       otherwise exception ModeError is raised (occ used in error messages)
    *)

  let rec checkDlocal (D, V, occ) =
    try checkD1 (D, V, occ, fun D' -> [ D' ])
    with ModeError (occ, msg) -> raise (Error' (occ, msg))
  (* --------------------------------------------------------- mode checking *)

  let rec cidFromHead = function I.Const a -> a | I.Def a -> a
  (* checkD (ConDec, occOpt)  = ()

       checkD terminates with () if ConDec is mode correct
       otherwise exception Error is raised

       (occOpt is used in error messages)
    *)

  let rec checkD (conDec, fileName, occOpt) =
    let _ = checkFree := false in
    let rec checkable = function
      | I.Root (Ha, _) -> (
          match ModeTable.mmodeLookup (cidFromHead Ha) with
          | [] -> false
          | _ -> true)
      | I.Uni _ -> false
      | I.Pi (_, V) -> checkable V
    in
    let V = I.conDecType conDec in
    if checkable V then
      try checkDlocal (I.Null, V, P.top)
      with Error' (occ, msg) -> (
        match occOpt with
        | None -> raise (Error msg)
        | Some occTree ->
            raise
              (Error (wrapMsg' (fileName, P.occToRegionClause occTree occ, msg))))
    else ()

  let rec checkAll = function
    | [] -> ()
    | I.Const c :: clist -> (
        if !Global.chatter > 3 then
          print (Names.qidToString (Names.constQid c) ^ " ")
        else ();
        try checkDlocal (I.Null, I.constType c, P.top)
        with Error' (occ, msg) ->
          raise (Error (wrapMsg (c, occ, msg)));
          checkAll clist)
    | I.Def d :: clist -> (
        if !Global.chatter > 3 then
          print (Names.qidToString (Names.constQid d) ^ " ")
        else ();
        try checkDlocal (I.Null, I.constType d, P.top)
        with Error' (occ, msg) ->
          raise (Error (wrapMsg (d, occ, msg)));
          checkAll clist)

  let rec checkMode (a, ms) =
    let _ =
      if !Global.chatter > 3 then
        print
          ("Mode checking family "
          ^ Names.qidToString (Names.constQid a)
          ^ ":\n")
      else ()
    in
    let clist = Index.lookup a in
    let _ = checkFree := false in
    let _ = checkAll clist in
    let _ = if !Global.chatter > 3 then print "\n" else () in
    ()

  let rec checkFreeOut (a, ms) =
    let _ =
      if !Global.chatter > 3 then
        print
          ("Checking output freeness of "
          ^ Names.qidToString (Names.constQid a)
          ^ ":\n")
      else ()
    in
    let clist = Index.lookup a in
    let _ = checkFree := true in
    let _ = checkAll clist in
    let _ = if !Global.chatter > 3 then print "\n" else () in
    ()

  let checkD = checkD
  let checkMode = checkMode
  let checkFreeOut = checkFreeOut
end

(* functor ModeCheck *)
