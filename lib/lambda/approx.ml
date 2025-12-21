(* Approximate language for_sml term reconstruction *)

(* Author: Kevin Watkins *)

module Approx (Whnf : WHNF) : APPROX = struct
  (*! structure IntSyn = IntSyn' !*)

  module I = IntSyn

  let rec headConDec = function
    | I.Const c -> I.sgnLookup c
    | I.Skonst c -> I.sgnLookup c
    | I.Def d -> I.sgnLookup d
    | I.NSDef d -> I.sgnLookup d
    | I.FgnConst (_, cd) -> cd
  (* others impossible by invariant *)

  (* The approximate language is based on the idea of erasure.  The
     erasure of a term is follows:

       c- = c
       d- = d
       type- = type
       kind- = kind
       ({x:A} B)- = A- -> B-
       ([x:A] M)- = M-    
       (M N)- = M-

       x- undefined
       X- undefined

     Note that erasure is always defined on well-typed terms at type
     family or kind level.  Also, if G |- U1 = U2 : V and U1,U2 are at
     type family or kind level, then U1- and U2- are defined and
     equal.  We can define the approximate typing judgment
             
       G |- U ~:~ V
                  
     by replacing appeals to equality in the usual presentation of the
     LF type theory with appeals to

       G |- U1 = U2 ~:~ V,

     which is defined to mean
           G |- U1 ~:~ V  and  G |- U2 ~:~ V  and  U1- = U2-
                                                         
     This is a mutual recursion between the two judgments, for_sml
     the standard LF type theory.

     There is also a typing judgment on approximate terms

       |- u : v

     defined in the obvious way.  If |- u : v : l then for_sml any
     well-formed G there are most general U, V such that G |- U : V
     and U- = u and V- = v.  *)

  (* The approximate language *)

  type uni = Level of int | Next of uni | LVar of uni option ref

  type exp =
    | Uni of uni
    | Arrow of exp * exp
    | Const of I.head
    | CVar of exp option ref
    | Undefined
  (* Because approximate type reconstruction uses the pattern G |- U
     ~:~ V ~:~ L and universe unification on L, if U is to be an
     arbitrary input expression, there must be an internal universe
     Hyperkind such that |- Type ~:~ Kind ~:~ Hyperkind.  The
     Hyperkind universe is used only during the approximate phase of
     reconstruction.  The invariants established by
     ReconTerm.filterLevel ensure that Hyperkind will never appear
     elsewhere. *)

  let Type = Level 1
  let Kind = Level 2
  let Hyperkind = Level 3
  let rec newLVar () = LVar (ref None)
  let rec newCVar () = CVar (ref None)
  (* whnfUni (l) = l'
       where l = l' and l' is in whnf *)

  let rec whnfUni = function
    | Next L -> (
        match whnfUni L with Level i -> Level (i + 1) | L' -> Next L')
    | LVar { contents = Some L } -> whnfUni L
    | L -> L
  (* whnf (u) = u'
       where u = u' and u' is in whnf *)

  let rec whnf = function CVar { contents = Some V } -> whnf V | V -> V
  (* just a little list since these are only for_sml printing errors *)

  type varEntry = (exp * exp * uni) * string

  let varList : varEntry list ref = ref []
  let rec varReset () = varList := []

  let rec varLookupRef r =
    List.find (fun ((CVar r', _, _), _) -> r = r') !varList

  let rec varLookupName name =
    List.find (fun (_, name') -> name = name') !varList

  let rec varInsert ((U, V, L), name) = varList := ((U, V, L), name) :: !varList

  exception Ambiguous
  (* getReplacementName (u, v, l, allowed) = name
         if u : v : l
         and u is a CVar at type family or kind level *)

  let rec getReplacementName (U, V, L, allowed) =
    match varLookupRef r with
    | Some (_, name) -> name
    | None ->
        (* others impossible by invariant *)
        let _ = if allowed then () else raise Ambiguous in
        let pref = match whnfUni L with Level 2 -> "A" | Level 3 -> "K" in
        let rec try_ i =
          let name = "%" ^ pref ^ Int.toString i ^ "%" in
          match varLookupName name with
          | None ->
              varInsert ((U, V, L), name);
              name
          | Some _ -> try_ (i + 1)
        in
        try_ 1
  (* findByReplacementName (name) = (u, v, l)
         if getReplacementName (u, v, l, allowed) = name was already called
         then u : v : l *)

  let rec findByReplacementName name =
    match varLookupName name with Some (UVL, _) -> UVL
  (* must be in list by invariant *)
  (* converting exact terms to approximate terms *)

  (* uniToApx (L) = L- *)

  let rec uniToApx = function I.Type -> Type | I.Kind -> Kind
  (* expToApx (U) = (U-, V-)
     if G |- U : V
     or G |- U ":" V = "hyperkind" *)

  let rec expToApx = function
    | I.Uni L ->
        let L' = uniToApx L in
        (Uni L', Uni (whnfUni (Next L')))
    | I.Pi ((I.Dec (_, V1), _), V2) ->
        let V1', _ (* Type *) = expToApx V1 in
        let V2', L' = expToApx V2 in
        (Arrow (V1', V2'), L')
    | I.Root (I.FVar (name, _, _), _) ->
        let U, V, L = findByReplacementName name in
        (U, V)
    | I.Root (H (* Const/Def/NSDef *), _) -> (Const H, Uni Type)
    | I.Redex (U, _) -> expToApx U
    | I.Lam (_, U) -> expToApx U
    | I.EClo (U, _) -> expToApx U
  (* classToApx (V) = (V-, L-)
     if G |- V : L
     or G |- V ":" L = "hyperkind" *)

  let rec classToApx V =
    let V', L' = expToApx V in
    let (Uni L'') = whnf L' in
    (V', L'')
  (* exactToApx (U, V) = (U-, V-)
     if G |- U : V *)

  let rec exactToApx (U, V) =
    let V', L' = classToApx V in
    match whnfUni L' with
    | Level 1 (* Type *) -> (Undefined, V', L')
    | _ (* Kind/Hyperkind *) ->
        let U', _ (* V' *) = expToApx U in
        (U', V', L')
  (* constDefApx (d) = V-
     if |- d = V : type *)

  let rec constDefApx d =
    match I.sgnLookup d with
    | I.ConDef (_, _, _, U, _, _, _) ->
        let V', _ (* Uni Type *) = expToApx U in
        V'
    | I.AbbrevDef (_, _, _, U, _, _) ->
        let V', _ (* Uni Type *) = expToApx U in
        V'
  (* converting approximate terms to exact terms *)

  (* apxToUni (L-) = L *)

  let rec apxToUniW = function Level 1 -> I.Type | Level 2 -> I.Kind
  (* others impossible by invariant *)

  let rec apxToUni L = apxToUniW (whnfUni L)
  (* apxToClass (G, v, L-, allowed) = V
     pre: L is ground and <= Hyperkind,
          and if L is Hyperkind then the target classifier
          of v is ground
          v : L-
     post: V is most general such that V- = v and G |- V : L *)

  let rec apxToClassW = function
    | G, Uni L, _ (* Next L *), allowed -> I.Uni (apxToUni L)
    | G, Arrow (V1, V2), L, allowed ->
        let V1' = apxToClass (G, V1, Type, allowed) in
        let D = I.Dec (None, V1') in
        let V2' = apxToClass (I.Decl (G, D), V2, L, allowed) in
        I.Pi ((D, I.Maybe), V2')
    | G, V, L (* Type or Kind *), allowed ->
        let name = getReplacementName (V, Uni L, Next L, allowed) in
        let s = I.Shift (I.ctxLength G) in
        I.Root (I.FVar (name, I.Uni (apxToUni L), s), I.Nil)
    | G, Const H, L (* Type *), allowed ->
        I.Root (H, Whnf.newSpineVar (G, (I.conDecType (headConDec H), I.id)))

  and apxToClass (G, V, L, allowed) = apxToClassW (G, whnf V, L, allowed)
  (* apxToExact (G, u, (V, s), allowed) = U
     if u : V-
     and G' |- V : L and G |- s : G'
     then U- = u and G |- U : V[s] and U is the most general such *)

  let rec apxToExactW = function
    | G, U, (I.Pi ((D, _), V), s), allowed ->
        let D' = I.decSub (D, s) in
        I.Lam (D', apxToExact (I.Decl (G, D'), U, (V, I.dot1 s), allowed))
    | G, U, (I.Uni L, s), allowed -> apxToClass (G, U, uniToApx L, allowed)
    | G, U, Vs, allowed -> (
        let V, L, _ (* Next L *) = findByReplacementName name in
        let (Uni L) = whnf L in
        match whnfUni L with
        | Level 1 -> I.newEVar (G, I.EClo Vs)
        | Level 2 ->
            (* U must be a CVar *)
            (* NOTE: V' differs from Vs by a Shift *)
            (* probably could avoid the following call by removing the
                  substitutions in Vs instead *)
            let name' = getReplacementName (whnf U, V, Level 2, allowed) in
            let V' = apxToClass (I.Null, V, Level 2, allowed) in
            let s' = I.Shift (I.ctxLength G) in
            I.Root (I.FVar (name', V', s'), I.Nil))
    | G, U, Vs (* an atomic type, not Def *), allowed -> I.newEVar (G, I.EClo Vs)

  and apxToExact (G, U, Vs, allowed) =
    apxToExactW (G, U, Whnf.whnfExpandDef Vs, allowed)
  (* matching for_sml the approximate language *)

  exception Unify of string
  (* occurUni (r, l) = ()
       iff r does not occur in l,
       otherwise raises Unify *)

  let rec occurUniW = function
    | r, Next L -> occurUniW (r, L)
    | r, LVar r' -> if r = r' then raise (Unify "Level circularity") else ()
    | r, _ -> ()

  let rec occurUni (r, L) = occurUniW (r, whnfUni L)
  (* matchUni (l1, l2) = ()
       iff l1<I> = l2<I> for_sml some most general instantiation I
       effect: applies I
       otherwise raises Unify *)

  let rec matchUniW = function
    | Level i1, Level i2 -> if i1 = i2 then () else raise (Unify "Level clash")
    | Level i1, Next L2 ->
        if i1 > 1 then matchUniW (Level (i1 - 1), L2)
        else raise (Unify "Level clash")
    | Next L1, Level i2 ->
        if i2 > 1 then matchUniW (L1, Level (i2 - 1))
        else raise (Unify "Level clash")
    | Next L1, Next L2 -> matchUniW (L1, L2)
    | LVar r1, L2 -> if r1 = r2 then () else r1 := Some L2
    | LVar r1, L2 ->
        occurUniW (r1, L2);
        r1 := Some L2
    | L1, LVar r2 ->
        occurUniW (r2, L1);
        r2 := Some L1

  let rec matchUni (L1, L2) = matchUniW (whnfUni L1, whnfUni L2)
  (* occur (r, u) = ()
       iff r does not occur in u,
       otherwise raises Unify *)

  let rec occurW = function
    | r, Arrow (V1, V2) ->
        occur (r, V1);
        occur (r, V2)
    | r, CVar r' ->
        if r = r' then raise (Unify "Type/kind variable occurrence") else ()
    | r, _ -> ()

  and occur (r, U) = occurW (r, whnf U)
  (* match (u1, u2) = ()
       iff u1<I> = u2<I> : v for_sml some most general instantiation I
       effect: applies I
       otherwise raises Unify *)

  let rec matchW = function
    | Uni L1, Uni L2 -> matchUni (L1, L2)
    | V1, V2 -> (
        match (H1, H2) with
        | I.Const c1, I.Const c2 ->
            if c1 = c2 then () else raise (Unify "Type/kind constant clash")
        | I.Def d1, I.Def d2 ->
            if d1 = d2 then () else match_ (constDefApx d1, constDefApx d2)
        | I.Def d1, _ -> match_ (constDefApx d1, V2)
        | _, I.Def d2 ->
            match_ (V1, constDefApx d2)
            (* strictness is irrelevant to matching on approximate types *)
        | I.NSDef d1, I.NSDef d2 ->
            if d1 = d2 then () else match_ (constDefApx d1, constDefApx d2)
        | I.NSDef d1, _ -> match_ (constDefApx d1, V2)
        | _, I.NSDef d2 ->
            match_ (V1, constDefApx d2) (* others cannot occur by invariant *))
    | Arrow (V1, V2), Arrow (V3, V4) -> (
        try match_ (V1, V3)
        with e ->
          match_ (V2, V4);
          raise e;
          match_ (V2, V4))
    | V1, Const (I.Def d2) -> match_ (V1, constDefApx d2)
    | Const (I.Def d1), V2 -> match_ (constDefApx d1, V2)
    | V1, Const (I.NSDef d2) -> match_ (V1, constDefApx d2)
    | Const (I.NSDef d1), V2 -> match_ (constDefApx d1, V2)
    | CVar r1, U2 -> if r1 = r2 then () else r1 := Some U2
    | CVar r1, U2 ->
        occurW (r1, U2);
        r1 := Some U2
    | U1, CVar r2 ->
        occurW (r2, U1);
        r2 := Some U1
    | _ -> raise (Unify "Type/kind expression clash")

  and match_ (U1, U2) = matchW (whnf U1, whnf U2)

  let rec matchable (U1, U2) =
    try
      match_ (U1, U2);
      true
    with Unify _ -> false

  let rec makeGroundUni = function
    | Level _ -> false
    | Next L -> makeGroundUni L
    | LVar { contents = Some L } -> makeGroundUni L
    | LVar r ->
        r := Some (Level 1);
        true
end

(* structure Apx *)
