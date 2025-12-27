open Basis

(* Approximate language for_sml term reconstruction *)

(* Author: Kevin Watkins *)

module type APPROX = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  type uni = Level of int | Next of uni | LVar of uni option ref

  type exp =
    | Uni of uni
    | Arrow of exp * exp
    | Const of IntSyn.head
    | CVar of exp option ref
    | Undefined

  val type_ : uni
  val kind : uni
  val hyperkind : uni

  (* resets names of undetermined type/kind variables chosen for_sml printing *)
  val varReset : unit -> unit
  val newLVar : unit -> uni
  val newCVar : unit -> exp
  val whnfUni : uni -> uni
  val whnf : exp -> exp
  val uniToApx : IntSyn.uni -> uni
  val classToApx : IntSyn.exp -> exp * uni
  val exactToApx : IntSyn.exp * IntSyn.exp -> exp * exp * uni

  exception Ambiguous

  val apxToUni : uni -> IntSyn.uni
  val apxToClass : IntSyn.dctx * exp * uni * bool -> IntSyn.exp
  val apxToExact : IntSyn.dctx * exp * IntSyn.eclo * bool -> IntSyn.exp

  exception Unify of string

  val matchUni : uni * uni -> unit
  val match_ : exp * exp -> unit
  val makeGroundUni : uni -> bool
end
(* Approximate language for_sml term reconstruction *)

(* Author: Kevin Watkins *)

module Approx (Whnf : Whnf.WHNF) : APPROX = struct
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
     Equal.  We can define the approximate typing judgment
             
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

  let type_ = Level 1
  let kind = Level 2
  let hyperkind = Level 3
  let rec newLVar () = LVar (ref None)
  let rec newCVar () = CVar (ref None)
  (* whnfUni (l) = l'
       where l = l' and l' is in whnf *)

  let rec whnfUni = function
    | Next l -> (
        match whnfUni l with Level i -> Level (i + 1) | l' -> Next l')
    | LVar { contents = Some l } -> whnfUni l
    | l -> l
  (* whnf (u) = u'
       where u = u' and u' is in whnf *)

  let rec whnf = function CVar { contents = Some v } -> whnf v | v -> v
  (* just a little list since these are only for_sml printing errors *)

  type varEntry = (exp * exp * uni) * string

  let varList : varEntry list ref = ref []
  let rec varReset () = varList := []

  let rec varLookupRef r =
    List.find (fun ((CVar r', _, _), _) -> r = r') !varList

  let rec varLookupName name = List.find (fun _ name' -> name = name') !varList
  let rec varInsert ((u, v, l), name) = varList := ((u, v, l), name) :: !varList

  exception Ambiguous
  (* getReplacementName (u, v, l, allowed) = name
         if u : v : l
         and u is a CVar at type family or kind level *)

  let rec getReplacementName (u, v, l, allowed) =
    match u with
    | CVar r -> (
        match varLookupRef r with
        | Some (_, name) -> name
        | None ->
            (* others impossible by invariant *)
            let _ = if allowed then () else raise Ambiguous in
            let pref = match whnfUni l with Level 2 -> "A" | Level 3 -> "K" in
            let rec try_ i =
              let name = "%" ^ pref ^ Int.toString i ^ "%" in
              match varLookupName name with
              | None ->
                  varInsert ((u, v, l), name);
                  name
              | Some _ -> try_ (i + 1)
            in
            try_ 1)
    | _ -> raise Ambiguous
  (* findByReplacementName (name) = (u, v, l)
         if getReplacementName (u, v, l, allowed) = name was already called
         then u : v : l *)

  let rec findByReplacementName name =
    match varLookupName name with Some (uvl, _) -> uvl
  (* must be in list by invariant *)
  (* converting exact terms to approximate terms *)

  (* uniToApx (L) = L- *)

  let rec uniToApx = function I.Type -> Type | I.Kind -> Kind
  (* expToApx (U) = (U-, V-)
     if G |- U : V
     or G |- U ":" V = "hyperkind" *)

  let rec expToApx = function
    | I.Uni L ->
        let l' = uniToApx L in
        (Uni l', Uni (whnfUni (Next l')))
    | I.Pi ((I.Dec (_, V1), _), V2) ->
        let v1', _ (* type_ *) = expToApx V1 in
        let v2', l' = expToApx V2 in
        (Arrow (v1', v2'), l')
    | I.Root (I.FVar (name, _, _), _) ->
        let u, v, l = findByReplacementName name in
        (u, v)
    | I.Root (H (* Const/Def/NSDef *), _) -> (Const H, Uni type_)
    | I.Redex (u, _) -> expToApx u
    | I.Lam (_, u) -> expToApx u
    | I.EClo (u, _) -> expToApx u
  (* classToApx (V) = (V-, L-)
     if G |- V : L
     or G |- V ":" L = "hyperkind" *)

  let rec classToApx v =
    let v', l' = expToApx v in
    let (Uni l'') = whnf l' in
    (v', l'')
  (* exactToApx U V = (U-, V-)
     if G |- U : V *)

  let rec exactToApx u v =
    let v', l' = classToApx v in
    match whnfUni l' with
    | Level 1 (* type_ *) -> (Undefined, v', l')
    | _ (* kind/hyperkind *) ->
        let u', _ (* v' *) = expToApx u in
        (u', v', l')
  (* constDefApx (d) = V-
     if |- d = V : type *)

  let rec constDefApx d =
    match I.sgnLookup d with
    | I.ConDef (_, _, _, u, _, _, _) ->
        let v', _ (* Uni type_ *) = expToApx u in
        v'
    | I.AbbrevDef (_, _, _, u, _, _) ->
        let v', _ (* Uni type_ *) = expToApx u in
        v'
  (* converting approximate terms to exact terms *)

  (* apxToUni (L-) = L *)

  let rec apxToUniW = function Level 1 -> I.Type | Level 2 -> I.Kind
  (* others impossible by invariant *)

  let rec apxToUni l = apxToUniW (whnfUni l)
  (* apxToClass (G, v, L-, allowed) = V
     pre: L is ground and <= Hyperkind,
          and if L is Hyperkind then the target classifier
          of v is ground
          v : L-
     post: V is most general such that V- = v and G |- V : L *)

  let rec apxToClassW = function
    | g, Uni l, _ (* Next l *), allowed -> I.Uni (apxToUni l)
    | g, Arrow (v1, v2), l, allowed ->
        let v1' = apxToClass (g, v1, type_, allowed) in
        let d = I.Dec (None, v1') in
        let v2' = apxToClass (I.Decl (g, d), v2, l, allowed) in
        I.Pi ((d, I.Maybe), v2')
    | g, v, l (* type_ or kind *), allowed ->
        let name = getReplacementName (v, Uni l, Next l, allowed) in
        let s = I.Shift (I.ctxLength g) in
        I.Root (I.FVar (name, I.Uni (apxToUni l), s), I.Nil)
    | g, Const h, l (* type_ *), allowed ->
        I.Root (h, Whnf.newSpineVar (g, (I.conDecType (headConDec h), I.id)))

  and apxToClass (g, v, l, allowed) = apxToClassW (g, whnf v, l, allowed)
  (* apxToExact (G, u, (V, s), allowed) = U
     if u : V-
     and G' |- V : L and G |- s : G'
     then U- = u and G |- U : V[s] and U is the most general such *)

  let rec apxToExactW = function
    | g, u, (I.Pi ((d, _), v), s), allowed ->
        let d' = I.decSub (d, s) in
        I.Lam (d', apxToExact (I.Decl (g, d'), u, (v, I.dot1 s), allowed))
    | g, u, (I.Uni l, s), allowed -> apxToClass (g, u, uniToApx l, allowed)
    | g, u, (I.Root (I.FVar (name, _, _), _), s), allowed -> (
        let v, l, _ (* Next l *) = findByReplacementName name in
        let (Uni l) = whnf l in
        match whnfUni l with
        | Level 1 ->
            I.newEVar
              ( g,
                I.EClo
                  ( I.Root (I.FVar (name, I.Uni (apxToUni l), I.Shift 0), I.Nil),
                    s ) )
        | Level 2 ->
            (* u must be a CVar *)
            (* NOTE: v' differs from vs by a Shift *)
            (* probably could avoid the following call by removing the
                  substitutions in vs instead *)
            let name' = getReplacementName (whnf u, v, Level 2, allowed) in
            let v' = apxToClass (I.Null, v, Level 2, allowed) in
            let s' = I.Shift (I.ctxLength g) in
            I.Root (I.FVar (name', v', s'), I.Nil)
        | _ ->
            I.newEVar
              ( g,
                I.EClo
                  ( I.Root (I.FVar (name, I.Uni (apxToUni l), I.Shift 0), I.Nil),
                    s ) ))
    | g, u, vs (* an atomic type, not Def *), allowed -> I.newEVar (g, I.EClo vs)

  and apxToExact (g, u, vs, allowed) =
    apxToExactW (g, u, Whnf.whnfExpandDef vs, allowed)
  (* matching for_sml the approximate language *)

  exception Unify of string
  (* occurUni r l = ()
       iff r does not occur in l,
       otherwise raises Unify *)

  let rec occurUniW = function
    | r, Next l -> occurUniW (r, l)
    | r, LVar r' -> if r = r' then raise (Unify "Level circularity") else ()
    | r, _ -> ()

  let rec occurUni r l = occurUniW (r, whnfUni l)
  (* matchUni l1 l2 = ()
       iff l1<I> = l2<I> for_sml some most general instantiation I
       effect: applies I
       otherwise raises Unify *)

  let rec matchUniW = function
    | Level i1, Level i2 -> if i1 = i2 then () else raise (Unify "Level clash")
    | Level i1, Next l2 ->
        if i1 > 1 then matchUniW (Level (i1 - 1), l2)
        else raise (Unify "Level clash")
    | Next l1, Level i2 ->
        if i2 > 1 then matchUniW (l1, Level (i2 - 1))
        else raise (Unify "Level clash")
    | Next l1, Next l2 -> matchUniW (l1, l2)
    | LVar r1, LVar r2 -> if r1 = r2 then () else r1 := Some (LVar r2)
    | LVar r1, l2 ->
        occurUniW (r1, l2);
        r1 := Some l2
    | l1, LVar r2 ->
        occurUniW (r2, l1);
        r2 := Some l1

  let rec matchUni l1 l2 = matchUniW (whnfUni l1, whnfUni l2)
  (* occur (r, u) = ()
       iff r does not occur in u,
       otherwise raises Unify *)

  let rec occurW = function
    | r, Arrow (v1, v2) ->
        occur (r, v1);
        occur (r, v2)
    | r, CVar r' ->
        if r = r' then raise (Unify "Type/kind variable occurrence") else ()
    | r, _ -> ()

  and occur (r, u) = occurW (r, whnf u)
  (* match (u1, u2) = ()
       iff u1<I> = u2<I> : v for_sml some most general instantiation I
       effect: applies I
       otherwise raises Unify *)

  let rec matchW = function
    | Uni l1, Uni l2 -> matchUni l1 l2
    | Const h1, Const h2 -> (
        match (h1, h2) with
        | I.Const c1, I.Const c2 ->
            if c1 = c2 then () else raise (Unify "Type/kind constant clash")
        | I.Def d1, I.Def d2 ->
            if d1 = d2 then () else match_ (constDefApx d1, constDefApx d2)
        | I.Def d1, _ -> match_ (constDefApx d1, Const h2)
        | _, I.Def d2 ->
            match_ (Const h1, constDefApx d2)
            (* strictness is irrelevant to matching on approximate types *)
        | I.NSDef d1, I.NSDef d2 ->
            if d1 = d2 then () else match_ (constDefApx d1, constDefApx d2)
        | I.NSDef d1, _ -> match_ (constDefApx d1, Const h2)
        | _, I.NSDef d2 ->
            match_ (Const h1, constDefApx d2)
            (* others cannot occur by invariant *))
    | Arrow (v1, v2), Arrow (v3, v4) -> (
        try match_ (v1, v3)
        with e ->
          match_ (v2, v4);
          raise e;
          match_ (v2, v4))
    | v1, Const (I.Def d2) -> match_ (v1, constDefApx d2)
    | Const (I.Def d1), v2 -> match_ (constDefApx d1, v2)
    | v1, Const (I.NSDef d2) -> match_ (v1, constDefApx d2)
    | Const (I.NSDef d1), v2 -> match_ (constDefApx d1, v2)
    | CVar r1, u2 ->
        occurW (r1, u2);
        r1 := Some u2
    | u1, CVar r2 ->
        occurW (r2, u1);
        r2 := Some u1
    | _ -> raise (Unify "Type/kind expression clash")

  and match_ (u1, u2) = matchW (whnf u1, whnf u2)

  let rec matchable u1 u2 =
    try
      match_ (u1, u2);
      true
    with Unify _ -> false

  let rec makeGroundUni = function
    | Level _ -> false
    | Next l -> makeGroundUni l
    | LVar { contents = Some l } -> makeGroundUni l
    | LVar r ->
        r := Some (Level 1);
        true
end

(* structure Apx *)
