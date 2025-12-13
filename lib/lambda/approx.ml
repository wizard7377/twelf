(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)

functor (* GEN BEGIN FUNCTOR DECL *) Approx ((*! structure IntSyn' : INTSYN !*)
                structure Whnf : WHNF
		(*! sharing Whnf.IntSyn = IntSyn' !*)
		  )
  : APPROX =
struct

  (*! structure IntSyn = IntSyn' !*)
  structure I = IntSyn

  fun (* GEN BEGIN FUN FIRST *) headConDec (I.Const c) = I.sgnLookup c (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) headConDec (I.Skonst c) = I.sgnLookup c (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) headConDec (I.Def d) = I.sgnLookup d (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) headConDec (I.NSDef d) = I.sgnLookup d (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) headConDec (I.FgnConst (_, cd)) = cd (* GEN END FUN BRANCH *)
      (* others impossible by invariant *)

  (* The approximate language is based on the idea of erasure.  The
     erasure of a term is defined as follows:

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
                                                         
     This is a mutual recursion between the two judgments, just as for
     the standard LF type theory.

     There is also a typing judgment on approximate terms

       |- u : v

     defined in the obvious way.  If |- u : v : l then for any
     well-formed G there are most general U, V such that G |- U : V
     and U- = u and V- = v.  *)
                                        
  (* The approximate language *)

    datatype uni =
        Level of int (* 1 = type, 2 = kind, 3 = hyperkind, etc. *)
      | Next of uni
      | LVar of uni option ref
    
    datatype exp =
        Uni of uni
      | Arrow of exp * exp
      | Const of I.head (* Const/Def/NSDef *)
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

    (* GEN BEGIN TAG OUTSIDE LET *) val Type = Level 1 (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val Kind = Level 2 (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val Hyperkind = Level 3 (* GEN END TAG OUTSIDE LET *)

    fun newLVar () = LVar (ref NONE)
    fun newCVar () = CVar (ref NONE)

    (* whnfUni (l) = l'
       where l = l' and l' is in whnf *)
    fun (* GEN BEGIN FUN FIRST *) whnfUni (Next L) =
        (case whnfUni L
           of Level i => Level (i+1)
            | L' => Next L') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) whnfUni (LVar (ref (SOME L))) = whnfUni L (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) whnfUni L = L (* GEN END FUN BRANCH *)

    (* whnf (u) = u'
       where u = u' and u' is in whnf *)
    fun (* GEN BEGIN FUN FIRST *) whnf (CVar (ref (SOME V))) = whnf V (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) whnf V = V (* GEN END FUN BRANCH *)
                 
    local
      (* just a little list since these are only for printing errors *)
      type var_entry = (exp * exp * uni) * string
      (* GEN BEGIN TAG OUTSIDE LET *) val varList : var_entry list ref = ref nil (* GEN END TAG OUTSIDE LET *)
    in
      fun varReset () = (varList := nil)
      fun varLookupRef r = List.find ((* GEN BEGIN FUNCTION EXPRESSION *) fn ((CVar r', _, _), _) => r = r' (* GEN END FUNCTION EXPRESSION *)) (!varList)
      fun varLookupName name = List.find ((* GEN BEGIN FUNCTION EXPRESSION *) fn (_, name') => name = name' (* GEN END FUNCTION EXPRESSION *)) (!varList)
      fun varInsert ((U, V, L), name) = (varList := ((U, V, L), name)::(!varList))

      exception Ambiguous

      (* getReplacementName (u, v, l, allowed) = name
         if u : v : l
         and u is a CVar at type family or kind level *)
      fun getReplacementName (U as CVar r, V, L, allowed) =
          (case varLookupRef r
             of SOME (_, name) => name
              | NONE =>
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val _ = if allowed then () else raise Ambiguous (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val pref = case whnfUni L
                               of Level 2 => "A"
                                | Level 3 => "K" (* GEN END TAG OUTSIDE LET *)
                                  (* others impossible by invariant *)
                  fun try i =
                      let
                        (* GEN BEGIN TAG OUTSIDE LET *) val name = "%" ^ pref ^ Int.toString i ^ "%" (* GEN END TAG OUTSIDE LET *)
                      in
                        case varLookupName name
                          of NONE => (varInsert ((U, V, L), name); name)
                           | SOME _ => try (i+1)
                      end
                in
                  try 1
                end)

      (* findByReplacementName (name) = (u, v, l)
         if getReplacementName (u, v, l, allowed) = name was already called
         then u : v : l *)
      fun findByReplacementName name =
          (case varLookupName name
             of SOME (UVL, _) => UVL
                (* must be in list by invariant *))
    end

  (* converting exact terms to approximate terms *)

  (* uniToApx (L) = L- *)
  fun (* GEN BEGIN FUN FIRST *) uniToApx (I.Type) = Type (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) uniToApx (I.Kind) = Kind (* GEN END FUN BRANCH *)

  (* expToApx (U) = (U-, V-)
     if G |- U : V
     or G |- U ":" V = "hyperkind" *)
  fun (* GEN BEGIN FUN FIRST *) expToApx (I.Uni L) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val L' = uniToApx L (* GEN END TAG OUTSIDE LET *)
      in
        (Uni L', Uni (whnfUni (Next L')))
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) expToApx (I.Pi ((I.Dec (_, V1), _), V2)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (V1', _ (* Type *)) = expToApx (V1) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (V2', L') = expToApx (V2) (* GEN END TAG OUTSIDE LET *)
      in
        (Arrow (V1', V2'), L')
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) expToApx (I.Root (I.FVar (name, _, _), _)) =
      (* must have been created to represent a CVar *)
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (U, V, L) = findByReplacementName (name) (* GEN END TAG OUTSIDE LET *)
      in
        (U, V)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) expToApx (I.Root (H (* Const/Def/NSDef *), _)) =
        (* are we sure Skonst/FgnConst are never types or kinds? *)
        (Const H, Uni Type) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) expToApx (I.Redex (U, _)) = expToApx U (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) expToApx (I.Lam (_, U)) = expToApx U (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) expToApx (I.EClo (U, _)) = expToApx U (* GEN END FUN BRANCH *)

  (* classToApx (V) = (V-, L-)
     if G |- V : L
     or G |- V ":" L = "hyperkind" *)
  fun classToApx (V) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (V', L') = expToApx (V) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Uni L'' = whnf L' (* GEN END TAG OUTSIDE LET *)
      in
        (V', L'')
      end

  (* exactToApx (U, V) = (U-, V-)
     if G |- U : V *)
  fun exactToApx (U, V) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (V', L') = classToApx (V) (* GEN END TAG OUTSIDE LET *)
      in
        case whnfUni L'
          of Level 1 (* Type *) => (Undefined, V', L')
           | _ (* Kind/Hyperkind *) =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val (U', _ (* V' *)) = expToApx (U) (* GEN END TAG OUTSIDE LET *)
             in
               (U', V', L')
             end
      end

  (* constDefApx (d) = V-
     if |- d = V : type *)
  fun constDefApx d =
      (case I.sgnLookup d
         of I.ConDef (_, _, _, U, _, _, _) =>
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (V', _ (* Uni Type *)) = expToApx U (* GEN END TAG OUTSIDE LET *)
            in
              V'
            end
          | I.AbbrevDef (_, _, _, U, _, _) =>
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (V', _ (* Uni Type *)) = expToApx U (* GEN END TAG OUTSIDE LET *)
            in
              V'
            end)

  (* converting approximate terms to exact terms *)

  (* apxToUni (L-) = L *)
  fun (* GEN BEGIN FUN FIRST *) apxToUniW (Level 1) = I.Type (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) apxToUniW (Level 2) = I.Kind (* GEN END FUN BRANCH *)
      (* others impossible by invariant *)
  fun apxToUni L = apxToUniW (whnfUni L)

  (* apxToClass (G, v, L-, allowed) = V
     pre: L is ground and <= Hyperkind,
          and if L is Hyperkind then the target classifier
          of v is ground
          v : L-
     post: V is most general such that V- = v and G |- V : L *)
  fun (* GEN BEGIN FUN FIRST *) apxToClassW (G, Uni L, _ (* Next L *), allowed) =
        I.Uni (apxToUni L) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) apxToClassW (G, Arrow (V1, V2), L, allowed) =
      (* this is probably very bad -- it should be possible to infer
         more accurately which pis can be dependent *)
      (* also, does the name of the bound variable here matter? *)
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val V1' = apxToClass (G, V1, Type, allowed) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val D = I.Dec (NONE, V1') (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val V2' = apxToClass (I.Decl (G, D), V2, L, allowed) (* GEN END TAG OUTSIDE LET *)
      in
        I.Pi ((D, I.Maybe), V2')
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) apxToClassW (G, V as CVar r, L (* Type or Kind *), allowed) =
      (* convert undetermined CVars to FVars *)
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val name = getReplacementName (V, Uni L, Next L, allowed) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val s = I.Shift (I.ctxLength (G)) (* GEN END TAG OUTSIDE LET *)
      in
        I.Root (I.FVar (name, I.Uni (apxToUni L), s), I.Nil)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) apxToClassW (G, Const H, L (* Type *), allowed) =
        I.Root (H, Whnf.newSpineVar (G, (I.conDecType (headConDec H), I.id))) (* GEN END FUN BRANCH *)
      (* Undefined case impossible *)
  and apxToClass (G, V, L, allowed) = apxToClassW (G, whnf V, L, allowed)

  (* apxToExact (G, u, (V, s), allowed) = U
     if u : V-
     and G' |- V : L and G |- s : G'
     then U- = u and G |- U : V[s] and U is the most general such *)
  fun (* GEN BEGIN FUN FIRST *) apxToExactW (G, U, (I.Pi ((D, _), V), s), allowed) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.decSub (D, s) (* GEN END TAG OUTSIDE LET *)
      in
        I.Lam (D', apxToExact (I.Decl (G, D'), U, (V, I.dot1 s), allowed))
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) apxToExactW (G, U, (I.Uni L, s), allowed) =
        apxToClass (G, U, uniToApx L, allowed) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) apxToExactW (G, U, Vs as (I.Root (I.FVar (name, _, _), _), s), allowed) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (V, L, _ (* Next L *)) = findByReplacementName (name) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Uni L = whnf L (* GEN END TAG OUTSIDE LET *)
      in
        case whnfUni L
          of Level 1 => I.newEVar (G, I.EClo Vs)
           | Level 2 =>
             (* U must be a CVar *)
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val name' = getReplacementName (whnf U, V, Level 2, allowed) (* GEN END TAG OUTSIDE LET *)
               (* NOTE: V' differs from Vs by a Shift *)
               (* probably could avoid the following call by removing the
                  substitutions in Vs instead *)
               (* GEN BEGIN TAG OUTSIDE LET *) val V' = apxToClass (I.Null, V, Level 2, allowed) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val s' = I.Shift (I.ctxLength (G)) (* GEN END TAG OUTSIDE LET *)
             in
               I.Root (I.FVar (name', V', s'), I.Nil)
             end
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) apxToExactW (G, U, Vs (* an atomic type, not Def *), allowed) =
        I.newEVar (G, I.EClo Vs) (* GEN END FUN BRANCH *)
  and apxToExact (G, U, Vs, allowed) = apxToExactW (G, U, Whnf.whnfExpandDef Vs, allowed)

  (* matching for the approximate language *)

  exception Unify of string

    (* occurUni (r, l) = ()
       iff r does not occur in l,
       otherwise raises Unify *)
    fun (* GEN BEGIN FUN FIRST *) occurUniW (r, Next L) = occurUniW (r, L) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occurUniW (r, LVar r') =
          if r = r' then raise Unify "Level circularity"
          else () (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occurUniW (r, _) = () (* GEN END FUN BRANCH *)
    fun occurUni (r, L) = occurUniW (r, whnfUni L)

    (* matchUni (l1, l2) = ()
       iff l1<I> = l2<I> for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
    fun (* GEN BEGIN FUN FIRST *) matchUniW (Level i1, Level i2) =
          if i1 = i2 then () else raise Unify "Level clash" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) matchUniW (Level i1, Next L2) =
          if i1 > 1 then matchUniW (Level (i1-1), L2)
          else raise Unify "Level clash" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchUniW (Next L1, Level i2) =
          if i2 > 1 then matchUniW (L1, Level (i2-1))
          else raise Unify "Level clash" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchUniW (Next L1, Next L2) =
          matchUniW (L1, L2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchUniW (LVar r1, L2 as LVar r2) =
          if r1 = r2 then ()
          else r1 := SOME L2 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchUniW (LVar r1, L2) =
          (occurUniW (r1, L2);
           r1 := SOME L2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchUniW (L1, LVar r2) =
          (occurUniW (r2, L1);
           r2 := SOME L1) (* GEN END FUN BRANCH *)
    fun matchUni (L1, L2) = matchUniW (whnfUni L1, whnfUni L2)

    (* occur (r, u) = ()
       iff r does not occur in u,
       otherwise raises Unify *)
    fun (* GEN BEGIN FUN FIRST *) occurW (r, Arrow (V1, V2)) = (occur (r, V1); occur (r, V2)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occurW (r, CVar r') =
          if r = r' then raise Unify "Type/kind variable occurrence"
          else () (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occurW (r, _) = () (* GEN END FUN BRANCH *)
    and occur (r, U) = occurW (r, whnf U)

    (* match (u1, u2) = ()
       iff u1<I> = u2<I> : v for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
    fun (* GEN BEGIN FUN FIRST *) matchW (Uni L1, Uni L2) = matchUni (L1, L2) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) matchW (V1 as Const H1, V2 as Const H2) =
        (case (H1, H2)
           of (I.Const(c1), I.Const(c2)) =>
              if c1 = c2 then ()
              else raise Unify "Type/kind constant clash"
            | (I.Def(d1), I.Def(d2)) =>
              if d1 = d2 then ()
              else match (constDefApx d1, constDefApx d2)
            | (I.Def(d1), _) => match (constDefApx d1, V2)
            | (_, I.Def(d2)) => match (V1, constDefApx d2)
              (* strictness is irrelevant to matching on approximate types *)
            | (I.NSDef(d1), I.NSDef(d2)) =>
              if d1 = d2 then ()
              else match (constDefApx d1, constDefApx d2)
            | (I.NSDef(d1), _) => match (constDefApx d1, V2)
            | (_, I.NSDef(d2)) => match (V1, constDefApx d2)
              (* others cannot occur by invariant *)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchW (Arrow (V1, V2), Arrow (V3, V4)) =
          (match (V1, V3)
           handle e => (match (V2, V4); raise e);
           match (V2, V4)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchW (V1 as Arrow _, Const(I.Def(d2))) =
          match (V1, constDefApx d2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchW (Const(I.Def(d1)), V2 as Arrow _) =
          match (constDefApx d1, V2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchW (V1 as Arrow _, Const(I.NSDef(d2))) =
          match (V1, constDefApx d2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchW (Const(I.NSDef(d1)), V2 as Arrow _) =
          match (constDefApx d1, V2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchW (CVar r1, U2 as CVar r2) =
          if r1 = r2 then ()
          else r1 := SOME U2 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchW (CVar r1, U2) =
          (occurW (r1, U2);
           r1 := SOME U2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchW (U1, CVar r2) =
          (occurW (r2, U1);
           r2 := SOME U1) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchW _ = raise Unify "Type/kind expression clash" (* GEN END FUN BRANCH *)
    and match (U1, U2) = matchW (whnf U1, whnf U2)

    fun matchable (U1, U2) = (match (U1, U2); true)
                             handle Unify _ => false

    fun (* GEN BEGIN FUN FIRST *) makeGroundUni (Level _) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) makeGroundUni (Next L) = makeGroundUni L (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) makeGroundUni (LVar (ref (SOME L))) = makeGroundUni L (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) makeGroundUni (LVar (r as ref NONE)) = (r := SOME (Level 1);
                                                true) (* GEN END FUN BRANCH *)

end (* GEN END FUNCTOR DECL *) (* structure Apx *)
