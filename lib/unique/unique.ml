(* Uniqueness Checking *)
(* Author: Frank Pfenning *)

functor (* GEN BEGIN FUNCTOR DECL *) Unique
  (structure Global : GLOBAL
   structure Whnf : WHNF
   structure Abstract : ABSTRACT
   structure Unify : UNIFY              (* must be trailing! *)
   structure Constraints : CONSTRAINTS
   structure UniqueTable : MODETABLE
   structure UniqueCheck : MODECHECK
   structure Index : INDEX
   structure Subordinate : SUBORDINATE

   structure WorldSyn : WORLDSYN
   structure Names : NAMES
   structure Print : PRINT
   structure TypeCheck : TYPECHECK
   structure Timers : TIMERS)
  : UNIQUE =
struct

  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn
    structure W = WorldSyn
    structure P = Paths
    structure F = Print.Formatter
    structure N = Names
    structure T = Tomega

    fun chatter chlev f =
        if !Global.chatter >= chlev
          then print (f ())
        else ()

    fun cName (cid) = N.qidToString (N.constQid cid)

    fun (* GEN BEGIN FUN FIRST *) pName (cid, SOME(x)) = "#" ^ cName cid ^ "_" ^ x (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) pName (cid, NONE) = "#" ^ cName cid ^ "_?" (* GEN END FUN BRANCH *)

    (*---------------------*)
    (* Auxiliary Functions *)
    (*---------------------*)

    (* instEVars (G, ({x1:V1}...{xn:Vn}a@S, id)) = (a @ S, s)
       where G |- s : {x1:V1}...{xn:Vn}
       substitutes new EVars for x1,...,xn

       Invariants: {x1:V1}...{xn:Vn}a@S NF
    *)
    fun (* GEN BEGIN FUN FIRST *) instEVars (G, (I.Pi ((I.Dec (_, V1), _), V2), s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val X1 = I.newEVar (G, I.EClo (V1, s)) (* GEN END TAG OUTSIDE LET *)
        in
          instEVars (G, (V2, (I.Dot (I.Exp (X1), s))))
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) instEVars (G, Vs as (I.Root _, _)) = Vs (* GEN END FUN BRANCH *)

    (* generalized from ../cover/cover.fun *)
    (* createEVarSub (G, G') = s

       Invariant:
       If   G |- G' ctx
       then G |- s : G' and s instantiates each x:A with an EVar G |- X : A
    *)
    fun (* GEN BEGIN FUN FIRST *) createEVarSub (G, I.Null) = I.Shift (I.ctxLength G) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createEVarSub (G, I.Decl(G', D as I.Dec (_, V))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val s = createEVarSub (G, G') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = I.EClo (V, s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, V') (* GEN END TAG OUTSIDE LET *)
        in
          I.Dot (I.Exp X, s)
        end (* GEN END FUN BRANCH *)

    (* unifiable (G, (U, s), (U', s')) = true
       iff G |- U[s] = U'[s'] : V  (for some V)
       Effect: may instantiate EVars in all inputs
    *)
    fun unifiable (G, (U, s), (U', s')) =
        Unify.unifiable (G, (U, s), (U', s'))

    (* unifiableSpines (G, (S, s), (S', s'), ms) = true
       iff G |- S[s] == S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
    fun (* GEN BEGIN FUN FIRST *) unifiableSpines (G, (I.Nil, s), (I.Nil, s'), M.Mnil) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) unifiableSpines (G, (I.App (U1, S2), s), (I.App (U1', S2'), s'),
                         M.Mapp (M.Marg (M.Plus, _), ms2)) =
          unifiable (G, (U1, s), (U1', s'))
          andalso unifiableSpines (G, (S2, s), (S2', s'), ms2) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) unifiableSpines (G, (I.App (U1, S2), s), (I.App (U1', S2'), s'),
                         M.Mapp (M.Marg (mode, _), ms2)) =
        (* skip output ( - ) or ignore ( * ) arguments *)
          unifiableSpines (G, (S2, s), (S2', s'), ms2) (* GEN END FUN BRANCH *)

    (* unifiableRoots (G, (a @ S, s), (a' @ S', s'), ms) = true
       iff G |- a@S[s] == a'@S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
    fun unifiableRoots (G, (I.Root (I.Const (a), S), s),
                           (I.Root (I.Const (a'), S'), s'), ms) =
        (a = a') andalso unifiableSpines (G, (S, s), (S', s'), ms)

    fun checkNotUnifiableTypes (G, Vs, Vs', ms, (bx, by)) =
        ( chatter 6 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "?- " ^ pName bx ^ " ~ " ^ pName by ^ "\n" (* GEN END FUNCTION EXPRESSION *)) ;
          CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                           if unifiableRoots (G, Vs, Vs', ms)
                             then raise Error ("Blocks " ^ pName bx ^ " and "
                                               ^ pName by ^ " overlap")
                           else () (* GEN END FUNCTION EXPRESSION *)) )

    (*----------------------------*)
    (* Constant/Constant overlaps *)
    (*----------------------------*)

    (* checkNotUnifable (c, c', ms) = ()
       check if c:A overlaps with c':A' on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
    fun checkDiffConstConst (I.Const(cid), I.Const(cid'), ms) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 6 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "?- " ^ cName cid ^ " ~ " ^ cName cid' ^ "\n" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Vs = instEVars (I.Null, (I.constType cid, I.id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Vs' = instEVars (I.Null, (I.constType cid', I.id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                                   if unifiableRoots (I.Null, Vs, Vs', ms)
                                     then raise Error ("Constants " ^ cName cid ^ " and "
                                                       ^ cName cid' ^ " overlap\n")
                                   else () (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end

    (* checkUniqueConstConsts (c, cs, ms) = ()
       checks if c:A overlaps with any c':A' in cs on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
    fun (* GEN BEGIN FUN FIRST *) checkUniqueConstConsts (c, nil, ms) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkUniqueConstConsts (c, c'::cs', ms) =
        ( checkDiffConstConst (c, c', ms) ;
          checkUniqueConstConsts (c, cs', ms) ) (* GEN END FUN BRANCH *)

    (* checkUniqueConsts (cs, ms) = ()
       checks if no two pairs of constant types in cs overlap on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
    fun (* GEN BEGIN FUN FIRST *) checkUniqueConsts (nil, ms) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkUniqueConsts (c::cs, ms) =
        ( checkUniqueConstConsts (c, cs, ms);
          checkUniqueConsts (cs, ms) ) (* GEN END FUN BRANCH *)

    (*-----------------------------------------*)
    (* Block/Block and Block/Constant overlaps *)
    (*-----------------------------------------*)

    (* checkDiffBlocksInternal (G, (V, s), (t, piDecs), (a, ms), bx) = ()
       checks that V[s] does not overlap with any declaration in piDecs
       on input arguments ( + ) according to mode spine ms.
       bx = (b, xOpt) is the block identifier and parameter name in which V[s] occur
       Invariant: V[s] = a @ S and ms is mode spine for a
    *)
    fun (* GEN BEGIN FUN FIRST *) checkDiffBlocksInternal (G, Vs, (t, nil), (a, ms), bx) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkDiffBlocksInternal (G, (V, s), (t, (D as I.Dec(yOpt, V'))::piDecs), (a, ms), (b, xOpt)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val a' = I.targetFam V' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (a = a')
                    then checkNotUnifiableTypes (G, (V, s), instEVars (G, (V', t)), ms, ((b, xOpt), (b, yOpt)))
                  else () (* GEN END TAG OUTSIDE LET *)
        in
          checkDiffBlocksInternal (I.Decl (G, D), (V, I.comp (s, I.shift)),
                                   (I.dot1 t, piDecs),
                                   (a, ms),
                                   (b, xOpt))
        end (* GEN END FUN BRANCH *)

    (* checkUniqueBlockInternal' (G, (t, piDecs), (a, ms), b) = ()
       checks that no two declarations for family a in piDecs[t] overlap
       on input arguments ( + ) according to mode spine ms
       b is the block identifier and parameter name is which piDecs
       Effect: raises Error(msg) otherwise
    *)
    fun (* GEN BEGIN FUN FIRST *) checkUniqueBlockInternal' (G, (t, nil), (a, ms), b) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkUniqueBlockInternal' (G, (t, (D as I.Dec(xOpt, V))::piDecs), (a, ms), b) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val a' = I.targetFam V (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (a = a')
                    then let (* GEN BEGIN TAG OUTSIDE LET *) val (V', s) = instEVars (G, (V, t)) (* GEN END TAG OUTSIDE LET *)
                         in
                           checkDiffBlocksInternal (I.Decl (G, D), (V', I.comp (s, I.shift)),
                                                    (I.dot1 t, piDecs), (a, ms), (b, xOpt))
                         end
                  else () (* GEN END TAG OUTSIDE LET *)
        in
          checkUniqueBlockInternal' (I.Decl (G, D), (I.dot1 t, piDecs), (a, ms), b)
        end (* GEN END FUN BRANCH *)

    (* checkUniqueBlockInternal ((Gsome, piDecs), (a, ms))
       see checkUniqueBlockInternal'
    *)
    fun checkUniqueBlockInternal ((Gsome, piDecs), (a, ms), b) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createEVarSub (I.Null, Gsome) (* GEN END TAG OUTSIDE LET *)
          (* . |- t : Gsome *)
        in
           checkUniqueBlockInternal' (I.Null, (t, piDecs), (a, ms), b)
        end

    (* checkUniqueBlockConstants (G, (V, s), cs, ms, bx) = ()
       checks that V[s] = a@S[s] does not overlap with any constant in cs
       according to mode spine ms for family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       Effect: raises Error(msg) otherwise
    *)
    fun (* GEN BEGIN FUN FIRST *) checkUniqueBlockConsts (G, Vs, nil, ms, bx) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkUniqueBlockConsts (G, Vs, I.Const(cid)::cs, ms, bx) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 6 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "?- " ^ pName bx ^ " ~ " ^ cName cid ^ "\n" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Vs' = instEVars (G, (I.constType cid, I.id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                                   if unifiableRoots (G, Vs, Vs', ms)
                                     then raise Error ("Block " ^ pName bx ^ " and constant "
                                                       ^ cName cid ^ " overlap")
                                   else () (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          checkUniqueBlockConsts (G, Vs, cs, ms, bx)
        end (* GEN END FUN BRANCH *)

    (* checkUniqueBlockBlock (G, (V, s), (t, piDecs), (a, ms), (bx, b')) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for a in piDecs[t] according to mode spine ms for family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       b' is the block indentifier in which piDecs occurs
       Effect: raises Error(msg) otherwise
    *)
    fun (* GEN BEGIN FUN FIRST *) checkUniqueBlockBlock (G, Vs, (t, nil), (a, ms), (bx, b')) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkUniqueBlockBlock (G, (V, s), (t, (D as I.Dec(yOpt, V'))::piDecs), (a, ms), (bx, b')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val a' = I.targetFam V' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (a = a')
                    then checkNotUnifiableTypes (G, (V, s), instEVars (G, (V', t)), ms, (bx, (b', yOpt)))
                  else () (* GEN END TAG OUTSIDE LET *)
        in
          checkUniqueBlockBlock (I.Decl(G, D), (V, I.comp (s, I.shift)), (I.dot1 t, piDecs), (a, ms), (bx, b'))
        end (* GEN END FUN BRANCH *)

    (* checkUniqueBlockBlocks (G, (V, s), bs, (a, ms), bx) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for family a in any block in bs = [b1,...,bn] according to mode spine ms for a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
    *)
    fun (* GEN BEGIN FUN FIRST *) checkUniqueBlockBlocks (G, Vs, nil, (a, ms), bx) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkUniqueBlockBlocks (G, Vs, b::bs, (a, ms), bx) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Gsome, piDecs) = I.constBlock b (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createEVarSub (G, Gsome) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkUniqueBlockBlock (G, Vs, (t, piDecs), (a, ms), (bx, b)) (* GEN END TAG OUTSIDE LET *)
        in
          checkUniqueBlockBlocks (G, Vs, bs, (a, ms), bx)
        end (* GEN END FUN BRANCH *)

    (* checkUniqueBlock' (G, (t, piDecs), bs, cs, (a, ms), b) = ()
       check that no declaration for family a in piDecs[t]
       overlaps with any declaration for a in bs or any constant in cs
       according to mode spine ms for a
       b is the block identifier in which piDecs occur for error messages
    *)
    fun (* GEN BEGIN FUN FIRST *) checkUniqueBlock' (G, (t, nil), bs, cs, (a, ms), b) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkUniqueBlock' (G, (t, (D as I.Dec(xOpt, V))::piDecs), bs, cs, (a, ms), b) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val a' = I.targetFam V (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (a = a')
                    then let
                           (* GEN BEGIN TAG OUTSIDE LET *) val (V', s) = instEVars (G, (V, t)) (* GEN END TAG OUTSIDE LET *)
                           (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkUniqueBlockBlocks (G, (V', s), bs, (a, ms), (b, xOpt)) (* GEN END TAG OUTSIDE LET *)
                           (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkUniqueBlockConsts (G, (V', s), cs, ms, (b, xOpt)) (* GEN END TAG OUTSIDE LET *)
                         in
                           ()
                         end
                  else () (* GEN END TAG OUTSIDE LET *)
        in
          checkUniqueBlock' (I.Decl (G, D), (I.dot1 t, piDecs), bs, cs, (a, ms), b)
        end (* GEN END FUN BRANCH *)

    (* checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) = ()
       see checkUniqueBlock'
    *)
    fun checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createEVarSub (I.Null, Gsome) (* GEN END TAG OUTSIDE LET *)
        in
          checkUniqueBlock' (I.Null, (t, piDecs), bs, cs, (a, ms), b)
        end

    (* checkUniqueWorlds (bs, cs, (a, ms)) = ()
       checks if no declarations for a in bs overlap with other declarations
       for a in bs or any constant in cs according to mode spine ms
       Effect: raise Error(msg) otherwise
    *)
    fun (* GEN BEGIN FUN FIRST *) checkUniqueWorlds (nil, cs, (a, ms)) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkUniqueWorlds (b::bs, cs, (a, ms)) =
        ( checkUniqueBlockInternal (I.constBlock b, (a, ms), b) ;
          checkUniqueBlock (I.constBlock b, b::bs, cs, (a, ms), b) ;
          checkUniqueWorlds (bs, cs, (a, ms)) ) (* GEN END FUN BRANCH *)

  in
    (* checkNoDef (a) = ()
       Effect: raises Error if a is a defined type family
    *)
    fun checkNoDef (a) =
        (case I.sgnLookup a
           of I.ConDef _ =>
                raise Error ("Uniqueness checking " ^ cName a
                             ^ ":\ntype family must not be defined.")
            | _ => ())

    (* checkUnique (a, ms) = ()
       checks uniqueness of applicable cases with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
    fun checkUnique (a, ms) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 4 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "Uniqueness checking family " ^ cName a
                             ^ "\n" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkNoDef (a) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Subordinate.checkNoDef (a)
                  handle Subordinate.Error (msg) =>
                    raise Error ("Coverage checking " ^ cName a ^ ":\n"
                                 ^ msg) (* GEN END TAG OUTSIDE LET *)
    
    
          (* GEN BEGIN TAG OUTSIDE LET *) val cs = Index.lookup a (* GEN END TAG OUTSIDE LET *)       (* lookup constants defining a *)
          (* GEN BEGIN TAG OUTSIDE LET *) val T.Worlds (bs) = W.lookup a (* worlds declarations for a *)
                              handle W.Error (msg)
                              => raise Error ("Uniqueness checking " ^ cName a
                                              ^ ":\nMissing world declaration for "
                                              ^ cName a) (* GEN END TAG OUTSIDE LET *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkUniqueConsts (cs, ms)
                  handle Error (msg) => raise Error ("Uniqueness checking " ^ cName a ^ ":\n" ^ msg) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkUniqueWorlds (bs, cs, (a, ms))
                  handle Error (msg) => raise Error ("Uniqueness checking " ^ cName a ^ ":\n" ^ msg) (* GEN END TAG OUTSIDE LET *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 5 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "Checking uniqueness modes for family " ^ cName a ^ "\n" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = UniqueCheck.checkMode (a, ms)
                  handle UniqueCheck.Error (msg) =>
                         raise Error ("Uniqueness mode checking " ^ cName a ^ ":\n" ^ msg) (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end

  end
end (* GEN END FUNCTOR DECL *);  (* functor Unique *)
