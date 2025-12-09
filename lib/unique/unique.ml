(* Uniqueness Checking *)
(* Author: Frank Pfenning *)

module Unique
  (Global : GLOBAL)
   (Whnf : WHNF)
   (Abstract : ABSTRACT)
   (Unify : UNIFY              (* must be trailing! *))
   (Constraints : CONSTRAINTS)
   (UniqueTable : MODETABLE)
   (UniqueCheck : MODECHECK)
   (Index : INDEX)
   (Subordinate : SUBORDINATE)
   (WorldSyn : WORLDSYN)
   (Names : NAMES)
   (Print : PRINT)
   (TypeCheck : TYPECHECK)
   (Timers : TIMERS)
  : UNIQUE =
struct

  exception Error of string

  local
    module I = IntSyn
    module M = ModeSyn
    module W = WorldSyn
    module P = Paths
    module F = Print.Formatter
    module N = Names
    module T = Tomega

    let rec chatter chlev f =
        if !Global.chatter >= chlev
          then print (f ())
        else ()

    let rec cName (cid) = N.qidToString (N.constQid cid)

    let rec pName = function (cid, SOME(x)) -> "#" ^ cName cid ^ "_" ^ x
      | (cid, NONE) -> "#" ^ cName cid ^ "_?"

    (*---------------------*)
    (* Auxiliary Functions *)
    (*---------------------*)

    (* instEVars (G, ({x1:V1}...{xn:Vn}a@S, id)) = (a @ S, s)
       where G |- s : {x1:V1}...{xn:Vn}
       substitutes new EVars for x1,...,xn

       Invariants: {x1:V1}...{xn:Vn}a@S NF
    *)
    let rec instEVars = function (G, (I.Pi ((I.Dec (_, V1), _), V2), s)) -> 
        let
          let X1 = I.newEVar (G, I.EClo (V1, s))
        in
          instEVars (G, (V2, (I.Dot (I.Exp (X1), s))))
        end
      | (G, Vs as (I.Root _, _)) -> Vs

    (* generalized from ../cover/cover.fun *)
    (* createEVarSub (G, G') = s

       Invariant:
       If   G |- G' ctx
       then G |- s : G' and s instantiates each x:A with an EVar G |- X : A
    *)
    let rec createEVarSub = function (G, I.Null) -> I.Shift (I.ctxLength G)
      | (G, I.Decl(G', D as I.Dec (_, V))) -> 
        let
          let s = createEVarSub (G, G')
          let V' = I.EClo (V, s)
          let X = I.newEVar (G, V')
        in
          I.Dot (I.Exp X, s)
        end

    (* unifiable (G, (U, s), (U', s')) = true
       iff G |- U[s] = U'[s'] : V  (for some V)
       Effect: may instantiate EVars in all inputs
    *)
    let rec unifiable (G, (U, s), (U', s')) =
        Unify.unifiable (G, (U, s), (U', s'))

    (* unifiableSpines (G, (S, s), (S', s'), ms) = true
       iff G |- S[s] == S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
    let rec unifiableSpines = function (G, (I.Nil, s), (I.Nil, s'), M.Mnil) -> true
      | unifiableSpines (G, (I.App (U1, S2), s), (I.App (U1', S2'), s'),
                         M.Mapp (M.Marg (M.Plus, _), ms2)) =
          unifiable (G, (U1, s), (U1', s'))
          andalso unifiableSpines (G, (S2, s), (S2', s'), ms2)
      | unifiableSpines (G, (I.App (U1, S2), s), (I.App (U1', S2'), s'),
                         M.Mapp (M.Marg (mode, _), ms2)) =
        (* skip output ( - ) or ignore ( * ) arguments *)
          unifiableSpines (G, (S2, s), (S2', s'), ms2)

    (* unifiableRoots (G, (a @ S, s), (a' @ S', s'), ms) = true
       iff G |- a@S[s] == a'@S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
    fun unifiableRoots (G, (I.Root (I.Const (a), S), s),
                           (I.Root (I.Const (a'), S'), s'), ms) =
        (a = a') andalso unifiableSpines (G, (S, s), (S', s'), ms)

    let rec checkNotUnifiableTypes (G, Vs, Vs', ms, (bx, by)) =
        ( chatter 6 (fn () => "?- " ^ pName bx ^ " ~ " ^ pName by ^ "\n") ;
          CSManager.trail (fn () =>
                           if unifiableRoots (G, Vs, Vs', ms)
                             then raise Error ("Blocks " ^ pName bx ^ " and "
                                               ^ pName by ^ " overlap")
                           else ()) )

    (*----------------------------*)
    (* Constant/Constant overlaps *)
    (*----------------------------*)

    (* checkNotUnifable (c, c', ms) = ()
       check if c:A overlaps with c':A' on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
    let rec checkDiffConstConst (I.Const(cid), I.Const(cid'), ms) =
        let
          let _ = chatter 6 (fn () => "?- " ^ cName cid ^ " ~ " ^ cName cid' ^ "\n")
          let Vs = instEVars (I.Null, (I.constType cid, I.id))
          let Vs' = instEVars (I.Null, (I.constType cid', I.id))
          let _ = CSManager.trail (fn () =>
                                   if unifiableRoots (I.Null, Vs, Vs', ms)
                                     then raise Error ("Constants " ^ cName cid ^ " and "
                                                       ^ cName cid' ^ " overlap\n")
                                   else ())
        in
          ()
        end

    (* checkUniqueConstConsts (c, cs, ms) = ()
       checks if c:A overlaps with any c':A' in cs on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
    let rec checkUniqueConstConsts = function (c, nil, ms) -> ()
      | (c, c'::cs', ms) -> 
        ( checkDiffConstConst (c, c', ms) ;
          checkUniqueConstConsts (c, cs', ms) )

    (* checkUniqueConsts (cs, ms) = ()
       checks if no two pairs of constant types in cs overlap on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
    let rec checkUniqueConsts = function (nil, ms) -> ()
      | (c::cs, ms) -> 
        ( checkUniqueConstConsts (c, cs, ms);
          checkUniqueConsts (cs, ms) )

    (*-----------------------------------------*)
    (* Block/Block and Block/Constant overlaps *)
    (*-----------------------------------------*)

    (* checkDiffBlocksInternal (G, (V, s), (t, piDecs), (a, ms), bx) = ()
       checks that V[s] does not overlap with any declaration in piDecs
       on input arguments ( + ) according to mode spine ms.
       bx = (b, xOpt) is the block identifier and parameter name in which V[s] occur
       Invariant: V[s] = a @ S and ms is mode spine for a
    *)
    let rec checkDiffBlocksInternal = function (G, Vs, (t, nil), (a, ms), bx) -> ()
      | (G, (V, s), (t, (D as I.Dec(yOpt, V'))::piDecs), (a, ms), (b, xOpt)) -> 
        let
          let a' = I.targetFam V'
          let _ = if (a = a')
                    then checkNotUnifiableTypes (G, (V, s), instEVars (G, (V', t)), ms, ((b, xOpt), (b, yOpt)))
                  else ()
        in
          checkDiffBlocksInternal (I.Decl (G, D), (V, I.comp (s, I.shift)),
                                   (I.dot1 t, piDecs),
                                   (a, ms),
                                   (b, xOpt))
        end

    (* checkUniqueBlockInternal' (G, (t, piDecs), (a, ms), b) = ()
       checks that no two declarations for family a in piDecs[t] overlap
       on input arguments ( + ) according to mode spine ms
       b is the block identifier and parameter name is which piDecs
       Effect: raises Error(msg) otherwise
    *)
    let rec checkUniqueBlockInternal' = function (G, (t, nil), (a, ms), b) -> ()
      | (G, (t, (D as I.Dec(xOpt, V))::piDecs), (a, ms), b) -> 
        let
          let a' = I.targetFam V
          let _ = if (a = a')
                    then let let (V', s) = instEVars (G, (V, t))
                         in
                           checkDiffBlocksInternal (I.Decl (G, D), (V', I.comp (s, I.shift)),
                                                    (I.dot1 t, piDecs), (a, ms), (b, xOpt))
                         end
                  else ()
        in
          checkUniqueBlockInternal' (I.Decl (G, D), (I.dot1 t, piDecs), (a, ms), b)
        end

    (* checkUniqueBlockInternal ((Gsome, piDecs), (a, ms))
       see checkUniqueBlockInternal'
    *)
    let rec checkUniqueBlockInternal ((Gsome, piDecs), (a, ms), b) =
        let
          let t = createEVarSub (I.Null, Gsome)
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
    let rec checkUniqueBlockConsts = function (G, Vs, nil, ms, bx) -> ()
      | (G, Vs, I.Const(cid)::cs, ms, bx) -> 
        let
          let _ = chatter 6 (fn () => "?- " ^ pName bx ^ " ~ " ^ cName cid ^ "\n")
          let Vs' = instEVars (G, (I.constType cid, I.id))
          let _ = CSManager.trail (fn () =>
                                   if unifiableRoots (G, Vs, Vs', ms)
                                     then raise Error ("Block " ^ pName bx ^ " and constant "
                                                       ^ cName cid ^ " overlap")
                                   else ())
        in
          checkUniqueBlockConsts (G, Vs, cs, ms, bx)
        end

    (* checkUniqueBlockBlock (G, (V, s), (t, piDecs), (a, ms), (bx, b')) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for a in piDecs[t] according to mode spine ms for family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       b' is the block indentifier in which piDecs occurs
       Effect: raises Error(msg) otherwise
    *)
    let rec checkUniqueBlockBlock = function (G, Vs, (t, nil), (a, ms), (bx, b')) -> ()
      | (G, (V, s), (t, (D as I.Dec(yOpt, V'))::piDecs), (a, ms), (bx, b')) -> 
        let
          let a' = I.targetFam V'
          let _ = if (a = a')
                    then checkNotUnifiableTypes (G, (V, s), instEVars (G, (V', t)), ms, (bx, (b', yOpt)))
                  else ()
        in
          checkUniqueBlockBlock (I.Decl(G, D), (V, I.comp (s, I.shift)), (I.dot1 t, piDecs), (a, ms), (bx, b'))
        end

    (* checkUniqueBlockBlocks (G, (V, s), bs, (a, ms), bx) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for family a in any block in bs = [b1,...,bn] according to mode spine ms for a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
    *)
    let rec checkUniqueBlockBlocks = function (G, Vs, nil, (a, ms), bx) -> ()
      | (G, Vs, b::bs, (a, ms), bx) -> 
        let
          let (Gsome, piDecs) = I.constBlock b
          let t = createEVarSub (G, Gsome)
          let _ = checkUniqueBlockBlock (G, Vs, (t, piDecs), (a, ms), (bx, b))
        in
          checkUniqueBlockBlocks (G, Vs, bs, (a, ms), bx)
        end

    (* checkUniqueBlock' (G, (t, piDecs), bs, cs, (a, ms), b) = ()
       check that no declaration for family a in piDecs[t]
       overlaps with any declaration for a in bs or any constant in cs
       according to mode spine ms for a
       b is the block identifier in which piDecs occur for error messages
    *)
    let rec checkUniqueBlock' = function (G, (t, nil), bs, cs, (a, ms), b) -> ()
      | (G, (t, (D as I.Dec(xOpt, V))::piDecs), bs, cs, (a, ms), b) -> 
        let
          let a' = I.targetFam V
          let _ = if (a = a')
                    then let
                           let (V', s) = instEVars (G, (V, t))
                           let _ = checkUniqueBlockBlocks (G, (V', s), bs, (a, ms), (b, xOpt))
                           let _ = checkUniqueBlockConsts (G, (V', s), cs, ms, (b, xOpt))
                         in
                           ()
                         end
                  else ()
        in
          checkUniqueBlock' (I.Decl (G, D), (I.dot1 t, piDecs), bs, cs, (a, ms), b)
        end

    (* checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) = ()
       see checkUniqueBlock'
    *)
    let rec checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) =
        let
          let t = createEVarSub (I.Null, Gsome)
        in
          checkUniqueBlock' (I.Null, (t, piDecs), bs, cs, (a, ms), b)
        end

    (* checkUniqueWorlds (bs, cs, (a, ms)) = ()
       checks if no declarations for a in bs overlap with other declarations
       for a in bs or any constant in cs according to mode spine ms
       Effect: raise Error(msg) otherwise
    *)
    let rec checkUniqueWorlds = function (nil, cs, (a, ms)) -> ()
      | (b::bs, cs, (a, ms)) -> 
        ( checkUniqueBlockInternal (I.constBlock b, (a, ms), b) ;
          checkUniqueBlock (I.constBlock b, b::bs, cs, (a, ms), b) ;
          checkUniqueWorlds (bs, cs, (a, ms)) )

  in
    (* checkNoDef (a) = ()
       Effect: raises Error if a is a defined type family
    *)
    let rec checkNoDef (a) =
        (case I.sgnLookup a
           of I.ConDef _ =>
                raise Error ("Uniqueness checking " ^ cName a
                             ^ ":\ntype family must not be defined.")
            | _ => ())

    (* checkUnique (a, ms) = ()
       checks uniqueness of applicable cases with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
    let rec checkUnique (a, ms) =
        let
          let _ = chatter 4 (fn () => "Uniqueness checking family " ^ cName a
                             ^ "\n")
          let _ = checkNoDef (a)
          let _ = Subordinate.checkNoDef (a)
                  handle Subordinate.Error (msg) =>
                    raise Error ("Coverage checking " ^ cName a ^ ":\n"
                                 ^ msg)


          let cs = Index.lookup a       (* lookup constants defining a *)
          let T.Worlds (bs) = W.lookup a (* worlds declarations for a *)
                              handle W.Error (msg)
                              => raise Error ("Uniqueness checking " ^ cName a
                                              ^ ":\nMissing world declaration for "
                                              ^ cName a)

          let _ = checkUniqueConsts (cs, ms)
                  handle Error (msg) => raise Error ("Uniqueness checking " ^ cName a ^ ":\n" ^ msg)
          let _ = checkUniqueWorlds (bs, cs, (a, ms))
                  handle Error (msg) => raise Error ("Uniqueness checking " ^ cName a ^ ":\n" ^ msg)

          let _ = chatter 5 (fn () => "Checking uniqueness modes for family " ^ cName a ^ "\n")
          let _ = UniqueCheck.checkMode (a, ms)
                  handle UniqueCheck.Error (msg) =>
                         raise Error ("Uniqueness mode checking " ^ cName a ^ ":\n" ^ msg)
        in
          ()
        end

  end
end;; (* functor Unique *)
