(* Uniqueness Checking *)

(* Author: Frank Pfenning *)

module type UNIQUE = sig
  exception Error of string

  val checkUnique : IntSyn.cid * ModeSyn.modeSpine -> unit
  (* raises Error(msg) *)
end

(* signature UNIQUE *)
(* Uniqueness Checking *)

(* Author: Frank Pfenning *)

module Unique
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Unify : UNIFY)
    (Constraints : CONSTRAINTS)
    (UniqueTable : MODETABLE)
    (UniqueCheck : MODECHECK)
    (Index : INDEX)
    (Subordinate : SUBORDINATE)
    (WorldSyn : WORLDSYN)
    (Names : NAMES)
    (Print : PRINT)
    (TypeCheck : TYPECHECK)
    (Timers : TIMERS) : UNIQUE = struct
  exception Error of string

  module I = IntSyn
  module M = ModeSyn
  module W = WorldSyn
  module P = Paths
  module F = PrintFormatter
  module N = Names
  module T = Tomega

  let rec chatter chlev f =
    if !Global.chatter >= chlev then print (f ()) else ()

  let rec cName cid = N.qidToString (N.constQid cid)

  let rec pName = function
    | cid, Some x -> "#" ^ cName cid ^ "_" ^ x
    | cid, None -> "#" ^ cName cid ^ "_?"
  (*---------------------*)

  (* Auxiliary Functions *)

  (*---------------------*)

  (* instEVars (G, ({x1:V1}...{xn:Vn}a@S, id)) = (a @ S, s)
       where G |- s : {x1:V1}...{xn:Vn}
       substitutes new EVars for_sml x1,...,xn

       Invariants: {x1:V1}...{xn:Vn}a@S NF
    *)

  let rec instEVars = function
    | G, (I.Pi ((I.Dec (_, V1), _), V2), s) ->
        let X1 = I.newEVar (G, I.EClo (V1, s)) in
        instEVars (G, (V2, I.Dot (I.Exp X1, s)))
    | G, Vs -> Vs
  (* generalized from ../cover/cover.fun *)

  (* createEVarSub (G, G') = s

       Invariant:
       If   G |- G' ctx
       then G |- s : G' and s instantiates each x:A with an EVar G |- X : A
    *)

  let rec createEVarSub = function
    | G, I.Null -> I.Shift (I.ctxLength G)
    | G, I.Decl (G', D) ->
        let s = createEVarSub (G, G') in
        let V' = I.EClo (V, s) in
        let X = I.newEVar (G, V') in
        I.Dot (I.Exp X, s)
  (* unifiable (G, (U, s), (U', s')) = true
       iff G |- U[s] = U'[s'] : V  (for_sml some V)
       Effect: may instantiate EVars in all inputs
    *)

  let rec unifiable (G, (U, s), (U', s')) = Unify.unifiable (G, (U, s), (U', s'))
  (* unifiableSpines (G, (S, s), (S', s'), ms) = true
       iff G |- S[s] == S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)

  let rec unifiableSpines = function
    | G, (I.Nil, s), (I.Nil, s'), M.Mnil -> true
    | ( G,
        (I.App (U1, S2), s),
        (I.App (U1', S2'), s'),
        M.Mapp (M.Marg (M.Plus, _), ms2) ) ->
        unifiable (G, (U1, s), (U1', s'))
        && unifiableSpines (G, (S2, s), (S2', s'), ms2)
    | ( G,
        (I.App (U1, S2), s),
        (I.App (U1', S2'), s'),
        M.Mapp (M.Marg (mode, _), ms2) ) ->
        unifiableSpines (G, (S2, s), (S2', s'), ms2)
  (* unifiableRoots (G, (a @ S, s), (a' @ S', s'), ms) = true
       iff G |- a@S[s] == a'@S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)

  let rec unifiableRoots
      (G, (I.Root (I.Const a, S), s), (I.Root (I.Const a', S'), s'), ms) =
    a = a' && unifiableSpines (G, (S, s), (S', s'), ms)

  let rec checkNotUnifiableTypes (G, Vs, Vs', ms, (bx, by)) =
    chatter 6 (fun () -> "?- " ^ pName bx ^ " ~ " ^ pName by ^ "\n");
    CSManager.trail (fun () ->
        if unifiableRoots (G, Vs, Vs', ms) then
          raise (Error ("Blocks " ^ pName bx ^ " and " ^ pName by ^ " overlap"))
        else ())
  (*----------------------------*)

  (* Constant/Constant overlaps *)

  (*----------------------------*)

  (* checkNotUnifable (c, c', ms) = ()
       check if c:A overlaps with c':A' on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)

  let rec checkDiffConstConst (I.Const cid, I.Const cid', ms) =
    let _ =
      chatter 6 (fun () -> "?- " ^ cName cid ^ " ~ " ^ cName cid' ^ "\n")
    in
    let Vs = instEVars (I.Null, (I.constType cid, I.id)) in
    let Vs' = instEVars (I.Null, (I.constType cid', I.id)) in
    let _ =
      CSManager.trail (fun () ->
          if unifiableRoots (I.Null, Vs, Vs', ms) then
            raise
              (Error
                 ("Constants " ^ cName cid ^ " and " ^ cName cid' ^ " overlap\n"))
          else ())
    in
    ()
  (* checkUniqueConstConsts (c, cs, ms) = ()
       checks if c:A overlaps with any c':A' in cs on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)

  let rec checkUniqueConstConsts = function
    | c, [], ms -> ()
    | c, c' :: cs', ms ->
        checkDiffConstConst (c, c', ms);
        checkUniqueConstConsts (c, cs', ms)
  (* checkUniqueConsts (cs, ms) = ()
       checks if no two pairs of constant types in cs overlap on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)

  let rec checkUniqueConsts = function
    | [], ms -> ()
    | c :: cs, ms ->
        checkUniqueConstConsts (c, cs, ms);
        checkUniqueConsts (cs, ms)
  (*-----------------------------------------*)

  (* Block/Block and Block/Constant overlaps *)

  (*-----------------------------------------*)

  (* checkDiffBlocksInternal (G, (V, s), (t, piDecs), (a, ms), bx) = ()
       checks that V[s] does not overlap with any declaration in piDecs
       on input arguments ( + ) according to mode spine ms.
       bx = (b, xOpt) is the block identifier and parameter name in which V[s] occur
       Invariant: V[s] = a @ S and ms is mode spine for_sml a
    *)

  let rec checkDiffBlocksInternal = function
    | G, Vs, (t, []), (a, ms), bx -> ()
    | G, (V, s), (t, D :: piDecs), (a, ms), (b, xOpt) ->
        let a' = I.targetFam V' in
        let _ =
          if a = a' then
            checkNotUnifiableTypes
              (G, (V, s), instEVars (G, (V', t)), ms, ((b, xOpt), (b, yOpt)))
          else ()
        in
        checkDiffBlocksInternal
          ( I.Decl (G, D),
            (V, I.comp (s, I.shift)),
            (I.dot1 t, piDecs),
            (a, ms),
            (b, xOpt) )
  (* checkUniqueBlockInternal' (G, (t, piDecs), (a, ms), b) = ()
       checks that no two declarations for_sml family a in piDecs[t] overlap
       on input arguments ( + ) according to mode spine ms
       b is the block identifier and parameter name is which piDecs
       Effect: raises Error(msg) otherwise
    *)

  let rec checkUniqueBlockInternal' = function
    | G, (t, []), (a, ms), b -> ()
    | G, (t, D :: piDecs), (a, ms), b ->
        let a' = I.targetFam V in
        let _ =
          if a = a' then
            let V', s = instEVars (G, (V, t)) in
            checkDiffBlocksInternal
              ( I.Decl (G, D),
                (V', I.comp (s, I.shift)),
                (I.dot1 t, piDecs),
                (a, ms),
                (b, xOpt) )
          else ()
        in
        checkUniqueBlockInternal' (I.Decl (G, D), (I.dot1 t, piDecs), (a, ms), b)
  (* checkUniqueBlockInternal ((Gsome, piDecs), (a, ms))
       see checkUniqueBlockInternal'
    *)

  let rec checkUniqueBlockInternal ((Gsome, piDecs), (a, ms), b) =
    (* . |- t : Gsome *)
    let t = createEVarSub (I.Null, Gsome) in
    checkUniqueBlockInternal' (I.Null, (t, piDecs), (a, ms), b)
  (* checkUniqueBlockConstants (G, (V, s), cs, ms, bx) = ()
       checks that V[s] = a@S[s] does not overlap with any constant in cs
       according to mode spine ms for_sml family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       Effect: raises Error(msg) otherwise
    *)

  let rec checkUniqueBlockConsts = function
    | G, Vs, [], ms, bx -> ()
    | G, Vs, I.Const cid :: cs, ms, bx ->
        let _ =
          chatter 6 (fun () -> "?- " ^ pName bx ^ " ~ " ^ cName cid ^ "\n")
        in
        let Vs' = instEVars (G, (I.constType cid, I.id)) in
        let _ =
          CSManager.trail (fun () ->
              if unifiableRoots (G, Vs, Vs', ms) then
                raise
                  (Error
                     ("Block " ^ pName bx ^ " and constant " ^ cName cid
                    ^ " overlap"))
              else ())
        in
        checkUniqueBlockConsts (G, Vs, cs, ms, bx)
  (* checkUniqueBlockBlock (G, (V, s), (t, piDecs), (a, ms), (bx, b')) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for_sml a in piDecs[t] according to mode spine ms for_sml family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       b' is the block indentifier in which piDecs occurs
       Effect: raises Error(msg) otherwise
    *)

  let rec checkUniqueBlockBlock = function
    | G, Vs, (t, []), (a, ms), (bx, b') -> ()
    | G, (V, s), (t, D :: piDecs), (a, ms), (bx, b') ->
        let a' = I.targetFam V' in
        let _ =
          if a = a' then
            checkNotUnifiableTypes
              (G, (V, s), instEVars (G, (V', t)), ms, (bx, (b', yOpt)))
          else ()
        in
        checkUniqueBlockBlock
          ( I.Decl (G, D),
            (V, I.comp (s, I.shift)),
            (I.dot1 t, piDecs),
            (a, ms),
            (bx, b') )
  (* checkUniqueBlockBlocks (G, (V, s), bs, (a, ms), bx) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for_sml family a in any block in bs = [b1,...,bn] according to mode spine ms for_sml a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
    *)

  let rec checkUniqueBlockBlocks = function
    | G, Vs, [], (a, ms), bx -> ()
    | G, Vs, b :: bs, (a, ms), bx ->
        let Gsome, piDecs = I.constBlock b in
        let t = createEVarSub (G, Gsome) in
        let _ = checkUniqueBlockBlock (G, Vs, (t, piDecs), (a, ms), (bx, b)) in
        checkUniqueBlockBlocks (G, Vs, bs, (a, ms), bx)
  (* checkUniqueBlock' (G, (t, piDecs), bs, cs, (a, ms), b) = ()
       check that no declaration for_sml family a in piDecs[t]
       overlaps with any declaration for_sml a in bs or any constant in cs
       according to mode spine ms for_sml a
       b is the block identifier in which piDecs occur for_sml error messages
    *)

  let rec checkUniqueBlock' = function
    | G, (t, []), bs, cs, (a, ms), b -> ()
    | G, (t, D :: piDecs), bs, cs, (a, ms), b ->
        let a' = I.targetFam V in
        let _ =
          if a = a' then
            let V', s = instEVars (G, (V, t)) in
            let _ =
              checkUniqueBlockBlocks (G, (V', s), bs, (a, ms), (b, xOpt))
            in
            let _ = checkUniqueBlockConsts (G, (V', s), cs, ms, (b, xOpt)) in
            ()
          else ()
        in
        checkUniqueBlock' (I.Decl (G, D), (I.dot1 t, piDecs), bs, cs, (a, ms), b)
  (* checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) = ()
       see checkUniqueBlock'
    *)

  let rec checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) =
    let t = createEVarSub (I.Null, Gsome) in
    checkUniqueBlock' (I.Null, (t, piDecs), bs, cs, (a, ms), b)
  (* checkUniqueWorlds (bs, cs, (a, ms)) = ()
       checks if no declarations for_sml a in bs overlap with other declarations
       for_sml a in bs or any constant in cs according to mode spine ms
       Effect: raise Error(msg) otherwise
    *)

  let rec checkUniqueWorlds = function
    | [], cs, (a, ms) -> ()
    | b :: bs, cs, (a, ms) ->
        checkUniqueBlockInternal (I.constBlock b, (a, ms), b);
        checkUniqueBlock (I.constBlock b, b :: bs, cs, (a, ms), b);
        checkUniqueWorlds (bs, cs, (a, ms))
  (* checkNoDef (a) = ()
       Effect: raises Error if a is a defined type family
    *)

  let rec checkNoDef a =
    match I.sgnLookup a with
    | I.ConDef _ ->
        raise
          (Error
             ("Uniqueness checking " ^ cName a
            ^ ":\ntype family must not be defined."))
    | _ -> ()
  (* checkUnique (a, ms) = ()
       checks uniqueness of applicable cases with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)

  let rec checkUnique (a, ms) =
    (* lookup constants defining a *)
    let _ =
      chatter 4 (fun () -> "Uniqueness checking family " ^ cName a ^ "\n")
    in
    let _ = checkNoDef a in
    let _ =
      try Subordinate.checkNoDef a
      with Subordinate.Error msg ->
        raise (Error ("Coverage checking " ^ cName a ^ ":\n" ^ msg))
    in
    let cs = Index.lookup a in
    let (T.Worlds bs) =
      try W.lookup a (* worlds declarations for_sml a *)
      with W.Error msg ->
        raise
          (Error
             ("Uniqueness checking " ^ cName a
            ^ ":\nMissing world declaration for_sml " ^ cName a))
    in
    let _ =
      try checkUniqueConsts (cs, ms)
      with Error msg ->
        raise (Error ("Uniqueness checking " ^ cName a ^ ":\n" ^ msg))
    in
    let _ =
      try checkUniqueWorlds (bs, cs, (a, ms))
      with Error msg ->
        raise (Error ("Uniqueness checking " ^ cName a ^ ":\n" ^ msg))
    in
    let _ =
      chatter 5 (fun () ->
          "Checking uniqueness modes for_sml family " ^ cName a ^ "\n")
    in
    let _ =
      try UniqueCheck.checkMode (a, ms)
      with UniqueCheck.Error msg ->
        raise (Error ("Uniqueness mode checking " ^ cName a ^ ":\n" ^ msg))
    in
    ()
end

(* functor Unique *)
