open Basis ;; 
(* Style Checking *)

(* Author: Carsten Schuermann *)

module type STYLECHECK = sig
  exception Error of string

  val check : unit -> unit

  (* raises Error (msg) *)
  val checkConDec : IntSyn.cid -> unit
end

(* signature STYLECHECK *)
(* Style Checking *)

(* Author: Carsten Schuermann *)

module StyleCheck
    (Whnf : Whnf.WHNF)
    (Index : Index.INDEX)
    (Origins : Origins.ORIGINS) : STYLECHECK = struct
  exception Error of string

  module I = IntSyn
  module P = Paths

  type polarity = Plus | Minus
  (* indicates positivity *)

  type info = Correct | Incorrect of string list * string
  (* distinguishes style correct
                                           from - incorrect declarations *)

  let rec toggle = function Plus -> Minus | Minus -> Plus
  (* wrapMsg (c, occ, msg) err = s

       Invariant:
       Let c be a cid
       occ by an occurrence,
       msg an error message,
       and err a function that computes adequate region information for_sml c
       then s is msg wrapped with location information
    *)

  let rec wrapMsg (c, occ, msg) err =
    match Origins.originLookup c with
    | fileName, None -> fileName ^ ":" ^ msg
    | fileName, Some occDec ->
        P.wrapLoc'
          ( P.Loc (fileName, err occDec occ),
            Origins.linesInfoLookup fileName,
            msg )
  (* denumber L = L'

       Invariant:
       L' = L without digits
    *)

  let rec denumber = function
    | [] -> []
    | c :: l ->
        let x = ord c in
        let l' = denumber l in
        if (x >= 65 && x <= 90) || (x >= 97 && x <= 122) then c :: l' else l'

  let rec options = function n :: [] -> n | n :: l -> n ^ ", " ^ options l

  let rec error c (prefNames, n, occ) err =
    [
      wrapMsg
        ( c,
          occ,
          "Variable naming: expected " ^ options prefNames ^ " found " ^ n
          ^ "\n" )
        err;
    ]
  (* checkVariblename (n, prefNames) = I

       Invariant:
       If n occurs in prefNames then I = Correct otherwise Incorrect
    *)

  let rec checkVariablename (n, prefNames) =
    if
      List.exists
        (fun n' -> denumber (explode n) = denumber (explode n'))
        prefNames
    then Correct
    else Incorrect (prefNames, n)
  (* checkVar (D, pol) = I

       Invariant:
       If  D's name corresponds to the name choice for_sml pol,
       then I is Correct else Incorrect
    *)

  let rec checkVar = function
    | I.Dec (Some n, V), pol -> (
        match Names.getNamePref (I.targetFam V) with
        | None -> Correct
        | Some (prefENames, prefUNames) -> (
            match pol with
            | Plus -> checkVariablename (n, prefENames)
            | Minus -> checkVariablename (n, prefUNames)))
    | I.Dec (None, V), pol -> Correct
  (* implicitHead H = k

       Invariant:
       k = # implicit arguments associated with H
    *)

  let rec implicitHead = function
    | I.BVar k -> 0
    | I.Const c -> I.constImp c
    | I.Skonst k -> 0
    | I.Def d -> I.constImp d
    | I.NSDef d -> I.constImp d
    | I.FgnConst _ -> 0
  (* checkExp c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for_sml G
       and   G |- U : V
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  L is a list of strings (error messages) computed from U
    *)

  let rec checkExp = function
    | c, ((G, P), I.Uni _, occ), err -> []
    | c, ((G, P), I.Lam (D, U), occ), err ->
        checkDec c
          ((G, P), D, Minus, occ)
          err
          (fun ((G', P'), L') -> L' @ checkExp c ((G', P'), U, P.body occ) err)
    | c, ((G, P), I.Root (H, S), occ), err ->
        checkHead c ((G, P), H, P.head occ) err
        @ checkSpine c ((G, P), 1, implicitHead H, S, P.body occ) err
    | c, ((G, P), I.FgnExp (_, _), occ), err -> []

  and checkType = function
    | c, ((G, P), I.Uni _, pol, occ), err -> []
    | c, ((G, P), I.Pi ((D, I.Maybe), V), pol, occ), err ->
        checkDec c
          ((G, P), D, pol, occ)
          err
          (fun ((G', P'), L') ->
            L' @ checkType c ((G', P'), V, pol, P.body occ) err)
    | c, ((G, P), I.Pi ((D, I.No), V), pol, occ), err ->
        checkDec c
          ((G, P), D, pol, occ)
          err
          (fun ((G', P'), L') ->
            L' @ checkType c ((G', P'), V, pol, P.body occ) err)
    | c, ((G, P), I.Root (H, S), pol, occ), err ->
        checkHead c ((G, P), H, P.head occ) err
        @ checkSpine c ((G, P), 1, implicitHead H, S, P.body occ) err
    | c, ((G, P), I.FgnExp (_, _), pol, occ), err -> []

  and checkDecImp ((G, P), D, pol) k =
    let I = checkVar (D, pol) in
    k ((I.Decl (G, D), I.Decl (P, I)), [])

  and checkDec c ((G, P), D, pol, occ) err k =
    let I = checkVar (D, pol) in
    let E1 =
      match I with
      | Correct -> []
      | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err
    in
    let E2 = checkType c ((G, P), V, toggle pol, P.label occ) err in
    k ((I.Decl (G, D), I.Decl (P, I)), E1 @ E2)

  and checkHead = function
    | c, ((G, P), I.BVar k, occ), err -> (
        match I.ctxLookup (P, k) with
        | Correct -> []
        | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err)
    | c, ((G, P), I.Const _, occ), err -> []
    | c, ((G, P), I.Skonst k, occ), err -> []
    | c, ((G, P), I.Def d, occ), err -> []
    | c, ((G, P), I.NSDef d, occ), err -> []
    | c, ((G, P), I.FgnConst _, occ), err -> []

  and checkSpine = function
    | c, ((G, P), n, 0, I.Nil, occ), err -> []
    | c, ((G, P), n, 0, I.App (U, S), occ), err ->
        checkExp c ((G, P), U, P.arg (n, occ)) err
        @ checkSpine c ((G, P), n + 1, 0, S, occ) err
    | c, ((G, P), n, i, I.App (U, S), occ), err ->
        checkSpine c ((G, P), n + 1, i - 1, S, occ) err
  (* checkType' c ((G, P), n, V, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for_sml G
       and   n a decreasing number of implicit arguments
       and   G |- V : type
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from V
       (omitted arguments generate error message where they are used not declared)
    *)

  let rec checkType' = function
    | c, ((G, P), 0, V, occ), err -> checkType c ((G, P), V, Plus, occ) err
    | c, ((G, P), n, I.Pi ((D, I.Maybe), V), occ), err ->
        checkDecImp
          ((G, P), D, Plus)
          (fun ((G', P'), L') ->
            L' @ checkType' c ((G', P'), n - 1, V, P.body occ) err)
  (* checkExp' c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for_sml G
       and   G |- U : V for_sml some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from U
       (top level negative occurrences exception.  pos occurrences)
    *)

  let rec checkExp' = function
    | c, ((G, P), I.Lam (D, U), occ), err ->
        checkDec c
          ((G, P), D, Plus, occ)
          err
          (fun ((G', P'), L') -> L' @ checkExp' c ((G', P'), U, P.body occ) err)
    | c, ((G, P), U, occ), err -> checkExp c ((G, P), U, occ) err
  (* checkDef c ((G, P), n, U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for_sml G
       and   n a decreasing number of implicit arguments
       and   G |- U : V for_sml some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of strings (error messages) computed from U
       (top level negative occurrences exception.  pos occurrences)
    *)

  let rec checkDef = function
    | c, ((G, P), 0, U, occ), err -> checkExp' c ((G, P), U, occ) err
    | c, ((G, P), n, I.Lam (D, U), occ), err ->
        checkDecImp
          ((G, P), D, Plus)
          (fun ((G', P'), L') ->
            L' @ checkDef c ((G', P'), n - 1, U, P.body occ) err)
  (* checkConDec c C = L

       Invariant:
       Let   c be a cid
       and   . |- C : V for_sml some type V, constant declaration
       then  L is a list of  strings (error messages) computed from C
    *)

  let rec checkConDec = function
    | c, I.ConDec (_, _, implicit, _, U, _) ->
        if !Global.chatter > 3 then
          print (Names.qidToString (Names.constQid c) ^ " ")
        else ();
        checkType' c ((I.Null, I.Null), implicit, U, P.top) P.occToRegionDec
    | c, I.ConDef (_, _, implicit, U, V, I.Type, _) ->
        if !Global.chatter > 3 then
          print (Names.qidToString (Names.constQid c) ^ " ")
        else ();
        checkType' c ((I.Null, I.Null), implicit, V, P.top) P.occToRegionDef2
        @ checkDef c ((I.Null, I.Null), implicit, U, P.top) P.occToRegionDef1
    | c, I.AbbrevDef (_, _, implicit, U, V, I.Type) ->
        if !Global.chatter > 3 then
          print (Names.qidToString (Names.constQid c) ^ " ")
        else ();
        checkType' c ((I.Null, I.Null), implicit, V, P.top) P.occToRegionDef2;
        checkDef c ((I.Null, I.Null), implicit, U, P.top) P.occToRegionDef1
    | c, _ -> []
  (* in all other cases *)

  (* checkAll (c, n) = L

       Invariant:
       Let   c be a cid
       and   n the max. number of cids
       then  L is a list of  strings (error messages) computed from the signature c<=n
    *)

  let rec checkAll (c, n) =
    if c <= n then checkConDec c (I.sgnLookup c) @ checkAll (c + 1, n) else []
  (* checkAll () = L

       Invariant:
       L is a list of  strings (error messages) computed from the entire Twelf signature
    *)

  let rec check () =
    let n, _ = I.sgnSize () in
    map print (checkAll (0, n));
    ()

  let checkConDec =
   fun c ->
    map print (checkConDec c (I.sgnLookup c));
    ()

  let check = check
end
