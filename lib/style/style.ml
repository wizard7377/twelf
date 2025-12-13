(* Style Checking *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) StyleCheck (structure Whnf : WHNF
                    structure Index : INDEX
                    structure Origins : ORIGINS)
  : STYLECHECK =
struct
  exception Error of string

  local
    structure I = IntSyn
    structure P = Paths

    datatype polarity = Plus | Minus    (* indicates positivity *)
    datatype info = Correct | Incorrect of string list * string
                                        (* distinguishes style correct
                                           from - incorrect declarations *)

    fun (* GEN BEGIN FUN FIRST *) toggle Plus = Minus (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) toggle Minus = Plus (* GEN END FUN BRANCH *)

    (* wrapMsg (c, occ, msg) err = s

       Invariant:
       Let c be a cid
       occ by an occurrence,
       msg an error message,
       and err a function that computes adequate region information for c
       then s is msg wrapped with location information
    *)
    fun wrapMsg (c, occ, msg) err =
        (case Origins.originLookup c
           of (fileName, NONE) => (fileName ^ ":" ^ msg)
            | (fileName, SOME occDec) =>
                (P.wrapLoc' (P.Loc (fileName, err occDec occ),
                             Origins.linesInfoLookup (fileName), msg)))

    (* denumber L = L'

       Invariant:
       L' = L without digits
    *)
    fun (* GEN BEGIN FUN FIRST *) denumber [] = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) denumber (c :: l) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val x = ord c (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val l' = denumber l (* GEN END TAG OUTSIDE LET *)
        in
          if (x >= 65 andalso x <= 90)
            orelse (x >= 97 andalso x <= 122) then c :: l' else l'
        end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) options (n :: nil) = n (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) options (n :: l) = n ^ ", " ^ (options l) (* GEN END FUN BRANCH *)


    fun error c (prefNames, n, occ) err =
         [wrapMsg (c, occ, "Variable naming: expected " ^ options prefNames ^ " found " ^ n ^ "\n") err]

    (* checkVariblename (n, prefNames) = I

       Invariant:
       If n occurs in prefNames then I = Correct otherwise Incorrect
    *)
    fun checkVariablename (n, prefNames) =
      if List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn n' => (denumber (explode n) = denumber (explode n')) (* GEN END FUNCTION EXPRESSION *)) prefNames then Correct
      else Incorrect (prefNames, n)

    (* checkVar (D, pol) = I

       Invariant:
       If  D's name corresponds to the name choice for pol,
       then I is Correct else Incorrect
    *)
    fun (* GEN BEGIN FUN FIRST *) checkVar (I.Dec (SOME n, V), pol) =
        (case (Names.getNamePref (I.targetFam V))
           of NONE => Correct
            | SOME (prefENames, prefUNames) =>
              (case pol
                 of Plus => checkVariablename (n, prefENames)
                  | Minus => checkVariablename (n, prefUNames))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkVar (I.Dec (NONE, V), pol) = Correct (* GEN END FUN BRANCH *)

    (* implicitHead H = k

       Invariant:
       k = # implicit arguments associated with H
    *)
    fun (* GEN BEGIN FUN FIRST *) implicitHead (I.BVar k) = 0 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) implicitHead (I.Const c) = I.constImp c (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) implicitHead (I.Skonst k) = 0 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) implicitHead (I.Def d) = I.constImp d (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) implicitHead (I.NSDef d) = I.constImp d (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) implicitHead (I.FgnConst _) = 0 (* GEN END FUN BRANCH *)


    (* checkExp c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- U : V
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  L is a list of strings (error messages) computed from U
    *)
    fun (* GEN BEGIN FUN FIRST *) checkExp c ((G, P), I.Uni _, occ) err = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkExp c ((G, P), I.Lam (D, U), occ) err =
        (checkDec c ((G, P), D, Minus, occ) err
         ((* GEN BEGIN FUNCTION EXPRESSION *) fn ((G', P'), L') => L' @ checkExp c ((G', P'), U, P.body occ) err (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkExp c ((G, P), I.Root (H, S), occ) err=
         checkHead c ((G, P), H, P.head occ) err @
        checkSpine c ((G, P), 1, implicitHead H, S, P.body occ) err (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkExp c ((G, P), I.FgnExp (_, _), occ) err = [] (* GEN END FUN BRANCH *)

    (* checkType c ((G, P), V, pol, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  V : type
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  L is a list of strings (error messages) computed from V
    *)
    and (* GEN BEGIN FUN FIRST *) checkType c ((G, P), I.Uni _, pol, occ) err = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkType c ((G, P), I.Pi ((D, I.Maybe), V), pol, occ) err =
        (checkDec c ((G, P), D, pol, occ) err
         ((* GEN BEGIN FUNCTION EXPRESSION *) fn ((G', P'), L') => L' @ checkType c ((G', P'), V, pol, P.body occ) err (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkType c ((G, P), I.Pi ((D, I.No), V), pol, occ) err =
        (checkDec c ((G, P), D,  pol, occ) err
         ((* GEN BEGIN FUNCTION EXPRESSION *) fn ((G', P'), L') => L' @ checkType c ((G', P'), V, pol, P.body occ) err (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkType c ((G, P), I.Root (H, S), pol, occ) err =
         checkHead c ((G, P), H, P.head occ) err @
        checkSpine c ((G, P), 1, implicitHead H, S, P.body occ) err (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkType c ((G, P), I.FgnExp (_, _), pol, occ) err = [] (* GEN END FUN BRANCH *)

    (* checkDecImp c ((G, P), D, pol) k = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  D declation
       and   k a continuation, that expects the extended context (G', P')
             and a list of already computed error messages L' as argument.
       then  L is a list of strings (error messages) computed D
       ( checkDecImp does not generate any error messages for D since omitted)
    *)
    and checkDecImp ((G, P), D as I.Dec (_, V), pol) k =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val I = checkVar (D, pol) (* GEN END TAG OUTSIDE LET *)
        in
          k ((I.Decl (G, D), I.Decl (P, I)), [])
        end

    (* checkDec c ((G, P), D, pol, occ) err k = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  D declation
       and   occ occurrence, err wrapper function
       and   k a continuation, that expects the extended context (G', P')
             and a list of already computed error messages L' as argument.
       then  L is a list of strings (error messages) computed from D
    *)
    and checkDec c ((G, P), D as I.Dec (_, V), pol, occ) err k =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val I = checkVar (D, pol) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val E1 = (case I
                     of Correct => []
                      | Incorrect (prefNames, n) => error c (prefNames, n, occ) err) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val E2 = checkType c ((G, P), V, toggle pol, P.label occ) err (* GEN END TAG OUTSIDE LET *)
        in
          k ((I.Decl (G, D), I.Decl (P, I)), E1 @ E2)
        end


    (* checkHead c ((G, P), H, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-  H head
       and   occ occurrence, err wrapper function
       then  L is a list of at most one string (error message) computed from H
    *)
    and (* GEN BEGIN FUN FIRST *) checkHead c ((G, P), I.BVar k, occ) err =
        (case I.ctxLookup (P, k)
           of Correct => []
            | Incorrect (prefNames, n) => error c (prefNames, n, occ) err) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkHead c ((G, P), I.Const _, occ) err = [] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkHead c ((G, P), I.Skonst k, occ) err = [] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkHead c ((G, P), I.Def d, occ) err = [] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkHead c ((G, P), I.NSDef d, occ) err = [] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkHead c ((G, P), I.FgnConst _, occ) err = [] (* GEN END FUN BRANCH *)


    (* checkSpine c ((G, P), S, n, i, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- S : V1 >> V2  for V1 V2, valid types
       and   n a running number of arguments considered
       and   i the number of remaining implicit arguments
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from S
    *)
    and (* GEN BEGIN FUN FIRST *) checkSpine c ((G, P), n, 0, I.Nil, occ) err = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkSpine c ((G, P), n, 0, I.App (U, S), occ) err =
         (checkExp c ((G, P), U, P.arg (n, occ)) err @
          checkSpine c ((G, P), n+1, 0, S, occ) err) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSpine c ((G, P), n, i, I.App (U, S), occ) err =
          checkSpine c ((G, P), n+1, i-1, S, occ) err (* GEN END FUN BRANCH *)

    (* checkType' c ((G, P), n, V, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   n a decreasing number of implicit arguments
       and   G |- V : type
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from V
       (omitted arguments generate error message where they are used not declared)
    *)
    fun (* GEN BEGIN FUN FIRST *) checkType' c ((G, P), 0, V, occ) err = checkType c ((G, P), V, Plus, occ) err (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkType' c ((G, P), n, I.Pi ((D, I.Maybe), V), occ) err =
         (checkDecImp ((G, P), D, Plus)
          ((* GEN BEGIN FUNCTION EXPRESSION *) fn ((G', P'), L') => L' @
          checkType' c ((G', P'), n-1, V, P.body occ) err (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)

    (* checkExp' c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- U : V for some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from U
       (top level negative occurrences exception.  Treated as pos occurrences)
    *)
    fun (* GEN BEGIN FUN FIRST *) checkExp' c ((G, P), I.Lam (D, U), occ) err =
         (checkDec c ((G, P), D, Plus, occ) err
          ((* GEN BEGIN FUNCTION EXPRESSION *) fn ((G', P'), L') => L' @
          checkExp' c ((G', P'), U, P.body occ) err (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkExp' c ((G, P), U, occ) err = checkExp c ((G, P), U, occ) err (* GEN END FUN BRANCH *)


    (* checkDef c ((G, P), n, U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   n a decreasing number of implicit arguments
       and   G |- U : V for some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of strings (error messages) computed from U
       (top level negative occurrences exception.  Treated as pos occurrences)
    *)
    fun (* GEN BEGIN FUN FIRST *) checkDef c ((G, P), 0, U,  occ) err = checkExp' c ((G, P), U, occ) err (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkDef c ((G, P), n, I.Lam (D, U),  occ) err =
         (checkDecImp ((G, P), D, Plus)
          ((* GEN BEGIN FUNCTION EXPRESSION *) fn ((G', P'), L') => L' @
           checkDef c ((G', P'), n-1, U, P.body occ) err (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)

    (* checkConDec c C = L

       Invariant:
       Let   c be a cid
       and   . |- C : V for some type V, constant declaration
       then  L is a list of  strings (error messages) computed from C
    *)
    fun (* GEN BEGIN FUN FIRST *) checkConDec c (I.ConDec (_, _, implicit, _, U, _)) =
        (if !Global.chatter > 3
           then print (Names.qidToString (Names.constQid c) ^ " ")
         else ();
           checkType' c ((I.Null, I.Null), implicit, U, P.top) P.occToRegionDec) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkConDec c (I.ConDef (_, _, implicit, U, V, I.Type, _)) =
           (if !Global.chatter > 3
              then print (Names.qidToString (Names.constQid c) ^ " ")
            else ();
           checkType' c ((I.Null, I.Null), implicit, V, P.top) P.occToRegionDef2 @
           checkDef c ((I.Null, I.Null), implicit, U, P.top) P.occToRegionDef1) (* GEN END FUN BRANCH *)
              (* type level definitions ? *)
      | (* GEN BEGIN FUN BRANCH *) checkConDec c (I.AbbrevDef (_, _, implicit, U, V, I.Type)) =
           (if !Global.chatter > 3
              then print (Names.qidToString (Names.constQid c) ^ " ")
            else ();
           checkType' c ((I.Null, I.Null), implicit, V, P.top) P.occToRegionDef2;
           checkDef c ((I.Null, I.Null), implicit, U, P.top) P.occToRegionDef1) (* GEN END FUN BRANCH *)
              (* type level abbreviations ? *)
      | (* GEN BEGIN FUN BRANCH *) checkConDec c _ = [] (* GEN END FUN BRANCH *)   (* in all other cases *)


    (* checkAll (c, n) = L

       Invariant:
       Let   c be a cid
       and   n the max. number of cids
       then  L is a list of  strings (error messages) computed from the signature c<=n
    *)
    fun checkAll (c, n) =
        (if c <= n then checkConDec c (I.sgnLookup c) @ checkAll (c+1, n) else [])

    (* checkAll () = L

       Invariant:
       L is a list of  strings (error messages) computed from the entire Twelf signature
    *)
    fun check () =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (n, _) = I.sgnSize () (* GEN END TAG OUTSIDE LET *)
      in (map print (checkAll (0, n)); ())
      end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val checkConDec = ((* GEN BEGIN FUNCTION EXPRESSION *) fn c => (map print (checkConDec c (I.sgnLookup c)); ()) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val check = check (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *)
