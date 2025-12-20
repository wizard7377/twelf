(* Modes: short and full mode declarations *)


(* Author: Carsten Schuermann *)


(* Modified: Frank Pfenning *)


module ModeDec : MODEDEC = struct (*! structure ModeSyn = ModeSyn' !*)

(*! structure Paths = Paths' !*)

exception Error of string
module M = ModeSyn
module I = IntSyn
module P = Paths
type arg = Implicit | Explicit | Local
(* Representation invariant:

       The modes of parameters are represented in the following mode list

       M ::= . | M, <Marg, Arg>

       G corresponds to a context. We say M is a mode list for_sml U, if
       G |- U : V and M assigns modes to parameters in G
         (and similarly for_sml all other syntactic categories)

       The main function of this module is to
        (a) assign modes to implicit arguments in a type family
        (b) check the mode specification for_sml consistency

       Example:

         a : type.
         b : a -> a -> type.
         c : b X X -> b X Y -> type.

       Then

         %mode c +M -N.

       will infer X to be input and Y to be output

         %mode +{X:a} -{Y:a} +{M:b X Y} -{N:b X Y} (c M N).

       Generally, it is inconsistent
       for_sml an unspecified ( * ) or output (-) argument to occur
       in the type of an input (+) argument
    *)

let rec error (r, msg)  = raise (Error (P.wrap (r, msg)))
(* checkname mS = ()

       Invariant:
       mS modeSpine, all modes are named.
       If mS contains two entries with the same name
       then Error is raised
    *)

let rec checkName = function (M.Mnil) -> () | (M.Mapp (M.Marg (_, Some name), mS)) -> ( let rec checkName' = function (M.Mnil) -> () | (M.Mapp (M.Marg (_, Some name'), mS)) -> if name = name' then raise (Error ("Variable name clash: " ^ name ^ " is not unique")) else checkName' mS in  checkName' mS )
(* modeConsistent (m1, m2) = true
       iff it is consistent for_sml a variable x with mode m1
           to an index object in the type of a variable y:V(x) with mode m2

       m1\m2 + * - -1
        +    Y Y Y Y
        *    N y n n
        -    N y Y n
        -1   N Y Y Y

       The entries y,n constitute a bug fix, Wed Aug 20 11:50:27 2003 -fp
       The entry n specifies that the type
    *)

let rec modeConsistent = function (M.Star, M.Plus) -> false | (M.Star, M.Minus) -> false | (M.Star, M.Minus1) -> false | (M.Minus, M.Plus) -> false | (M.Minus, M.Minus1) -> false | (M.Minus1, M.Plus) -> false | _ -> true
(* empty (k, ms, V) = (ms', V')

       Invariant:
       If    V = {A_1} .. {A_n} V1   in Sigma
       and   V has k implicit arguments
       then  ms' = ms, <( *, NONE), Implicit>  ... <( *, NONE), Implicit>   (k times)
       and   V' = V1
    *)

let rec empty = function (0, ms, V) -> (ms, V) | (k, ms, I.Pi (_, V)) -> empty (k - 1, I.Decl (ms, (M.Marg (M.Star, None), Implicit)), V)
(* inferVar (ms, m, k) = ms'

       Invariant:
       If  ms is a mode list,
       and k is declared with mode mk in ms
       and m is the mode for_sml a variable y in whose type k occurs
       then ms' is the ms replacing only mk by
       mk' = m o mk

        m o mk  + * - -1
        ----------------
        +       + + + +
        *       + * - -1
        -       + - - -1
        -1      + -1-1-1

        Effect: if the mode mk for_sml k was explicitly declared and inconsistent
                with m o mk, an error is raised
    *)

let rec inferVar = function (I.Decl (ms, (M.Marg (M.Star, nameOpt), Implicit)), mode, 1) -> I.Decl (ms, (M.Marg (mode, nameOpt), Implicit)) | (I.Decl (ms, (M.Marg (_, nameOpt), Implicit)), M.Plus, 1) -> I.Decl (ms, (M.Marg (M.Plus, nameOpt), Implicit)) | (I.Decl (ms, (M.Marg (M.Minus, nameOpt), Implicit)), M.Minus1, 1) -> I.Decl (ms, (M.Marg (M.Minus1, nameOpt), Implicit)) | (ms, _, 1) -> ms | (ms, _, 1) -> ms | (ms, mode, 1) -> if modeConsistent (mode', mode) then ms else raise (Error ("Mode declaration for_sml " ^ name ^ " expected to be " ^ M.modeToString mode)) | (I.Decl (ms, md), mode, k) -> I.Decl (inferVar (ms, mode, k - 1), md)
(* inferExp (ms, m, U) = ms'

       Invariant:
       If  ms is a mode list for_sml U,   (U in nf)
       and m is a mode
       then ms' is the mode list consistently updated for_sml all parameters occurring in U,
         wrt. to m. (see inferVar)
    *)

let rec inferExp = function (ms, mode, I.Root (I.BVar (k), S)) -> inferSpine (inferVar (ms, mode, k), mode, S) | (ms, mode, I.Root (I.Const (cid), S)) -> inferSpine (ms, mode, S) | (ms, mode, I.Root (I.Def (cid), S)) -> inferSpine (ms, mode, S) | (ms, mode, I.Root (I.FgnConst (cs, conDec), S)) -> inferSpine (ms, mode, S) | (ms, mode, I.Lam (D, U)) -> I.ctxPop (inferExp (I.Decl (inferDec (ms, mode, D), (M.Marg (mode, nameOpt), Local)), mode, U)) | (ms, mode, I.Pi ((D, _), V)) -> I.ctxPop (inferExp (I.Decl (inferDec (ms, mode, D), (M.Marg (mode, nameOpt), Local)), mode, V)) | (ms, mode, I.FgnExp _) -> ms
and inferSpine = function (ms, mode, I.Nil) -> ms | (ms, mode, I.App (U, S)) -> inferSpine (inferExp (ms, mode, U), mode, S)
and inferDec (ms, mode, I.Dec (_, V))  = inferExp (ms, mode, V)
(* inferMode ((ms, V), mS) = ms'

       Invariant:
       If  ms is a mode list for_sml V,
       and mS is a mode spine,
       then ms' is the mode list for_sml V which is consistent with V.
    *)

let rec inferMode = function ((ms, I.Uni (I.Type)), M.Mnil) -> ms | ((_, I.Uni (I.Type)), _) -> raise (Error "Too many modes specified") | ((ms, I.Pi ((I.Dec (name, V1), _), V2)), M.Mapp (M.Marg (mode, _), mS)) -> I.ctxPop (inferMode ((I.Decl (inferExp (ms, mode, V1), (M.Marg (mode, name), Explicit)), V2), mS)) | ((ms, I.Root _), _) -> raise (Error "Expected type family, found object constant") | _ -> raise (Error "Not enough modes specified")
(* abstractMode (ms, mS) = mS'

       Invariant:
       If    V = {A1} .. {An} V1  is a type (with n implicit parameter)
       and   ms is a mode list for_sml V,
       then  mS' = {m1} .. {mn} mS
       where m1 .. mn are the infered modes for_sml the implicit parameters
    *)

let rec abstractMode (ms, mS)  = ( let rec abstractMode' = function (I.Null, mS, _) -> mS | (I.Decl (ms, (marg, _)), mS, k) -> abstractMode' (ms, M.Mapp (marg, mS), k + 1) in  abstractMode' (ms, mS, 1) )
(* shortToFull (cid, mS, r) = mS'

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is a mode spine in short form (implicit parameters are not moded),
       then mS' is a mode spine in full form (all parameters are moded)

       Full form can be different then intended by the user.
    *)

let rec shortToFull (a, mS, r)  = ( let rec calcImplicit' = function (I.ConDec (_, _, k, _, V, _)) -> abstractMode (inferMode (empty (k, I.Null, V), mS), mS) | (I.ConDef (_, _, k, _, V, _, _)) -> abstractMode (inferMode (empty (k, I.Null, V), mS), mS) in  try (checkName mS; calcImplicit' (I.sgnLookup a)) with Error (msg) -> error (r, msg)(* re-raise Error with location *)
 )
(* checkFull (a, mS, r) = ()

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is not a valid mode spine in full form then
       exception Error is raised.
    *)

let rec checkFull (a, mS, r)  = try (checkName mS; match I.sgnLookup a with I.ConDec (_, _, _, _, V, _) -> (inferMode ((I.Null, V), mS); ())(* defined type families separate types for_sml
                 purposes of mode checking (as the operational
                 semantics doesn't expand type definitions) *)
 | I.ConDef (_, _, _, _, V, _, _) -> (inferMode ((I.Null, V), mS); ())) with Error (msg) -> error (r, msg)
(* re-raise error with location *)

(* checkPure (a, mS, r) = ()
       Effect: raises Error(msg) if the modes in mS mention (-1)
    *)

let rec checkPure = function ((a, M.Mnil), r) -> () | ((a, M.Mapp (M.Marg (M.Minus1, _), mS)), r) -> error (r, "Uniqueness modes (-1) not permitted in `%mode' declarations (use `%unique')") | ((a, M.Mapp (_, mS)), r) -> checkPure ((a, mS), r)
let shortToFull = shortToFull
let checkFull = checkFull
let checkPure = checkPure
 end


(* functor ModeDec *)

