(* Reconstruct queries *)


(* Author: Frank Pfenning *)


(* Modified: Roberto Virga, Jeff Polakow *)


module ReconQuery (Global : GLOBAL) (Names : NAMES) (Abstract : ABSTRACT) (ReconTerm' : RECON_TERM) (TypeCheck : TYPECHECK) (Strict : STRICT) (Timers : TIMERS) (Print : PRINT) : RECON_QUERY = struct (*! structure IntSyn = IntSyn' !*)

(*! structure Paths = Paths' !*)

module ExtSyn = ReconTerm'
module T = ReconTerm'
exception Error of string
(* error (r, msg) raises a syntax error within region r with text msg *)

let rec error (r, msg)  = raise (Error (Paths.wrap (r, msg)))
type name = string
(* Queries, with optional proof term variable *)

type query = Query of name option * T.term
(* define := <constant name> option * <def body> * <type> option *)

type define = Define of string option * T.term * T.term option
type solve = solve of string option * T.term * Paths.region
(* freeVar (XOpt, [(X1,"X1"),...,(Xn,"Xn")]) = true
     iff XOpt = SOME("Xi"), false otherwise
  *)

let rec freeVar = function (Some (name), Xs) -> List.exists (fun (_, name') -> name = name') Xs | _ -> false
(* queryToQuery (q) = (V, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)

(* call TypeCheck... if !doubleCheck = true? *)

(* Wed May 20 08:00:28 1998 -fp *)

let rec queryToQuery (Query (optName, tm), Paths.Loc (fileName, r))  = ( (* construct an external term for_sml the result of the query
        val res = (case optName
                     of NONE => T.omitted (r)
                      | SOME name => T.evar (name, r)) *)
(* ??? Since the reconstruction of a query is subject to constraints,
           couldn't optName "occur" in a constraint involving the type
           without being detected by this test?  -kw *)
let _ = Names.varReset IntSyn.Null in let _ = T.resetErrors fileName in let T.JClass ((V, oc), L) = (Timers.time Timers.recon T.reconQuery) (T.jclass tm) in let _ = T.checkErrors (r) in let _ = (match L with IntSyn.Type -> () | _ -> error (r, "Query was not a type")) in let Xs = Names.namedEVars () in let _ = if freeVar (optName, Xs) then error (r, "Proof term variable " ^ valOf optName ^ " occurs in type") else () in  (V, optName, Xs) )
let rec finishDefine (Define (optName, tm, clsOpt), ((U, oc1), (V, oc2Opt), L))  = ( (* is this necessary? -kw *)
let (i, (U', V')) = try (Timers.time Timers.abstract Abstract.abstractDef) (U, V) with Abstract.Error (msg) -> raise (Abstract.Error (Paths.wrap (Paths.toRegion oc1, msg))) in let name = match optName with None -> "_" | Some (name) -> name in let ocd = Paths.def (i, oc1, oc2Opt) in let cd = (try (Strict.check ((U', V'), Some (ocd)); IntSyn.ConDef (name, None, i, U', V', L, IntSyn.ancestor U')) with Strict.Error _ -> IntSyn.AbbrevDef (name, None, i, U', V', L)) in let cd = Names.nameConDec cd in let _ = if ! Global.chatter >= 3 then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n") else () in let _ = if ! Global.doubleCheck then ((Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni L); (Timers.time Timers.checking TypeCheck.check) (U', V')) else () in let conDecOpt = match optName with None -> None | Some _ -> Some (cd) in  (conDecOpt, Some (ocd)) )
let rec finishSolve (solve (nameOpt, tm, r), U, V)  = ( (* is this necessary? -kw *)
let (i, (U', V')) = try (Timers.time Timers.abstract Abstract.abstractDef) (U, V) with Abstract.Error (msg) -> raise (Abstract.Error (Paths.wrap (r, msg))) in let name = match nameOpt with None -> "_" | Some (name) -> name in let cd = (try (Strict.check ((U', V'), None); IntSyn.ConDef (name, None, i, U', V', IntSyn.Type, IntSyn.ancestor U')) with Strict.Error _ -> IntSyn.AbbrevDef (name, None, i, U', V', IntSyn.Type)) in let cd = Names.nameConDec cd in let _ = if ! Global.chatter >= 3 then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n") else () in let _ = if ! Global.doubleCheck then ((Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni IntSyn.Type); (Timers.time Timers.checking TypeCheck.check) (U', V')) else () in let conDecOpt = match nameOpt with None -> None | Some _ -> Some (cd) in  conDecOpt )
(* queryToQuery (q) = (V, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)

(* call TypeCheck... if !doubleCheck = true? *)

(* Wed May 20 08:00:28 1998 -fp *)

let rec solveToSolve (defines, sol, Paths.Loc (fileName, r))  = ( (* val Xs = Names.namedEVars () *)
let _ = Names.varReset IntSyn.Null in let _ = T.resetErrors fileName in let rec mkd = function (Define (_, tm1, None)) -> T.jterm tm1 | (Define (_, tm1, Some (tm2))) -> T.jof (tm1, tm2) in let rec mkj = function ([]) -> T.jnothing | (def :: defs) -> T.jand (mkd def, mkj defs) in let T.JAnd (defines', T.JClass ((V, _), L)) = (Timers.time Timers.recon T.reconQuery) (T.jand (mkj defines, T.jclass tm)) in let _ = T.checkErrors (r) in let _ = (match L with IntSyn.Type -> () | _ -> error (r0, "Query was not a type")) in let rec sc = function (M, [], _) -> (match finishSolve (sol, M, V) with None -> [] | Some condec -> [(condec, None)]) | (M, def :: defs, T.JAnd (T.JTerm ((U, oc1), V, L), f)) -> (match finishDefine (def, ((U, oc1), (V, None), L)) with (None, _) -> sc (M, defs, f) | (Some condec, ocdOpt) -> (condec, ocdOpt) :: sc (M, defs, f)) | (M, def :: defs, T.JAnd (T.JOf ((U, oc1), (V, oc2), L), f)) -> (match finishDefine (def, ((U, oc1), (V, Some oc2), L)) with (None, _) -> sc (M, defs, f) | (Some condec, ocdOpt) -> (condec, ocdOpt) :: sc (M, defs, f)) in  (V, fun M -> sc (M, defines, defines')) )
 end

(* functor ReconQuery *)

(* External Syntax for_sml queries *)

(* Author: Frank Pfenning *)

module type EXTQUERY = sig
  module ExtSyn : EXTSYN

  (*! structure Paths : PATHS !*)
  type query

  (* query *)
  val query : string option * ExtSyn.term -> query

  (* ucid : tm | tm *)
  type define

  val define : string option * ExtSyn.term * ExtSyn.term option -> define

  type solve

  val solve : string option * ExtSyn.term * Paths.region -> solve
  (* id : tm | _ : tm *)
end

(* signature EXTQUERY *)

module type RECON_QUERY = sig
  (*! structure IntSyn : INTSYN !*)
  include EXTQUERY

  exception Error of string

  val queryToQuery :
    query * Paths.location ->
    IntSyn.exp * string option * IntSyn.exp * string list

  (* (A, SOME("X"), [(Y1, "Y1"),...] *)
  (* where A is query type, X the optional proof term variable name *)
  (* Yi the EVars in the query and "Yi" their names *)
  val solveToSolve :
    define list * solve * Paths.location ->
    IntSyn.exp * (IntSyn.exp -> IntSyn.conDec * Paths.occConDec option list)
end

(* signature RECON_QUERY *)
