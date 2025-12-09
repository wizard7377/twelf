(* Reconstruct queries *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga, Jeff Polakow *)

module ReconQuery  (Global : GLOBAL)
                     (*! module IntSyn' : INTSYN !*)
		     (Names : NAMES)
		     (*! sharing Names.IntSyn = IntSyn' !*)
                     (Abstract : ABSTRACT)
		     (*! sharing Abstract.IntSyn = IntSyn' !*)
                     (*! module Paths' : PATHS !*)
                     module ReconTerm' : RECON_TERM
		     (*! sharing ReconTerm'.IntSyn = IntSyn' !*)
		     (*! sharing ReconTerm'.Paths = Paths' !*)
		     (TypeCheck : TYPECHECK)
		     (*! sharing TypeCheck.IntSyn = IntSyn' !*)
		     (Strict : STRICT)
		     (*! sharing Strict.IntSyn = IntSyn' !*)
		     (*! sharing Strict.Paths = Paths' !*)
		     (Timers : TIMERS)
                     (Print : PRINT): RECON_QUERY =
		     (*! sharing Print.IntSyn = IntSyn' !*)
struct
  (*! module IntSyn = IntSyn' !*)
  (*! module Paths = Paths' !*)
  module ExtSyn = ReconTerm'
  module T = ReconTerm'

  exception Error of string

  (* error (r, msg) raises a syntax error within region r with text msg *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  type name = string

  (* Queries, with optional proof term variable *)
  type query =
      query of name option * T.term

  (* define := <constant name> option * <def body> * <type> option *)
  type define =
      define of string option * T.term * T.term option

  type solve =
      solve of string option * T.term * Paths.region

  (* freeVar (XOpt, [(X1,"X1"),...,(Xn,"Xn")]) = true
     iff XOpt = SOME("Xi"), false otherwise
  *)
  let rec freeVar = function (SOME(name), Xs) -> 
        List.exists (fn (_, name') => name = name') Xs
    | _ -> false

  (* queryToQuery (q) = (V, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter module
     is instantiated to EVars, not FVars.
  *)
  (* call TypeCheck... if !doubleCheck = true? *)
  (* Wed May 20 08:00:28 1998 -fp *)
  fun queryToQuery (query (optName, tm), Paths.Loc (fileName, r)) = 
      let
        (* construct an external term for the result of the query
        let res = (case optName
                     of NONE => T.omitted (r)
                      | SOME name => T.evar (name, r)) *)
	let _ = Names.varReset IntSyn.Null
        let _ = T.resetErrors fileName
        let T.JClass ((V, oc), L) =
              (Timers.time Timers.recon T.reconQuery) (T.jclass tm)
        let _ = T.checkErrors (r)
        let _ = (case L
                   of IntSyn.Type => ()
                    | _ => error (r, "Query was not a type"))
	let Xs = Names.namedEVars ()
        (* ??? Since the reconstruction of a query is subject to constraints,
           couldn't optName "occur" in a constraint involving the type
           without being detected by this test?  -kw *)
	let _ = if freeVar (optName, Xs)
		  then error (r,
			      "Proof term variable " ^ valOf optName
			      ^ " occurs in type")
		else ()
      in
	(V, optName, Xs)
      end

  fun finishDefine (define (optName, tm, clsOpt),
                    ((U, oc1), (V, oc2Opt), L)) =
      let
        let (i, (U', V')) =
            (Timers.time Timers.abstract Abstract.abstractDef) (U, V)
            handle Abstract.Error (msg)
                   => raise Abstract.Error (Paths.wrap (Paths.toRegion oc1, msg))
        let name = case optName of NONE => "_" | SOME(name) => name
        let ocd = Paths.def (i, oc1, oc2Opt)
        let cd = ((Strict.check ((U', V'), SOME(ocd));
	           IntSyn.ConDef (name, NONE, i, U', V', L, IntSyn.ancestor U')) 
		  handle Strict.Error _ => 
			 IntSyn.AbbrevDef (name, NONE, i, U', V', L))
        (* is this necessary? -kw *)
        let cd = Names.nameConDec cd
        let _ = if !Global.chatter >= 3
                   then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                else ()
        let _ = if !Global.doubleCheck
                   then ((Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni L);
                         (Timers.time Timers.checking TypeCheck.check) (U', V'))
                else ()
        let conDecOpt = case optName of NONE => NONE | SOME _ => SOME (cd)
      in
        (conDecOpt, SOME(ocd))
      end

  fun finishSolve (solve (nameOpt, tm, r), U, V) =
      let
        let (i, (U', V')) =
            (Timers.time Timers.abstract Abstract.abstractDef) (U, V)
            handle Abstract.Error (msg)
                   => raise Abstract.Error (Paths.wrap (r, msg))
        let name = case nameOpt of NONE => "_" | SOME(name) => name
	let cd = ((Strict.check ((U', V'), NONE); 
	           IntSyn.ConDef (name, NONE, i, U', V', IntSyn.Type, IntSyn.ancestor U')) 
		  handle Strict.Error _ => 
			 IntSyn.AbbrevDef (name, NONE, i, U', V', IntSyn.Type))
        (* is this necessary? -kw *)
        let cd = Names.nameConDec cd
        let _ = if !Global.chatter >= 3
                   then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                else ()
        let _ = if !Global.doubleCheck
                   then ((Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni IntSyn.Type);
                         (Timers.time Timers.checking TypeCheck.check) (U', V'))
                else ()
        let conDecOpt = case nameOpt of NONE => NONE | SOME _ => SOME (cd)
      in
        conDecOpt
      end

  (* queryToQuery (q) = (V, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter module
     is instantiated to EVars, not FVars.
  *)
  (* call TypeCheck... if !doubleCheck = true? *)
  (* Wed May 20 08:00:28 1998 -fp *)
  fun solveToSolve (defines, sol as solve (optName, tm, r0), Paths.Loc (fileName, r)) = 
      let
	let _ = Names.varReset IntSyn.Null
        let _ = T.resetErrors fileName
        let rec mkd = function (define (_, tm1, NONE)) -> T.jterm tm1
          | (define (_, tm1, SOME (tm2))) -> T.jof (tm1, tm2)
        let rec mkj = function (nil) -> T.jnothing
          | (def::defs) -> T.jand (mkd def, mkj defs)
        let T.JAnd (defines', T.JClass ((V, _), L)) =
              (Timers.time Timers.recon T.reconQuery)
                (T.jand (mkj defines, T.jclass tm))
        let _ = T.checkErrors (r)

        let _ = (case L
                   of IntSyn.Type => ()
                    | _ => error (r0, "Query was not a type"))

	(* let Xs = Names.namedEVars () *)
        let rec sc = function (M, nil, _) -> 
              (case finishSolve (sol, M, V)
                 of NONE => nil
                  | SOME condec => [(condec, NONE)])
          | (M, def::defs, T.JAnd (T.JTerm ((U, oc1), V, L), f)) -> 
              (case finishDefine (def, ((U, oc1), (V, NONE), L))
                 of (NONE, _) => sc (M, defs, f)
                  | (SOME condec, ocdOpt) =>
                      (condec, ocdOpt)::sc (M, defs, f))
          | (M, def::defs, T.JAnd (T.JOf ((U, oc1), (V, oc2), L), f)) -> 
              (case finishDefine (def, ((U, oc1), (V, SOME oc2), L))
                 of (NONE, _) => sc (M, defs, f)
                  | (SOME condec, ocdOpt) =>
                      (condec, ocdOpt)::sc (M, defs, f))
      in
	(V, fun M -> sc (M, defines, defines'))
      end

end (* functor ReconQuery *)
