ReconQuery  Global GLOBAL    Names NAMES    Abstract ABSTRACT    ReconTerm' RECON_TERM    TypeCheck TYPECHECK    Strict STRICT    Timers TIMERS    Print PRINT     RECON_QUERY  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Paths = Paths' !*)
module module exception (* error (r, msg) raises a syntax error within region r with text msg *)
let rec error(r,  , msg) raise (error (wrap (r,  , msg)))type Name(* Queries, with optional proof term variable *)
type Query(* define := <constant name> option * <def body> * <type> option *)
type Definetype Solve(* freeVar (XOpt, [(X1,"X1"),...,(Xn,"Xn")]) = true
     iff XOpt = SOME("Xi"), false otherwise
  *)
let rec freeVar(sOME (name),  , xs) exists (fun (_,  , name') -> name = name') xs freeVar_ false(* queryToQuery (q) = (V, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)
(* call TypeCheck... if !doubleCheck = true? *)
(* Wed May 20 08:00:28 1998 -fp *)
let rec queryToQuery(query (optName,  , tm),  , loc (fileName,  , r)) let (* construct an external term for the result of the query
        val res = (case optName
                     of NONE => T.omitted (r)
                      | SOME name => T.evar (name, r)) *)
let  inlet  inlet  inlet  inlet  inlet  in(* ??? Since the reconstruction of a query is subject to constraints,
           couldn't optName "occur" in a constraint involving the type
           without being detected by this test?  -kw *)
let  in in (v,  , optName,  , xs)let rec finishDefine(define (optName,  , tm,  , clsOpt),  , ((u,  , oc1),  , (v,  , oc2Opt),  , l)) let let  inlet  inlet  inlet  in(* is this necessary? -kw *)
let  inlet  inlet  inlet  in in (conDecOpt,  , sOME (ocd))let rec finishSolve(solve (nameOpt,  , tm,  , r),  , u,  , v) let let  inlet  inlet  in(* is this necessary? -kw *)
let  inlet  inlet  inlet  in in conDecOpt(* queryToQuery (q) = (V, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)
(* call TypeCheck... if !doubleCheck = true? *)
(* Wed May 20 08:00:28 1998 -fp *)
let rec solveToSolve(defines,  , sol as solve (optName,  , tm,  , r0),  , loc (fileName,  , r)) let let  inlet  inlet rec mkd(define (_,  , tm1,  , nONE)) jterm tm1 mkd(define (_,  , tm1,  , sOME (tm2))) jof (tm1,  , tm2)let rec mkj(nil) jnothing mkj(def :: defs) jand (mkd def,  , mkj defs)let  inlet  inlet  in(* val Xs = Names.namedEVars () *)
let rec sc(m,  , nil,  , _) (match finishSolve (sol,  , m,  , v) with nONE -> nil sOME condec -> [(condec,  , nONE)]) sc(m,  , def :: defs,  , jAnd (jTerm ((u,  , oc1),  , v,  , l),  , f)) (match finishDefine (def,  , ((u,  , oc1),  , (v,  , nONE),  , l)) with (nONE,  , _) -> sc (m,  , defs,  , f) (sOME condec,  , ocdOpt) -> (condec,  , ocdOpt) :: sc (m,  , defs,  , f)) sc(m,  , def :: defs,  , jAnd (jOf ((u,  , oc1),  , (v,  , oc2),  , l),  , f)) (match finishDefine (def,  , ((u,  , oc1),  , (v,  , sOME oc2),  , l)) with (nONE,  , _) -> sc (m,  , defs,  , f) (sOME condec,  , ocdOpt) -> (condec,  , ocdOpt) :: sc (m,  , defs,  , f)) in (v,  , fun m -> sc (m,  , defines,  , defines'))end