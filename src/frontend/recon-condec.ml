ReconConDec  Global GLOBAL    Names NAMES    Abstract ABSTRACT    ReconTerm' RECON_TERM    Constraints CONSTRAINTS    Strict STRICT    TypeCheck TYPECHECK    Timers TIMERS    Print PRINT    Msg MSG     RECON_CONDEC  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Paths = Paths' !*)
module exception (* error (r, msg) raises a syntax error within region r with text msg *)
let rec error(r,  , msg) raise (error (wrap (r,  , msg)))type Name(* Constant declarations *)
type Condec(* condecToConDec (condec, r) = (SOME(cd), SOME(ocd))
     if condec is a named constant declaration with occurrence tree ocd,
     NONE if name or occurrence tree is missing

     Free variables in condec are interpreted universally (as FVars)
     then abstracted as implicit parameters.

     Only works properly when the declaration contains no EVars.
  *)
(* should printing of result be moved to frontend? *)
(* Wed May 20 08:08:50 1998 -fp *)
let rec condecToConDec(condec (name,  , tm),  , loc (fileName,  , r),  , abbFlag) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in (sOME (cd),  , sOME (ocd)) condecToConDec(condef (optName,  , tm1,  , tm2Opt),  , loc (fileName,  , r),  , abbFlag) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in (optConDec,  , sOME (ocd)) condecToConDec(blockdec (name,  , lsome,  , lblock),  , loc (fileName,  , r),  , abbFlag) let let rec makectxnil null makectx(d :: l) decl (makectx l,  , d)let rec ctxToList(null,  , acc) acc ctxToList(decl (g,  , d),  , acc) ctxToList (g,  , d :: acc)let rec ctxAppend(g,  , null) g ctxAppend(g,  , decl (g',  , d)) decl (ctxAppend (g,  , g'),  , d)let rec ctxBlockToString(g0,  , (g1,  , g2)) let let  inlet  inlet  inlet  in in ctxToString (null,  , g0') ^ "\n" ^ (match g1' with null -> "" _ -> "some " ^ ctxToString (g0',  , g1') ^ "\n") ^ "pi " ^ ctxToString (ctxAppend (g0',  , g1'),  , g2')let rec checkFreevars(null,  , (g1,  , g2),  , r) () checkFreevars(g0,  , (g1,  , g2),  , r) let let  inlet  inlet  inlet  in in error (r,  , "Free variables in context block after term reconstruction:\n" ^ ctxBlockToString (g0',  , (g1',  , g2')))let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in (sOME bd,  , nONE) condecToConDec(blockdef (name,  , w),  , loc (fileName,  , r),  , abbFlag) let let  inlet  inlet  inlet  in in (sOME bd,  , nONE)let rec internalInst_ raise (match)let rec externalInst_ raise (match)end