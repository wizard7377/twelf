ParseQuery  ExtQuery' EXTQUERY    ParseTerm PARSE_TERM    ParseTerm ExtSyn  ExtQuery' ExtSyn    PARSE_QUERY  struct (*! structure Parsing = Parsing' !*)
module module module module let rec returnQuery(optName,  , (tm,  , f)) (query (optName,  , tm),  , f)(* parseQuery1 (name, f, f')   ": A" from f' or "V" from f. *)
let rec parseQuery1(name,  , f,  , cons ((cOLON,  , r),  , s')) returnQuery (sOME (name),  , parseTerm' (expose s')) parseQuery1(name,  , f,  , _) returnQuery (nONE,  , parseTerm' f)(* parseQuery' : lexResult front -> ExtQuery.query * lexResult front *)
(* parseQuery'  "X : A" | "A" *)
(* Query parsing is ambiguous, since a term "V" might have the form "U' : V'" *)
(* We look for an uppercase variable X followed by a `:'.
       If we find this, we parse a query of the form "X : A".
       Otherwise we parse a query of the form "A".
    *)
let rec parseQuery'(f as cons ((iD (upper,  , name),  , r),  , s')) parseQuery1 (name,  , f,  , expose s') parseQuery'(f) returnQuery (nONE,  , parseTerm' f)(* parseQuery --- currently not exported *)
let rec parseQuery(s) parseQuery' (expose s)(* parseDefine4 parses the definition body *)
(* "U" *)
let rec parseDefine4(optName,  , optT,  , s) let let  in in (define (optName,  , tm',  , optT),  , f')(* parseDefine3 parses the equal sign in a long form define *)
(* "= U" *)
let rec parseDefine3(optName,  , (tm,  , cons ((eQUAL,  , r),  , s'))) parseDefine4 (optName,  , sOME (tm),  , s') parseDefine3(_,  , (tm,  , cons ((t,  , r),  , _))) error (r,  , "Expected `=', found " ^ toString t)(* parseDefine2 switches between short and long form *)
(* ": V = U" | "= U" *)
let rec parseDefine2(optName,  , cons ((cOLON,  , r),  , s')) parseDefine3 (optName,  , parseTerm' (expose s')) parseDefine2(optName,  , cons ((eQUAL,  , r),  , s')) parseDefine4 (optName,  , nONE,  , s') parseDefine2(_,  , cons ((t,  , r),  , _)) error (r,  , "Expected `:' or `=', found " ^ toString t)(* parseDefine1 parses the name of the constant to be defined *)
(* "c : V = U" | "_ : V = U" | "c = U" | "_ = U" *)
let rec parseDefine1(cons ((iD (idCase,  , name),  , r),  , s')) parseDefine2 (sOME (name),  , expose s') parseDefine1(cons ((uNDERSCORE,  , r),  , s')) parseDefine2 (nONE,  , expose s') parseDefine1(cons ((t,  , r),  , _)) error (r,  , "Expected identifier or `_', found " ^ toString t)let rec parseSolve3(defns,  , nameOpt,  , cons ((cOLON,  , r),  , s'),  , r0) let let  in in ((rev defns,  , solve (nameOpt,  , tm,  , join (r0,  , r))),  , f') parseSolve3(_,  , _,  , cons ((t,  , r),  , s'),  , r0) error (r,  , "Expected `:', found " ^ toString t)let rec parseSolve2(defns,  , cons ((uNDERSCORE,  , r),  , s'),  , r0) parseSolve3 (defns,  , nONE,  , expose s',  , r0) parseSolve2(defns,  , cons ((iD (_,  , name),  , r),  , s'),  , r0) parseSolve3 (defns,  , sOME name,  , expose s',  , r0) parseSolve2(_,  , cons ((t,  , r),  , s'),  , r0) error (r,  , "Expected identifier or `_', found " ^ toString t) parseSolve1(defns,  , cons ((sOLVE,  , r0),  , s')) parseSolve2 (defns,  , expose s',  , r0) parseSolve1(defns,  , cons ((dEFINE,  , r0),  , s')) let let  in in parseSolve1 (defn :: defns,  , f') parseSolve1(defns,  , cons ((t,  , r),  , s)) error (r,  , "Expected %define or %solve, found " ^ toString t) parseSolve'(f) parseSolve1 (nil,  , f)let  inlet  in(* local ... in *)
end