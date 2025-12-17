Twelf  Global GLOBAL    Timers TIMERS    Whnf WHNF    Print PRINT    Names NAMES    Origins ORIGINS    Lexer LEXER    Parser PARSER    Parser Names  Names   TypeCheck TYPECHECK    Strict STRICT    Constraints CONSTRAINTS    Abstract ABSTRACT    ReconTerm RECON_TERM     Term Term  ReconConDec RECON_CONDEC     Condec Condec  ReconQuery RECON_QUERY    ModeTable MODETABLE    ModeCheck MODECHECK    ReconMode RECON_MODE     Modedec Modedec  ModePrint MODEPRINT    ModeDec MODEDEC    StyleCheck STYLECHECK    Unique UNIQUE    UniqueTable MODETABLE    Cover COVER    Converter CONVERTER    TomegaPrint TOMEGAPRINT    TomegaCoverage TOMEGACOVERAGE    TomegaTypeCheck TOMEGATYPECHECK    Total TOTAL    Reduces REDUCES    Index INDEX    IndexSkolem INDEX    Subordinate SUBORDINATE    Compile COMPILE    AbsMachine ABSMACHINE    Tabled TABLED    Solve SOLVE     Query Query   Define Define   Solve Solve  Fquery FQUERY     Query Query   Define Define   Solve Solve  ThmSyn THMSYN    ThmSyn Names  Names   Thm THM    Thm ThmSyn  ThmSyn   ReconThm RECON_THM    ReconThm ThmSyn  ThmSyn    Tdecl Tdecl   Rdecl Rdecl   Tableddecl Tableddecl   KeepTabledecl KeepTabledecl   Wdecl Wdecl   Theorem Theorem   Theoremdec Theoremdec   Prove Prove   Establish Establish   Assert Assert  ThmPrint THMPRINT    ThmPrint ThmSyn  ThmSyn   TabledSyn TABLEDSYN    WorldSyn WORLDSYN    Worldify WORLDIFY    ModSyn MODSYN    ModSyn Names  Names   ReconModule RECON_MODULE    ReconModule ModSyn  ModSyn    Sigdef Sigdef   Structdec Structdec   Sigexp Sigexp   Strexp Strexp  MetaGlobal METAGLOBAL    Skolem SKOLEM    Prover PROVER    ClausePrint CLAUSEPRINT    Trace TRACE    PrintTeX PRINT    ClausePrintTeX CLAUSEPRINT    CSManager CS_MANAGER    CSManager Fixity  Names Fixity   CSInstaller CS_INSTALLER    Compat COMPAT    UnknownExn UNKNOWN_EXN    Msg MSG     TWELF  struct (*! structure IntSyn = IntSyn' !*)
module let rec msgs message slet rec chmsgns chMessage n s msglet rec fileOpenMsg(fileName) (match ! chatter with 0 -> () 1 -> msg ("[Loading file " ^ fileName ^ " ...") _ -> msg ("[Opening file " ^ fileName ^ "]\n"))let rec fileCloseMsg(fileName) (match ! chatter with 0 -> () 1 -> msg ("]\n") _ -> msg ("[Closing file " ^ fileName ^ "]\n"))(* result of a computation *)
type Result(* val withOpenIn : string -> (TextIO.instream -> 'a) -> 'a *)
(* withOpenIn fileName (fn instream => body) = x
       opens fileName for input to obtain instream and evaluates body.
       The file is closed during normal and abnormal exit of body.
    *)
let rec withOpenIn(fileName)(scope) let let  inlet  inlet  inlet  inlet  in in match result with value (x) -> x exception (exn) -> raise (exn)(* evarInstToString Xs = msg
       formats instantiated EVars as a substitution.
       Abbreviate as empty string if chatter level is < 3.
    *)
let rec evarInstToString(xs) if ! chatter >= 3 then evarInstToString (xs) else ""(* expToString (G, U) = msg
       formats expression as a string.
       Abbreviate as empty string if chatter level is < 3.
    *)
let rec expToStringgU if ! chatter >= 3 then expToString gU else ""let rec printProgTeX() (msg "\\begin{bigcode}\n"; printSgn (); msg "\\end{bigcode}\n")let rec printSgnTeX() (msg "\\begin{bigcode}\n"; printSgn (); msg "\\end{bigcode}\n")(* status ::= OK | ABORT  is the return status of various operations *)
type Statuslet rec abortchlev(msg) (chmsg chlev (fun () -> msg); aBORT)let rec abortFileMsgchlev(fileName,  , msg) abort chlev (fileName ^ ":" ^ msg ^ "\n")let rec abortIO(fileName,  , {cause = sysErr (m,  , _); function = f; name = n}) (msg ("IO Error on file " ^ fileName ^ ":\n" ^ m ^ "\n"); aBORT) abortIO(fileName,  , {function = f; _}) (msg ("IO Error on file " ^ fileName ^ " from function " ^ f ^ "\n"); aBORT)(* should move to paths, or into the prover module... but not here! -cs *)
let rec joinregion(r,  , nil) r joinregion(r,  , r' :: rs) joinregion (join (r,  , r'),  , rs)let rec joinregions(r :: rs) joinregion (r,  , rs)let rec constraintsMsg(cnstrL) "Typing ambiguous -- unresolved constraints\n" ^ cnstrsToString cnstrL(* val handleExceptions : int -> string -> ('a -> Status) -> 'a -> Status *)
(* handleExceptions chlev filename f x = f x
       where standard exceptions are handled and an appropriate error message is
       issued if chatter level is greater or equal to chlev.
       Unrecognized exceptions are re-raised.
    *)
let rec handleExceptionschlevfileName(f : 'a -> Status)(x : 'a) (try  with )(* During elaboration of a signature expression, each constant
       that that the user declares is added to this table.  At top level,
       however, the reference holds NONE (in particular, shadowing is
       allowed).
    *)
let  inlet rec installConstfromCS(cid,  , fileNameocOpt) let let  inlet  inlet  inlet  inlet  inlet  in in ()(* installConDec fromCS (conDec, ocOpt)
       installs the constant declaration conDec which originates at ocOpt
       in various global tables, including the global signature.
       Note: if fromCS = FromCS then the declaration comes from a Constraint
       Solver and some limitations on the types are lifted.
    *)
let rec installConDecfromCS(conDec,  , fileNameocOpt as (fileName,  , ocOpt),  , r) let let  inlet  inlet  inlet  inlet  inlet  inlet  in in cidlet rec installBlockDecfromCS(conDec,  , fileNameocOpt as (fileName,  , ocOpt),  , r) let let  inlet  inlet  in(* val _ = Origins.installOrigin (cid, fileNameocOpt) *)
let  inlet  in in cidlet rec installBlockDeffromCS(conDec,  , fileNameocOpt as (fileName,  , ocOpt),  , r) let let  inlet  inlet  in(* val _ = Origins.installOrigin (cid, fileNameocOpt) *)
let  in in cidlet rec installStrDec(strdec,  , module,  , r,  , isDef) let let rec installAction(data as (cid,  , _)) (installConst ordinary data; if ! chatter >= 4 then msg (conDecToString (sgnLookup cid) ^ "\n") else ())let  in in ()let rec includeSig(module,  , r,  , isDef) let let rec installAction(data as (cid,  , _)) (installConst ordinary data; if ! chatter >= 4 then msg (conDecToString (sgnLookup cid) ^ "\n") else ())let  in in ()let rec cidToStringa qidToString (constQid a)let rec invalidateuninstallFuncidsmsg let let  inlet  in in ()(* install1 (decl) = ()
       Installs one declaration
       Effects: global state
                may raise standard exceptions
    *)
let rec install1(fileName,  , (conDec condec,  , r)) (try  with ) install1(fileName,  , (abbrevDec condec,  , r)) (try  with ) install1(fileName,  , (clauseDec condec,  , r)) (try  with ) install1(fileName,  , (solve (defines,  , solve),  , r)) (try  with ) install1(fileName,  , (query (expected,  , try,  , query),  , r)) (try  with ) install1(fileName,  , (fQuery (query),  , r)) (try  with ) install1(fileName,  , (querytabled (numSol,  , try,  , query),  , r)) (try  with ) install1(fileName,  , (trustMe (dec,  , r'),  , r)) let let  inlet  inlet  inlet  in in () install1(fileName,  , (subordDec (qidpairs),  , r)) let let rec toCidqid match constLookup qid with nONE -> raise (error ("Undeclared identifier " ^ qidToString (valOf (constUndef qid)) ^ " in subord declaration")) sOME cid -> cidlet  inlet  in in if ! chatter >= 3 then msg ("%subord" ^ foldr (fun ((a1,  , a2),  , s) -> " (" ^ qidToString (constQid a1) ^ " " ^ qidToString (constQid a2) ^ ")" ^ s) ".\n" cidpairs) else () install1(fileName,  , (freezeDec (qids),  , r)) let let rec toCidqid match constLookup qid with nONE -> raise (error ("Undeclared identifier " ^ qidToString (valOf (constUndef qid)) ^ " in freeze declaration")) sOME cid -> cidlet  inlet  in in (* Subordinate.installFrozen cids *)
if ! chatter >= 3 then msg ("%freeze" ^ foldr (fun (a,  , s) -> " " ^ qidToString (constQid a) ^ s) ".\n" cids) else ()if ! chatter >= 4 then msg ("Frozen:" ^ foldr (fun (a,  , s) -> " " ^ qidToString (constQid a) ^ s) "\n" frozen) else () install1(fileName,  , (thawDec (qids),  , r)) let let  inlet rec toCidqid match constLookup qid with nONE -> raise (error ("Undeclared identifier " ^ qidToString (valOf (constUndef qid)) ^ " in thaw declaration")) sOME cid -> cidlet  inlet  inlet  inlet  in(* invalidate prior meta-theoretic properteis of signatures *)
(* exempt only %mode [incremental], %covers [not stored] *)
let  inlet  inlet  inlet  inlet  in in () install1(fileName,  , (deterministicDec (qids),  , r)) let let rec toCidqid match constLookup qid with nONE -> raise (error ("Undeclared identifier " ^ qidToString (valOf (constUndef qid)) ^ " in deterministic declaration")) sOME cid -> cidlet rec insertCidcid detTableInsert (cid,  , true)let  in in map insertCid cidsif ! chatter >= 3 then msg ((if ! chatter >= 4 then "%" else "") ^ "%deterministic" ^ foldr (fun (a,  , s) -> " " ^ qidToString (constQid a) ^ s) ".\n" cids) else () install1(fileName,  , (compile (qids),  , r)) let let rec toCidqid match constLookup qid with nONE -> raise (error ("Undeclared identifier " ^ qidToString (valOf (constUndef qid)) ^ " in compile assertion")) sOME cid -> cidlet  in(* MOVED -- ABP 4/4/03 *)
(* ******************************************* *)
let rec checkFreeOutnil () checkFreeOut(a :: la) let let  inlet  in in checkFreeOut lalet  in(* ******************************************* *)
let  inlet  inlet  inlet  inlet rec fcid conDecName (sgnLookup cid)let  inlet  in in () install1(fileName,  , (fixDec ((qid,  , r),  , fixity),  , _)) (match constLookup qid with nONE -> raise (error ("Undeclared identifier " ^ qidToString (valOf (constUndef qid)) ^ " in fixity declaration")) sOME cid -> try  with ) install1(fileName,  , (namePref ((qid,  , r),  , namePref),  , _)) (match constLookup qid with nONE -> raise (error ("Undeclared identifier " ^ qidToString (valOf (constUndef qid)) ^ " in name preference")) sOME cid -> try  with ) install1(fileName,  , (modeDec mterms,  , r)) let let  inlet  inlet  inlet  inlet  inlet  inlet  in in () install1(fileName,  , (uniqueDec mterms,  , r)) let let  inlet  in(* convert all UniqueTable.Error to Unique.Error *)
let  in(* Timing added to coverage --- fix !!! -fp Sun Aug 17 12:17:51 2003 *)
let  in(* %unique does not auto-freeze, since family must already be frozen *)
let  in in () install1(fileName,  , (coversDec mterms,  , r)) let let  inlet  inlet  in(* MERGE Fri Aug 22 13:43:12 2003 -cs *)
let  inlet  in in () install1(fileName,  , (totalDec lterm,  , r)) let (* Mon Dec  2 17:20:18 2002 -fp *)
(* coverage checker appears to be safe now *)
(*
          val _ = if not (!Global.unsafe)
                    then raise Total.Error (Paths.wrapLoc (Paths.Loc (fileName, r), "%total not safe: Toggle `unsafe' flag"))
                  else ()
          *)
let  inlet  in(* ******************************************* *)
(*  Temporarily disabled -- cs Thu Oct 30 12:46:44 2003
          fun checkFreeOut nil = ()
            | checkFreeOut (a :: La) =
              let
                val SOME ms = ModeTable.modeLookup a
                val _ = ModeCheck.checkFreeOut (a, ms)
              in
                checkFreeOut La
              end
          val _ = checkFreeOut La
          val (lemma, projs, sels) = Converter.installPrg La


          (* ABP 2/28/03 -- factoring *)
          val _ = if (!Global.chatter >= 4) then print ("[Factoring ...") else ()
          val P = Redundant.convert (Tomega.lemmaDef lemma)
          val _ = if (!Global.chatter >= 4) then print ("]\n") else ()

          val F = Converter.convertFor La

          val _ = if !Global.chatter >= 2
                    then print (TomegaPrint.funToString ((map (fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid)) La,
                                                          projs), P) ^ "\n")
                  else ()

          val _ = TomegaTypeCheck.checkPrg (IntSyn.Null, (P, F))

          val result1 = (TomegaCoverage.coverageCheckPrg (WorldSyn.lookup (hd La), IntSyn.Null, P); NONE)
                        handle TomegaCoverage.Error msg => SOME msg


(*      val result1 = NONE *)

          fun covererror (SOME msg1, msg2) = raise Cover.Error (Paths.wrap (r, "Functional and relational coverage checker report coverage error:\n[Functional] "
                                                                            ^ msg1 ^ "\n[Relational] " ^ msg2))
            | covererror (NONE, msg2)      = raise Cover.Error (Paths.wrap (r, "Functional coverage succeeds, relationals fails:\n[Relational] " ^ msg2))

7 ******************************************* *)
let  in(* pre-install for recursive checking *)
let  in(*        val _ = case (result1)
                    of NONE => ()
                     | SOME msg => raise Cover.Error (Paths.wrap (r, "Relational coverage succeeds, funcational fails:\n This indicates a bug in the functional checker.\n[Functional] " ^ msg))
*)
(* %total does not auto-freeze, since the predicate must already be frozen *)
let  in in () install1(fileName,  , (terminatesDec lterm,  , _)) let let  inlet  in(* allow re-declaration since safe? *)
(* Thu Mar 10 13:45:42 2005 -fp *)
(*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookup a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare termination order for frozen constant "
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *)
let  inlet  inlet  inlet  in in () install1(fileName,  , (reducesDec lterm,  , _)) let let  inlet  in(* allow re-declaration since safe? *)
(* Thu Mar 10 14:06:13 2005 -fp *)
(*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookupROrder a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare reduction order for frozen constant "
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *)
let  in(*  -bp6/12/99.   *)
let  inlet  inlet  in in () install1(fileName,  , (tabledDec tdecl,  , _)) let let  inlet  in(*  -bp6/12/99.   *)
let  in in () install1(fileName,  , (keepTableDec tdecl,  , _)) let let  inlet  inlet  in in () install1(fileName,  , (theoremDec tdec,  , r)) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in () install1(fileName,  , (proveDec lterm,  , r)) let let  inlet  in(* La is the list of type constants *)
let  inlet  inlet  inlet  in(* times itself *)
let  in in (install (fun e -> installConDec ordinary (e,  , (fileName,  , nONE),  , r)); install la) install1(fileName,  , (establishDec lterm,  , r)) let let  inlet  in(* La is the list of type constants *)
let  inlet  inlet  inlet  in(* times itself *)
 in install (fun e -> installConDec ordinary (e,  , (fileName,  , nONE),  , r)) install1(fileName,  , (assertDec aterm,  , _)) let let  inlet  inlet  in(* La is the list of type constants *)
let  inlet  in in install la install1(fileName,  , (worldDec wdecl,  , _)) let let  inlet  inlet rec flattennilf f flatten(cid :: l)f (match sgnLookup cid with blockDec _ -> flatten l (cid :: f) blockDef (_,  , _,  , l') -> flatten (l @ l') f)let  inlet  inlet  inlet  in in (time worlds (map (fun (a,  , _) -> worldcheck w a)) cpa; ()(*if !Global.doubleCheck
             then (map (fn (a,_) => Worldify.worldify a) cpa; ())
           else  ()  --cs Sat Aug 27 22:04:29 2005 *)
) install1(fileName,  , declr as (sigDef _,  , _)) install1WithSig (fileName,  , nONE,  , declr) install1(fileName,  , declr as (structDec _,  , _)) install1WithSig (fileName,  , nONE,  , declr) install1(fileName,  , declr as (include _,  , _)) install1WithSig (fileName,  , nONE,  , declr) install1(fileName,  , declr as (open _,  , _)) install1WithSig (fileName,  , nONE,  , declr) install1(fileName,  , (use name,  , r)) (match ! context with nONE -> useSolver (name) _ -> raise (error (wrap (r,  , "%use declaration needs to be at top level")))) install1WithSig(fileName,  , moduleOpt,  , (sigDef sigdef,  , r)) let (* FIX: should probably time this -kw *)
let  inlet  inlet  inlet  in in () install1WithSig(fileName,  , moduleOpt,  , (structDec structdec,  , r)) (match structdecToStructDec (structdec,  , moduleOpt) with structDec (idOpt,  , module,  , wherecls) -> let let  inlet  inlet  in in () structDef (idOpt,  , mid) -> let let  inlet  inlet  inlet  in in ()) install1WithSig(fileName,  , moduleOpt,  , (include sigexp,  , r)) let let  inlet  inlet  inlet  in in () install1WithSig(fileName,  , nONE,  , (open strexp,  , r)) let let  inlet  inlet  inlet  inlet  in in ()let rec installSubsig(fileName,  , s) let let  inlet  inlet  inlet  inlet  inlet  inlet rec installs install' ((time parsing expose) s) install'(cons ((beginSubsig,  , _),  , s')) install (installSubsig (fileName,  , s')) install'(cons ((endSubsig,  , _),  , s')) s' install'(cons (declr,  , s')) (install1 (fileName,  , declr); install s')let  inlet  inlet  inlet  inlet  inlet  in(* val _ = ModeTable.resetFrom mark *)
(* val _ = Total.resetFrom mark *)
(* val _ = Subordinate.resetFrom mark (* ouch! *) *)
(* val _ = Reduces.resetFrom mark *)
(* Origins, CompSyn, FunSyn harmless? -kw *)
(* val _ = IntSyn.resetFrom (mark, markStruct)
             FIX: DON'T eliminate out-of-scope cids for now -kw *)
 in match result with value (module,  , s') -> let let  in in install1WithSig (fileName,  , sOME module,  , declr)s'' exception exn -> raise (exn)(* loadFile (fileName) = status
       reads and processes declarations from fileName in order, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
let rec loadFile(fileName) handleExceptions 0 fileName (withOpenIn fileName) (fun instream -> let let  inlet rec installs install' ((time parsing expose) s) install'(empty) oK install'(cons ((beginSubsig,  , _),  , s')) install (installSubsig (fileName,  , s')) install'(cons (decl,  , s')) (install1 (fileName,  , decl); install s') in install (parseStream instream))(* loadString (str) = status
       reads and processes declarations from str, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
let rec loadStringstr handleExceptions 0 "string" (fun () -> let let  inlet rec installs install' ((time parsing expose) s) install'(empty) oK install'(cons ((beginSubsig,  , _),  , s')) (installSubsig ("string",  , s'); install s') install'(cons (decl,  , s')) (install1 ("string",  , decl); install s') in install (parseStream (openString str))) ()(* Interactive Query Top Level *)
let rec sLoop() if qLoop () then oK else aBORTlet rec topLoop() match (handleExceptions 0 "stdIn" sLoop) ()(* "stdIn" as fake fileName *)
 with aBORT -> topLoop () oK -> ()(* top () = () starts interactive query loop *)
let rec top() topLoop ()let rec installCSMDec(conDec,  , optFixity,  , mdecL) let let  in(* put a more reasonable region here? -kw *)
let  inlet  inlet  inlet  in in cidlet  in(* reset () = () clears all global tables, including the signature *)
let rec reset() (sgnReset (); reset (); reset (); reset (); reset (); (* -fp Wed Mar  9 20:24:45 2005 *)
reset (); reset (); reset (); reset (); (* -fp *)
reset (); (* -fp *)
reset (); (* -bp *)
reset (); (* -bp *)
labelReset (); sProgReset (); (* necessary? -fp; yes - bp*)
detTableReset (); (*  -bp *)
sProgReset (); (* resetting substitution trees *)
reset (); resetSolvers (); context := nONE)let rec readDecl() handleExceptions 0 "stdIn" (fun () -> let let  inlet rec installs install' ((time parsing expose) s) install'(empty) aBORT install'(cons ((beginSubsig,  , _),  , s')) (installSubsig ("stdIn",  , s'); oK) install'(cons (decl,  , s')) (install1 ("stdIn",  , decl); oK) in install (parseStream stdIn)) ()(* decl (id) = () prints declaration of constant id *)
let rec decl(id) (match stringToQid id with nONE -> (msg (id ^ " is not a well-formed qualified identifier\n"); aBORT) sOME qid -> (match constLookup qid with nONE -> (msg (qidToString (valOf (constUndef qid)) ^ " has not been declared\n"); aBORT) sOME cid -> decl' (cid))) decl'(cid) let let  in(* val fixity = Names.getFixity (cid) *)
(* can't get name preference right now *)
(* val mode = ModeTable.modeLookup (cid) *)
(* can't get termination declaration *)
 in msg (conDecToString conDec ^ "\n")oK(* Support tracking file modification times for smart re-appending. *)
module (* config = ["fileName1",...,"fileName<n>"] *)
(* Files will be read in the order given! *)
module (* structure Config *)
(* make (configFile)
       read and then load configuration from configFile
    *)
let rec make(fileName) load (read fileName)(* re-exporting environment parameters and utilities defined elsewhere *)
module module module module module module module module let  inlet  inlet  inlet  inlet  in Status  Status let  inlet  inlet  inlet  inlet  inlet  inmodule let  inlet  inmodule (* local *)
end