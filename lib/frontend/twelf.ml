(* Front End Interface *)


(* Author: Frank Pfenning *)


(* Modified: Carsten Schuermann, Jeff Polakow *)


(* Modified: Brigitte Pientka, Roberto Virga *)


module Twelf ReconTerm.termParser.ExtSyn.term ReconConDec.condecParser.ExtConDec.condec ReconMode.modedecParser.ExtModes.modedec Solve.ExtQuery.queryParser.ExtQuery.query Solve.ExtQuery.defineParser.ExtQuery.define Solve.ExtQuery.solveParser.ExtQuery.solve Fquery.ExtQuery.queryParser.ExtQuery.query Fquery.ExtQuery.defineParser.ExtQuery.define Fquery.ExtQuery.solveParser.ExtQuery.solve ReconThm.tdeclParser.ThmExtSyn.tdecl ReconThm.rdeclParser.ThmExtSyn.rdecl ReconThm.tableddeclParser.ThmExtSyn.tableddecl ReconThm.keepTabledeclParser.ThmExtSyn.keepTabledecl ReconThm.wdeclParser.ThmExtSyn.wdecl ReconThm.theoremParser.ThmExtSyn.theorem ReconThm.theoremdecParser.ThmExtSyn.theoremdec ReconThm.proveParser.ThmExtSyn.prove ReconThm.establishParser.ThmExtSyn.establish ReconThm.assertParser.ThmExtSyn.assert ReconModule.sigdefParser.ModExtSyn.sigdef ReconModule.structdecParser.ModExtSyn.structdec ReconModule.sigexpParser.ModExtSyn.sigexp ReconModule.strexpParser.ModExtSyn.strexp (Global : GLOBAL) (Timers : TIMERS) (Whnf : WHNF) (Print : PRINT) (Names : NAMES) (Origins : ORIGINS) (Lexer : LEXER) (Parser : PARSER) (TypeCheck : TYPECHECK) (Strict : STRICT) (Constraints : CONSTRAINTS) (Abstract : ABSTRACT) (ReconTerm : RECON_TERM) (ReconConDec : RECON_CONDEC) (ReconQuery : RECON_QUERY) (ModeTable : MODETABLE) (ModeCheck : MODECHECK) (ReconMode : RECON_MODE) (ModePrint : MODEPRINT) (ModeDec : MODEDEC) (StyleCheck : STYLECHECK) (Unique : UNIQUE) (UniqueTable : MODETABLE) (Cover : COVER) (Converter : CONVERTER) (TomegaPrint : TOMEGAPRINT) (TomegaCoverage : TOMEGACOVERAGE) (TomegaTypeCheck : TOMEGATYPECHECK) (Total : TOTAL) (Reduces : REDUCES) (Index : INDEX) (IndexSkolem : INDEX) (Subordinate : SUBORDINATE) (Compile : COMPILE) (AbsMachine : ABSMACHINE) (Tabled : TABLED) (Solve : SOLVE) (Fquery : FQUERY) (ThmSyn : THMSYN) (Thm : THM) (ReconThm : RECON_THM) (ThmPrint : THMPRINT) (TabledSyn : TABLEDSYN) (WorldSyn : WORLDSYN) (Worldify : WORLDIFY) (ModSyn : MODSYN) (ReconModule : RECON_MODULE) (MetaGlobal : METAGLOBAL) (Skolem : SKOLEM) (Prover : PROVER) (ClausePrint : CLAUSEPRINT) (Trace : TRACE) (PrintTeX : PRINT) (ClausePrintTeX : CLAUSEPRINT) (CSManager : CS_MANAGER) (CSInstaller : CS_INSTALLER) (Compat : COMPAT) (UnknownExn : UNKNOWN_EXN) (Msg : MSG) : TWELF = struct (*! structure IntSyn = IntSyn' !*)

module S = ParserStream
let rec msg s  = Msg.message s
let rec chmsg n s  = Global.chMessage n s msg
let rec fileOpenMsg (fileName)  = (match ! Global.chatter with 0 -> () | 1 -> msg ("[Loading file " ^ fileName ^ " ...") | _ -> msg ("[Opening file " ^ fileName ^ "]\n"))
let rec fileCloseMsg (fileName)  = (match ! Global.chatter with 0 -> () | 1 -> msg ("]\n") | _ -> msg ("[Closing file " ^ fileName ^ "]\n"))
(* result of a computation *)

type 'a result = Value of 'a | Exception of exn
(* val withOpenIn : string -> (TextIO.instream -> 'a) -> 'a *)

(* withOpenIn fileName (fn instream => body) = x
       opens fileName for_sml input to obtain instream and evaluates body.
       The file is closed during normal and abnormal exit of body.
    *)

let rec withOpenIn (fileName) (scope)  = ( let instream = TextIO.openIn fileName in let _ = fileOpenMsg (fileName) in let result = try Value (scope instream) with exn -> Exception (exn) in let _ = fileCloseMsg (fileName) in let _ = TextIO.closeIn instream in  match result with Value (x) -> x | Exception (exn) -> raise (exn) )
(* evarInstToString Xs = msg
       formats instantiated a substitution.
       empty string if chatter level is < 3.
    *)

let rec evarInstToString (Xs)  = if ! Global.chatter >= 3 then Print.evarInstToString (Xs) else ""
(* expToString (G, U) = msg
       formats a string.
       empty string if chatter level is < 3.
    *)

let rec expToString GU  = if ! Global.chatter >= 3 then Print.expToString GU else ""
let rec printProgTeX ()  = (msg "\\begin{bigcode}\n"; ClausePrintTeX.printSgn (); msg "\\end{bigcode}\n")
let rec printSgnTeX ()  = (msg "\\begin{bigcode}\n"; PrintTeX.printSgn (); msg "\\end{bigcode}\n")
(* status ::= OK | ABORT  is the return status of various operations *)

type status = OK | ABORT
let rec abort chlev (msg)  = (chmsg chlev (fun () -> msg); ABORT)
let rec abortFileMsg chlev (fileName, msg)  = abort chlev (fileName ^ ":" ^ msg ^ "\n")
let rec abortIO = function (fileName, {cause = OS.SysErr (m, _); function_ = f; name = n}) -> (msg ("IO Error on file " ^ fileName ^ ":\n" ^ m ^ "\n"); ABORT) | (fileName, {function_ = f; _}) -> (msg ("IO Error on file " ^ fileName ^ " from function " ^ f ^ "\n"); ABORT)
(* should move to paths, or into the prover module... but not here! -cs *)

let rec joinregion = function (r, []) -> r | (r, r' :: rs) -> joinregion (Paths.join (r, r'), rs)
let rec joinregions (r :: rs)  = joinregion (r, rs)
let rec constraintsMsg (cnstrL)  = "Typing ambiguous -- unresolved constraints\n" ^ Print.cnstrsToString cnstrL
(* val handleExceptions : int -> string -> ('a -> Status) -> 'a -> Status *)

(* handleExceptions chlev filename f x = f x
       where standard exceptions are handled and an appropriate error message is
       issued if chatter level is greater or equal to chlev.
       Unrecognized exceptions are re-raised.
    *)

let rec handleExceptions chlev fileName (f : 'a -> status) (x : 'a)  = (try f x with ReconTerm.Error (msg) -> abortFileMsg chlev (fileName, msg) | ReconConDec.Error (msg) -> abortFileMsg chlev (fileName, msg) | ReconQuery.Error (msg) -> abortFileMsg chlev (fileName, msg) | ReconMode.Error (msg) -> abortFileMsg chlev (fileName, msg) | ReconThm.Error (msg) -> abortFileMsg chlev (fileName, msg) | ReconModule.Error (msg) -> abortFileMsg chlev (fileName, msg) | TypeCheck.Error (msg) -> abort 0 ("Double-checking types fails: " ^ msg ^ "\n" ^ "This indicates a bug in Twelf.\n") | Abstract.Error (msg) -> abortFileMsg chlev (fileName, msg) | (* | Constraints.Error (cnstrL) => abortFileMsg (fileName, constraintsMsg cnstrL) *)
 | Total.Error (msg) -> abort chlev (msg ^ "\n") | (* Total includes filename *)
 | Reduces.Error (msg) -> abort chlev (msg ^ "\n") | (* Reduces includes filename *)
 | Compile.Error (msg) -> abortFileMsg chlev (fileName, msg) | Thm.Error (msg) -> abortFileMsg chlev (fileName, msg) | ModeTable.Error (msg) -> abortFileMsg chlev (fileName, msg) | ModeCheck.Error (msg) -> abort chlev (msg ^ "\n") | (* ModeCheck includes filename *)
 | ModeDec.Error (msg) -> abortFileMsg chlev (fileName, msg) | Unique.Error (msg) -> abortFileMsg chlev (fileName, msg) | Cover.Error (msg) -> abortFileMsg chlev (fileName, msg) | Parsing.Error (msg) -> abortFileMsg chlev (fileName, msg) | Lexer.Error (msg) -> abortFileMsg chlev (fileName, msg) | IntSyn.Error (msg) -> abort chlev ("Signature error: " ^ msg ^ "\n") | Names.Error (msg) -> abortFileMsg chlev (fileName, msg) | (* - Not supported in polyML ABP - 4/20/03
              * | IO.Io (ioError) => abortIO (fileName, ioError)
              *)
 | Solve.AbortQuery (msg) -> abortFileMsg chlev (fileName, msg) | ThmSyn.Error (msg) -> abortFileMsg chlev (fileName, msg) | Prover.Error (msg) -> abortFileMsg chlev (fileName, msg) | Strict.Error (msg) -> abortFileMsg chlev (fileName, msg) | Subordinate.Error (msg) -> abortFileMsg chlev (fileName, msg) | WorldSyn.Error (msg) -> abort chlev (msg ^ "\n") | (* includes filename *)
 | Worldify.Error (msg) -> abort chlev (msg ^ "\n") | (* includes filename *)
 | ModSyn.Error (msg) -> abortFileMsg chlev (fileName, msg) | Converter.Error (msg) -> abortFileMsg chlev (fileName, msg) | CSManager.Error (msg) -> abort chlev ("Constraint Solver Manager error: " ^ msg ^ "\n") | exn -> (abort 0 (UnknownExn.unknownExn exn); raise (exn)))
(* During elaboration of a signature expression, each constant
       that that the user declares is added to this table.  At top level,
       however, the reference holds NONE (in particular, shadowing is
       allowed).
    *)

let context : Names.namespace option ref = ref None
let rec installConst fromCS (cid, fileNameocOpt)  = ( let _ = Origins.installOrigin (cid, fileNameocOpt) in let _ = Index.install fromCS (IntSyn.Const cid) in let _ = IndexSkolem.install fromCS (IntSyn.Const cid) in let _ = (Timers.time Timers.compiling Compile.install) fromCS cid in let _ = (Timers.time Timers.subordinate Subordinate.install) cid in let _ = (Timers.time Timers.subordinate Subordinate.installDef) cid in  () )
(* installConDec fromCS (conDec, ocOpt)
       installs the constant declaration conDec which originates at ocOpt
       in various global tables, including the global signature.
       Note: if fromCS = FromCS then the declaration comes from a Constraint
       Solver and some limitations on the types are lifted.
    *)

let rec installConDec fromCS (conDec, fileNameocOpt, r)  = ( let _ = (Timers.time Timers.modes ModeCheck.checkD) (conDec, fileName, ocOpt) in let cid = IntSyn.sgnAdd conDec in let _ = try (match (fromCS, ! context) with (IntSyn.Ordinary, Some namespace) -> Names.insertConst (namespace, cid) | (IntSyn.Clause, Some namespace) -> Names.insertConst (namespace, cid) | _ -> ()) with Names.Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in let _ = Names.installConstName cid in let _ = try installConst fromCS (cid, fileNameocOpt) with Subordinate.Error (msg) -> raise (Subordinate.Error (Paths.wrap (r, msg))) in let _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ()) in let _ = if ! Global.style >= 1 then StyleCheck.checkConDec cid else () in  cid )
let rec installBlockDec fromCS (conDec, fileNameocOpt, r)  = ( (* val _ = Origins.installOrigin (cid, fileNameocOpt) *)
let cid = IntSyn.sgnAdd conDec in let _ = try (match (fromCS, ! context) with (IntSyn.Ordinary, Some namespace) -> Names.insertConst (namespace, cid)(* (Clause, _) should be impossible *)
 | _ -> ()) with Names.Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in let _ = Names.installConstName cid in let _ = try (Timers.time Timers.subordinate Subordinate.installBlock) cid with Subordinate.Error (msg) -> raise (Subordinate.Error (Paths.wrap (r, msg))) in let _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ()) in  cid )
let rec installBlockDef fromCS (conDec, fileNameocOpt, r)  = ( (* val _ = Origins.installOrigin (cid, fileNameocOpt) *)
let cid = IntSyn.sgnAdd conDec in let _ = try (match (fromCS, ! context) with (IntSyn.Ordinary, Some namespace) -> Names.insertConst (namespace, cid)(* (Clause, _) should be impossible *)
 | _ -> ()) with Names.Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in let _ = Names.installConstName cid in let _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ()) in  cid )
let rec installStrDec (strdec, module_, r, isDef)  = ( let rec installAction (data)  = (installConst IntSyn.Ordinary data; if ! Global.chatter >= 4 then msg (Print.conDecToString (IntSyn.sgnLookup cid) ^ "\n") else ()) in let _ = try ModSyn.installStruct (strdec, module_, ! context, installAction, isDef) with Names.Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in  () )
let rec includeSig (module_, r, isDef)  = ( let rec installAction (data)  = (installConst IntSyn.Ordinary data; if ! Global.chatter >= 4 then msg (Print.conDecToString (IntSyn.sgnLookup cid) ^ "\n") else ()) in let _ = try ModSyn.installSig (module_, ! context, installAction, isDef) with Names.Error msg -> raise (Names.Error (Paths.wrap (r, msg))) in  () )
let rec cidToString a  = Names.qidToString (Names.constQid a)
let rec invalidate uninstallFun cids msg  = ( let uninstalledCids = List.filter (fun a -> uninstallFun a) cids in let _ = match uninstalledCids with [] -> () | _ -> chmsg 4 (fun () -> "Invalidated " ^ msg ^ " properties of families" ^ List.foldr (fun (a, s) -> " " ^ cidToString a ^ s) "\n" uninstalledCids) in  () )
(* install1 (decl) = ()
       Installs one declaration
       Effects: global state
                may raise standard exceptions
    *)

let rec install1 = function (fileName, (Parser.ConDec condec, r)) -> (try ( let (optConDec, ocOpt) = ReconConDec.condecToConDec (condec, Paths.Loc (fileName, r), false) in let rec icd = function (Some (conDec)) -> ( (* allocate new cid. *)
let cid = installBlockDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r) in  () ) | (Some (conDec)) -> ( (* allocate new cid. *)
let cid = installBlockDef IntSyn.Ordinary (conDec, (fileName, ocOpt), r) in  () ) | (Some (conDec)) -> ( (* names are assigned in ReconConDec *)
(* val conDec' = nameConDec (conDec) *)
(* should print here, not in ReconConDec *)
(* allocate new cid after checking modes! *)
let cid = installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r) in  () ) | (None) -> () in  icd optConDec ) with Constraints.Error (eqns) -> raise (ReconTerm.Error (Paths.wrap (r, constraintsMsg eqns)))) | (fileName, (Parser.AbbrevDec condec, r)) -> (try ( let (optConDec, ocOpt) = ReconConDec.condecToConDec (condec, Paths.Loc (fileName, r), true) in let rec icd = function (Some (conDec)) -> ( (* names are assigned in ReconConDec *)
(* val conDec' = nameConDec (conDec) *)
(* should print here, not in ReconConDec *)
(* allocate new cid after checking modes! *)
let cid = installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r) in  () ) | (None) -> () in  icd optConDec ) with Constraints.Error (eqns) -> raise (ReconTerm.Error (Paths.wrap (r, constraintsMsg eqns)))) | (fileName, (Parser.ClauseDec condec, r)) -> (try ( (* val _ = print "%clause " *)
let (optConDec, ocOpt) = ReconConDec.condecToConDec (condec, Paths.Loc (fileName, r), false) in let rec icd = function (Some (conDec)) -> ( let cid = installConDec IntSyn.Clause (conDec, (fileName, ocOpt), r) in  () ) | None -> () in  icd optConDec ) with Constraints.Error (eqns) -> raise (ReconTerm.Error (Paths.wrap (r, constraintsMsg eqns)))) | (fileName, (Parser.Solve (defines, solve), r)) -> (try ( let conDecL = try Solve.solve (defines, solve, Paths.Loc (fileName, r)) with Solve.AbortQuery (msg) -> raise (Solve.AbortQuery (Paths.wrap (r, msg))) in let rec icd (conDec, ocOpt)  = (( (* should print here, not in ReconQuery *)
(* allocate new cid after checking modes! *)
(* allocate cid after strictness has been checked! *)
let cid = installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r) in  () )) in  List.app icd conDecL ) with Constraints.Error (eqns) -> raise (ReconTerm.Error (Paths.wrap (r, constraintsMsg eqns)))) | (fileName, (Parser.Query (expected, try_, query), r)) -> (try Solve.query ((expected, try_, query), Paths.Loc (fileName, r)) with Solve.AbortQuery (msg) -> raise (Solve.AbortQuery (Paths.wrap (r, msg)))) | (fileName, (Parser.FQuery (query), r)) -> (try Fquery.run (query, Paths.Loc (fileName, r)) with Fquery.AbortQuery (msg) -> raise (Fquery.AbortQuery (Paths.wrap (r, msg)))) | (fileName, (Parser.Querytabled (numSol, try_, query), r)) -> (try Solve.querytabled ((numSol, try_, query), Paths.Loc (fileName, r)) with Solve.AbortQuery (msg) -> raise (Solve.AbortQuery (Paths.wrap (r, msg)))) | (fileName, (Parser.TrustMe (dec, r'), r)) -> ( let _ = if not (! Global.unsafe) then raise (Thm.Error ("%trustme not safe: Toggle `unsafe' flag")) else () in let _ = chmsg 3 (fun () -> "[%trustme ...\n") in let _ = match handleExceptions 4 fileName (fun args -> (install1 args; OK)) (fileName, (dec, r)) with OK -> chmsg 3 (fun () -> "trustme subject succeeded\n") | ABORT -> chmsg 3 (fun () -> "trustme subject failed; continuing\n") in let _ = chmsg 3 (fun () -> "%]\n") in  () ) | (fileName, (Parser.SubordDec (qidpairs), r)) -> ( let rec toCid qid  = match Names.constLookup qid with None -> raise (Names.Error ("Undeclared identifier " ^ Names.qidToString (valOf (Names.constUndef qid)) ^ " in subord declaration")) | Some cid -> cid in let cidpairs = try List.map (fun (qid1, qid2) -> (toCid qid1, toCid qid2)) qidpairs with Names.Error (msg) -> raise (Names.Error (Paths.wrap (r, msg))) in let _ = try List.app Subordinate.addSubord cidpairs with Subordinate.Error (msg) -> raise (Subordinate.Error (Paths.wrap (r, msg))) in  if ! Global.chatter >= 3 then msg ("%subord" ^ List.foldr (fun ((a1, a2), s) -> " (" ^ Names.qidToString (Names.constQid a1) ^ " " ^ Names.qidToString (Names.constQid a2) ^ ")" ^ s) ".\n" cidpairs) else () ) | (fileName, (Parser.FreezeDec (qids), r)) -> ( let rec toCid qid  = match Names.constLookup qid with None -> raise (Names.Error ("Undeclared identifier " ^ Names.qidToString (valOf (Names.constUndef qid)) ^ " in freeze declaration")) | Some cid -> cid in let cids = try List.map toCid qids with Names.Error (msg) -> raise (Names.Error (Paths.wrap (r, msg))) in let frozen = try Subordinate.freeze cids with Subordinate.Error (msg) -> raise (Subordinate.Error (Paths.wrap (r, msg))) in  (* Subordinate.installFrozen cids *)
if ! Global.chatter >= 3 then msg ("%freeze" ^ List.foldr (fun (a, s) -> " " ^ Names.qidToString (Names.constQid a) ^ s) ".\n" cids) else (); if ! Global.chatter >= 4 then msg ("Frozen:" ^ List.foldr (fun (a, s) -> " " ^ Names.qidToString (Names.constQid a) ^ s) "\n" frozen) else () ) | (fileName, (Parser.ThawDec (qids), r)) -> ( (* invalidate prior meta-theoretic properteis of signatures *)
(* exempt only %mode [incremental], %covers [not stored] *)
let _ = if not (! Global.unsafe) then raise (ThmSyn.Error "%thaw not safe: Toggle `unsafe' flag") else () in let rec toCid qid  = match Names.constLookup qid with None -> raise (Names.Error ("Undeclared identifier " ^ Names.qidToString (valOf (Names.constUndef qid)) ^ " in thaw declaration")) | Some cid -> cid in let cids = try List.map toCid qids with Names.Error (msg) -> raise (Names.Error (Paths.wrap (r, msg))) in let thawed = try Subordinate.thaw cids with Subordinate.Error (msg) -> raise (Subordinate.Error (Paths.wrap (r, msg))) in let _ = if ! Global.chatter >= 3 then msg ("%thaw" ^ List.foldr (fun (a, s) -> " " ^ cidToString a ^ s) ".\n" cids) else () in let _ = if ! Global.chatter >= 4 then msg ("Thawed" ^ List.foldr (fun (a, s) -> " " ^ cidToString a ^ s) "\n" thawed) else () in let _ = invalidate WorldSyn.uninstall thawed "world" in let _ = invalidate Thm.uninstallTerminates thawed "termination" in let _ = invalidate Thm.uninstallReduces thawed "reduction" in let _ = invalidate UniqueTable.uninstallMode thawed "uniqueness" in let _ = invalidate Total.uninstall thawed "totality" in  () ) | (fileName, (Parser.DeterministicDec (qids), r)) -> ( let rec toCid qid  = match Names.constLookup qid with None -> raise (Names.Error ("Undeclared identifier " ^ Names.qidToString (valOf (Names.constUndef qid)) ^ " in deterministic declaration")) | Some cid -> cid in let rec insertCid cid  = CompSyn.detTableInsert (cid, true) in let cids = try List.map toCid qids with Names.Error (msg) -> raise (Names.Error (Paths.wrap (r, msg))) in  List.map insertCid cids; if ! Global.chatter >= 3 then msg ((if ! Global.chatter >= 4 then "%" else "") ^ "%deterministic" ^ List.foldr (fun (a, s) -> " " ^ Names.qidToString (Names.constQid a) ^ s) ".\n" cids) else () ) | (fileName, (Parser.Compile (qids), r)) -> ( (* MOVED -- ABP 4/4/03 *)
(* ******************************************* *)
(* ******************************************* *)
let rec toCid qid  = match Names.constLookup qid with None -> raise (Names.Error ("Undeclared identifier " ^ Names.qidToString (valOf (Names.constUndef qid)) ^ " in compile assertion")) | Some cid -> cid in let cids = try List.map toCid qids with Names.Error (msg) -> raise (Names.Error (Paths.wrap (r, msg))) in let rec checkFreeOut = function [] -> () | (a :: La) -> ( let Some ms = ModeTable.modeLookup a in let _ = ModeCheck.checkFreeOut (a, ms) in  checkFreeOut La ) in let _ = checkFreeOut cids in let (lemma, projs, sels) = Converter.installPrg cids in let P = Tomega.lemmaDef lemma in let F = Converter.convertFor cids in let _ = TomegaTypeCheck.checkPrg (IntSyn.Null, (P, F)) in let rec f cid  = IntSyn.conDecName (IntSyn.sgnLookup cid) in let _ = if ! Global.chatter >= 2 then msg ("\n" ^ TomegaPrint.funToString ((map f cids, projs), P) ^ "\n") else () in let _ = if ! Global.chatter >= 3 then msg ((if ! Global.chatter >= 4 then "%" else "") ^ "%compile" ^ List.foldr (fun (a, s) -> " " ^ Names.qidToString (Names.constQid a) ^ s) ".\n" cids) else () in  () ) | (fileName, (Parser.FixDec ((qid, r), fixity), _)) -> (match Names.constLookup qid with None -> raise (Names.Error ("Undeclared identifier " ^ Names.qidToString (valOf (Names.constUndef qid)) ^ " in fixity declaration")) | Some cid -> try (Names.installFixity (cid, fixity); if ! Global.chatter >= 3 then msg ((if ! Global.chatter >= 4 then "%" else "") ^ Names.Fixity.toString fixity ^ " " ^ Names.qidToString (Names.constQid cid) ^ ".\n") else ()) with Names.Error (msg) -> raise (Names.Error (Paths.wrap (r, msg)))) | (fileName, (Parser.NamePref ((qid, r), namePref), _)) -> (match Names.constLookup qid with None -> raise (Names.Error ("Undeclared identifier " ^ Names.qidToString (valOf (Names.constUndef qid)) ^ " in name preference")) | Some cid -> try Names.installNamePref (cid, namePref) with Names.Error (msg) -> raise (Names.Error (Paths.wrap (r, msg)))) | (fileName, (Parser.ModeDec mterms, r)) -> ( let mdecs = List.map ReconMode.modeToMode mterms in let _ = ReconTerm.checkErrors (r) in let _ = List.app (fun (mdec, r) -> match ModeTable.modeLookup a with None -> () | Some _ -> if Subordinate.frozen [a] then raise (ModeTable.Error (Paths.wrap (r, "Cannot redeclare mode for_sml frozen constant " ^ Names.qidToString (Names.constQid a)))) else ()) mdecs in let _ = List.app (fun (mdec, r) -> try (match (IntSyn.conDecStatus (IntSyn.sgnLookup a)) with IntSyn.Normal -> ModeTable.installMode mdec | _ -> raise (ModeTable.Error "Cannot declare modes for_sml foreign constants")) with ModeTable.Error (msg) -> raise (ModeTable.Error (Paths.wrap (r, msg)))) mdecs in let _ = List.app (fun mdec -> ModeDec.checkPure mdec) mdecs in let _ = List.app (fun (mdec, r) -> try ModeCheck.checkMode mdec(* exception comes with location *)
 with ModeCheck.Error (msg) -> raise (ModeCheck.Error (msg))) mdecs in let _ = if ! Global.chatter >= 3 then msg ("%mode " ^ ModePrint.modesToString (List.map (fun (mdec, r) -> mdec) mdecs) ^ ".\n") else () in  () ) | (fileName, (Parser.UniqueDec mterms, r)) -> ( (* convert all UniqueTable.Error to Unique.Error *)
(* Timing added to coverage --- fix !!! -fp Sun Aug 17 12:17:51 2003 *)
(* %unique does not auto-freeze, since family must already be frozen *)
let mdecs = List.map ReconMode.modeToMode mterms in let _ = ReconTerm.checkErrors (r) in let _ = List.app (fun (mdec, r) -> try (match (IntSyn.conDecStatus (IntSyn.sgnLookup a)) with IntSyn.Normal -> UniqueTable.installMode mdec | _ -> raise (UniqueTable.Error "Cannot declare modes for_sml foreign constants")) with UniqueTable.Error (msg) -> raise (Unique.Error (Paths.wrap (r, msg)))) mdecs in let _ = List.app (fun (mdec, r) -> try (Timers.time Timers.coverage Unique.checkUnique) mdec with Unique.Error (msg) -> raise (Unique.Error (Paths.wrap (r, msg)))) mdecs in let _ = if ! Global.chatter >= 3 then msg ("%unique " ^ ModePrint.modesToString (List.map (fun (mdec, r) -> mdec) mdecs) ^ ".\n") else () in  () ) | (fileName, (Parser.CoversDec mterms, r)) -> ( (* MERGE Fri Aug 22 13:43:12 2003 -cs *)
let mdecs = List.map ReconMode.modeToMode mterms in let _ = ReconTerm.checkErrors (r) in let _ = List.app (fun mdec -> ModeDec.checkPure mdec) mdecs in let _ = List.app (fun (mdec, r) -> try (Timers.time Timers.coverage Cover.checkCovers) mdec with Cover.Error (msg) -> raise (Cover.Error (Paths.wrap (r, msg)))) mdecs in let _ = if ! Global.chatter >= 3 then msg ("%covers " ^ ModePrint.modesToString (List.map (fun (mdec, r) -> mdec) mdecs) ^ ".\n") else () in  () ) | (fileName, (Parser.TotalDec lterm, r)) -> ( (* Mon Dec  2 17:20:18 2002 -fp *)
(* coverage checker appears to be safe now *)
(*
          val _ = if not (!Global.unsafe)
                    then raise Total.Error (Paths.wrapLoc (Paths.Loc (fileName, r), "%total not safe: Toggle `unsafe' flag"))
                  else ()
          *)
(* ******************************************* *)
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
(* pre-install for_sml recursive checking *)
(*        val _ = case (result1)
                    of NONE => ()
                     | SOME msg => raise Cover.Error (Paths.wrap (r, "Relational coverage succeeds, funcational fails:\n This indicates a bug in the functional checker.\n[Functional] " ^ msg))
*)
(* %total does not auto-freeze, since the predicate must already be frozen *)
let (T, rrs) = ReconThm.tdeclTotDecl lterm in let La = Thm.installTotal (T, rrs) in let _ = map Total.install La in let _ = try map Total.checkFam La with Total.Error (msg) -> raise (Total.Error (msg)) | (* include region and file *)
 | Cover.Error (msg) -> raise (Cover.Error (Paths.wrap (r, msg))) | (*                     | Cover.Error (msg) => covererror (result1, msg)  disabled -cs Thu Jan 29 16:35:13 2004 *)
 | Reduces.Error (msg) -> raise (Reduces.Error (msg)) | (* includes filename *)
 | Subordinate.Error (msg) -> raise (Subordinate.Error (Paths.wrap (r, msg))) in let _ = if ! Global.chatter >= 3 then msg ("%total " ^ ThmPrint.tDeclToString T ^ ".\n") else () in  () ) | (fileName, (Parser.TerminatesDec lterm, _)) -> ( (* allow re-declaration since safe? *)
(* Thu Mar 10 13:45:42 2005 -fp *)
(*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookup a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare termination order for_sml frozen constant "
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *)
let (T, rrs) = ReconThm.tdeclTotDecl lterm in let ThmSyn.TDecl (_, ThmSyn.Callpats (callpats)) = T in let La = Thm.installTerminates (T, rrs) in let _ = map (Timers.time Timers.terminate Reduces.checkFam) La in let _ = if ! Global.autoFreeze then (Subordinate.freeze La; ()) else () in let _ = if ! Global.chatter >= 3 then msg ("%terminates " ^ ThmPrint.tDeclToString T ^ ".\n") else () in  () ) | (fileName, (Parser.ReducesDec lterm, _)) -> ( (* allow re-declaration since safe? *)
(* Thu Mar 10 14:06:13 2005 -fp *)
(*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookupROrder a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare reduction order for_sml frozen constant "
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *)
(*  -bp6/12/99.   *)
let (R, rrs) = ReconThm.rdeclTorDecl lterm in let ThmSyn.RDecl (_, ThmSyn.Callpats (callpats)) = R in let La = Thm.installReduces (R, rrs) in let _ = map (Timers.time Timers.terminate Reduces.checkFamReduction) La in let _ = if ! Global.autoFreeze then (Subordinate.freeze La; ()) else () in let _ = if ! Global.chatter >= 3 then msg ("%reduces " ^ ThmPrint.rDeclToString R ^ ".\n") else () in  () ) | (fileName, (Parser.TabledDec tdecl, _)) -> ( (*  -bp6/12/99.   *)
let (T, r) = ReconThm.tableddeclTotabledDecl tdecl in let La = Thm.installTabled T in let _ = if ! Global.chatter >= 3 then msg ("%tabled " ^ ThmPrint.tabledDeclToString T ^ ".\n") else () in  () ) | (fileName, (Parser.KeepTableDec tdecl, _)) -> ( let (T, r) = ReconThm.keepTabledeclToktDecl tdecl in let La = Thm.installKeepTable T in let _ = if ! Global.chatter >= 3 then msg ("%keeptabled " ^ ThmPrint.keepTableDeclToString T ^ ".\n") else () in  () ) | (fileName, (Parser.TheoremDec tdec, r)) -> ( let Tdec = ReconThm.theoremDecToTheoremDec tdec in let _ = ReconTerm.checkErrors (r) in let (GBs, E) = ThmSyn.theoremDecToConDec (Tdec, r) in let _ = FunSyn.labelReset () in let _ = List.foldr (fun ((G1, G2), k) -> FunSyn.labelAdd (FunSyn.LabelDec (Int.toString k, FunSyn.ctxToList G1, FunSyn.ctxToList G2))) 0 GBs in let cid = installConDec IntSyn.Ordinary (E, (fileName, None), r) in let MS = ThmSyn.theoremDecToModeSpine (Tdec, r) in let _ = ModeTable.installMode (cid, MS) in let _ = if ! Global.chatter >= 3 then msg ("%theorem " ^ Print.conDecToString E ^ "\n") else () in  () ) | (fileName, (Parser.ProveDec lterm, r)) -> ( (* La is the list of type constants *)
(* times itself *)
let (ThmSyn.PDecl (depth, T), rrs) = ReconThm.proveToProve lterm in let La = Thm.installTerminates (T, rrs) in let _ = if ! Global.chatter >= 3 then msg ("%prove " ^ (Int.toString depth) ^ " " ^ (ThmPrint.tDeclToString T) ^ ".\n") else () in let _ = Prover.init (depth, La) in let _ = if ! Global.chatter >= 3 then map (fun a -> msg ("%mode " ^ (ModePrint.modeToString (a, valOf (ModeTable.modeLookup a))) ^ ".\n")) La(* mode must be declared!*)
 else [()] in let _ = try Prover.auto () with Prover.Error msg -> raise (Prover.Error (Paths.wrap (joinregion rrs, msg))) in let _ = if ! Global.chatter >= 3 then msg ("%QED\n") else () in  (Prover.install (fun E -> installConDec IntSyn.Ordinary (E, (fileName, None), r)); Skolem.install La) ) | (fileName, (Parser.EstablishDec lterm, r)) -> ( (* La is the list of type constants *)
(* times itself *)
let (ThmSyn.PDecl (depth, T), rrs) = ReconThm.establishToEstablish lterm in let La = Thm.installTerminates (T, rrs) in let _ = if ! Global.chatter >= 3 then msg ("%prove " ^ (Int.toString depth) ^ " " ^ (ThmPrint.tDeclToString T) ^ ".\n") else () in let _ = Prover.init (depth, La) in let _ = if ! Global.chatter >= 3 then map (fun a -> msg ("%mode " ^ (ModePrint.modeToString (a, valOf (ModeTable.modeLookup a))) ^ ".\n")) La(* mode must be declared!*)
 else [()] in let _ = try Prover.auto () with Prover.Error msg -> raise (Prover.Error (Paths.wrap (joinregion rrs, msg))) in  Prover.install (fun E -> installConDec IntSyn.Ordinary (E, (fileName, None), r)) ) | (fileName, (Parser.AssertDec aterm, _)) -> ( (* La is the list of type constants *)
let _ = if not (! Global.unsafe) then raise (ThmSyn.Error "%assert not safe: Toggle `unsafe' flag") else () in let (cp, rrs) = ReconThm.assertToAssert aterm in let La = map (fun (c, P) -> c) L in let _ = if ! Global.chatter >= 3 then msg ("%assert " ^ (ThmPrint.callpatsToString cp) ^ ".\n") else () in let _ = if ! Global.chatter >= 3 then map (fun a -> msg ("%mode " ^ (ModePrint.modeToString (a, valOf (ModeTable.modeLookup a))) ^ ".\n")) La(* mode must be declared!*)
 else [()] in  Skolem.install La ) | (fileName, (Parser.WorldDec wdecl, _)) -> ( let (ThmSyn.WDecl (qids, cp), rs) = ReconThm.wdeclTowDecl wdecl in let _ = ListPair.app (fun ((a, _), r) -> if Subordinate.frozen [a] then raise (WorldSyn.Error (Paths.wrapLoc (Paths.Loc (fileName, r), "Cannot declare worlds for_sml frozen family " ^ Names.qidToString (Names.constQid a)))) else ()) (cpa, rs) in let rec flatten = function ([], F) -> F | ((cid :: L), F) -> (match IntSyn.sgnLookup cid with IntSyn.BlockDec _ -> flatten L (cid :: F) | IntSyn.BlockDef (_, _, L') -> flatten (L @ L') F) in let W = Tomega.Worlds (flatten (List.map (fun qid -> match Names.constLookup qid with None -> raise (Names.Error ("Undeclared label " ^ Names.qidToString (valOf (Names.constUndef qid)) ^ ".")) | Some cid -> cid) qids) []) in let _ = try List.app (fun (a, _) -> WorldSyn.install (a, W)) cpa with WorldSyn.Error (msg)(* error location inaccurate here *)
 -> raise (WorldSyn.Error (Paths.wrapLoc (Paths.Loc (fileName, joinregions rs), msg))) in let _ = if ! Global.autoFreeze then (Subordinate.freeze (List.map (fun (a, _) -> a) cpa); ()) else () in let _ = if ! Global.chatter >= 3 then msg ("%worlds " ^ Print.worldsToString W ^ " " ^ ThmPrint.callpatsToString cp ^ ".\n") else () in  (Timers.time Timers.worlds (map (fun (a, _) -> WorldSyn.worldcheck W a)) cpa; ()(*if !Global.doubleCheck
             then (map (fn (a,_) => Worldify.worldify a) cpa; ())
           else  ()  --cs Sat Aug 27 22:04:29 2005 *)
) ) | (fileName, declr) -> install1WithSig (fileName, None, declr) | (fileName, declr) -> install1WithSig (fileName, None, declr) | (fileName, declr) -> install1WithSig (fileName, None, declr) | (fileName, declr) -> install1WithSig (fileName, None, declr) | (fileName, (Parser.Use name, r)) -> (match ! context with None -> CSManager.useSolver (name) | _ -> raise (ModSyn.Error (Paths.wrap (r, "%use declaration needs to be at top level"))))
and install1WithSig = function (fileName, moduleOpt, (Parser.SigDef sigdef, r)) -> ( (* FIX: should probably time this -kw *)
let (idOpt, module_, wherecls) = ReconModule.sigdefToSigdef (sigdef, moduleOpt) in let module' = foldl (fun (inst, module_) -> ReconModule.moduleWhere (module_, inst)) module_ wherecls in let name = try (match idOpt with Some id -> (ModSyn.installSigDef (id, module'); id) | None -> "_"(* anonymous *)
) with ModSyn.Error msg -> raise (ModSyn.Error (Paths.wrap (r, msg))) in let _ = if ! Global.chatter >= 3 then msg ("%sig " ^ name ^ " = { ... }.\n") else () in  () ) | (fileName, moduleOpt, (Parser.StructDec structdec, r)) -> (match ReconModule.structdecToStructDec (structdec, moduleOpt) with ReconModule.StructDec (idOpt, module_, wherecls) -> ( let module' = foldl (fun (inst, module_) -> ReconModule.moduleWhere (module_, inst)) module_ wherecls in let name = (match idOpt with Some id -> (installStrDec (IntSyn.StrDec (id, None), module', r, false); id) | None -> "_"(* anonymous *)
) in let _ = if ! Global.chatter = 3 then msg ("%struct " ^ name ^ " : { ... }.\n") else () in  () ) | ReconModule.StructDef (idOpt, mid) -> ( let ns = Names.getComponents mid in let module_ = ModSyn.abstractModule (ns, Some mid) in let name = (match idOpt with Some id -> (installStrDec (IntSyn.StrDec (id, None), module_, r, true); id) | None -> "_"(* anonymous *)
) in let _ = if ! Global.chatter = 3 then msg ("%struct " ^ name ^ " = " ^ Names.qidToString (Names.structQid mid) ^ ".\n") else () in  () )) | (fileName, moduleOpt, (Parser.Include sigexp, r)) -> ( let (module_, wherecls) = ReconModule.sigexpToSigexp (sigexp, moduleOpt) in let module' = foldl (fun (inst, module_) -> ReconModule.moduleWhere (module_, inst)) module_ wherecls in let _ = includeSig (module', r, false) in let _ = if ! Global.chatter = 3 then msg ("%include { ... }.\n") else () in  () ) | (fileName, None, (Parser.Open strexp, r)) -> ( let mid = ReconModule.strexpToStrexp strexp in let ns = Names.getComponents mid in let module_ = ModSyn.abstractModule (ns, Some mid) in let _ = includeSig (module_, r, true) in let _ = if ! Global.chatter = 3 then msg ("%open " ^ Names.qidToString (Names.structQid mid) ^ ".\n") else () in  () )
let rec installSubsig (fileName, s)  = ( (* val _ = ModeTable.resetFrom mark *)
(* val _ = Total.resetFrom mark *)
(* val _ = Subordinate.resetFrom mark (* ouch! *) *)
(* val _ = Reduces.resetFrom mark *)
(* Origins, CompSyn, FunSyn harmless? -kw *)
(* val _ = IntSyn.resetFrom (mark, markStruct)
             FIX: DON'T eliminate out-of-scope cids for_sml now -kw *)
let namespace = Names.newNamespace () in let (mark, markStruct) = IntSyn.sgnSize () in let markSigDef = ModSyn.sigDefSize () in let oldContext = ! context in let _ = context := Some namespace in let _ = if ! Global.chatter >= 4 then msg ("\n% begin subsignature\n") else () in let rec install s  = install' ((Timers.time Timers.parsing S.expose) s)
and install' = function (S.Cons ((Parser.BeginSubsig, _), s')) -> install (installSubsig (fileName, s')) | (S.Cons ((Parser.EndSubsig, _), s')) -> s' | (S.Cons (declr, s')) -> (install1 (fileName, declr); install s') in let result = try ( let s' = install s in let module_ = ModSyn.abstractModule (namespace, None) in let _ = if ! Global.chatter >= 4 then msg ("% end subsignature\n\n") else () in  Value (module_, s') ) with exn -> Exception exn in let _ = context := oldContext in let _ = Names.resetFrom (mark, markStruct) in let _ = Index.resetFrom mark in let _ = IndexSkolem.resetFrom mark in let _ = ModSyn.resetFrom markSigDef in  match result with Value (module_, s') -> ( let S.Cons (declr, s'') = (Timers.time Timers.parsing S.expose) s' in  install1WithSig (fileName, Some module_, declr); s'' ) | Exception exn -> raise (exn) )
(* loadFile (fileName) = status
       reads and processes declarations from fileName in order, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)

let rec loadFile (fileName)  = handleExceptions 0 fileName (withOpenIn fileName) (fun instream -> ( let _ = ReconTerm.resetErrors fileName in let rec install s  = install' ((Timers.time Timers.parsing S.expose) s)
and install' = function (S.Empty) -> OK | (S.Cons ((Parser.BeginSubsig, _), s')) -> install (installSubsig (fileName, s')) | (S.Cons (decl, s')) -> (install1 (fileName, decl); install s') in  install (Parser.parseStream instream) ))
(* loadString (str) = status
       reads and processes declarations from str, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)

let rec loadString str  = handleExceptions 0 "string" (fun () -> ( let _ = ReconTerm.resetErrors "string" in let rec install s  = install' ((Timers.time Timers.parsing S.expose) s)
and install' = function (S.Empty) -> OK | (S.Cons ((Parser.BeginSubsig, _), s')) -> (installSubsig ("string", s'); install s') | (S.Cons (decl, s')) -> (install1 ("string", decl); install s') in  install (Parser.parseStream (TextIO.openString str)) )) ()
(* Interactive Query Top Level *)

let rec sLoop ()  = if Solve.qLoop () then OK else ABORT
let rec topLoop ()  = match (handleExceptions 0 "stdIn" sLoop) ()(* "stdIn" as fake fileName *)
 with ABORT -> topLoop () | OK -> ()
(* top () = () starts interactive query loop *)

let rec top ()  = topLoop ()
let rec installCSMDec (conDec, optFixity, mdecL)  = ( (* put a more reasonable region here? -kw *)
let _ = ModeCheck.checkD (conDec, "%use", None) in let cid = installConDec IntSyn.FromCS (conDec, ("", None), Paths.Reg (0, 0)) in let _ = if ! Global.chatter >= 3 then msg (Print.conDecToString (conDec) ^ "\n") else () in let _ = (match optFixity with Some (fixity) -> (Names.installFixity (cid, fixity); if ! Global.chatter >= 3 then msg ((if ! Global.chatter >= 4 then "%" else "") ^ Names.Fixity.toString fixity ^ " " ^ Names.qidToString (Names.constQid cid) ^ ".\n") else ()) | None -> ()) in let _ = List.app (fun mdec -> ModeTable.installMmode (cid, mdec)) mdecL in  cid )
let _ = CSManager.setInstallFN (installCSMDec)
(* reset () = () clears all global tables, including the signature *)

let rec reset ()  = (IntSyn.sgnReset (); Names.reset (); Origins.reset (); ModeTable.reset (); UniqueTable.reset (); (* -fp Wed Mar  9 20:24:45 2005 *)
Index.reset (); IndexSkolem.reset (); Subordinate.reset (); Total.reset (); (* -fp *)
WorldSyn.reset (); (* -fp *)
Reduces.reset (); (* -bp *)
TabledSyn.reset (); (* -bp *)
FunSyn.labelReset (); CompSyn.sProgReset (); (* necessary? -fp; yes - bp*)
CompSyn.detTableReset (); (*  -bp *)
Compile.sProgReset (); (* resetting substitution trees *)
ModSyn.reset (); CSManager.resetSolvers (); context := None)
let rec readDecl ()  = handleExceptions 0 "stdIn" (fun () -> ( let _ = ReconTerm.resetErrors "stdIn" in let rec install s  = install' ((Timers.time Timers.parsing S.expose) s)
and install' = function (S.Empty) -> ABORT | (S.Cons ((Parser.BeginSubsig, _), s')) -> (installSubsig ("stdIn", s'); OK) | (S.Cons (decl, s')) -> (install1 ("stdIn", decl); OK) in  install (Parser.parseStream TextIO.stdIn) )) ()
(* decl (id) = () prints declaration of constant id *)

let rec decl (id)  = (match Names.stringToQid id with None -> (msg (id ^ " is not a well-formed qualified identifier\n"); ABORT) | Some qid -> (match Names.constLookup qid with None -> (msg (Names.qidToString (valOf (Names.constUndef qid)) ^ " has not been declared\n"); ABORT) | Some cid -> decl' (cid)))
and decl' (cid)  = ( (* val fixity = Names.getFixity (cid) *)
(* can't get name preference right now *)
(* val mode = ModeTable.modeLookup (cid) *)
(* can't get termination declaration *)
let conDec = IntSyn.sgnLookup (cid) in  msg (Print.conDecToString conDec ^ "\n"); OK )
(* Support tracking file modification times for_sml smart re-appending. *)

module ModFile : sig
  type mfile
  val create : string -> mfile
  val fileName : mfile -> string
  val editName : (string -> string) -> mfile -> mfile
  val modified : mfile -> bool
  val makeModified : mfile -> unit
  val makeUnmodified : mfile -> unit

end = struct type mfile = string * Time.time option ref
let rec create file  = (file, ref None)
let rec fileName (file, _)  = file
let rec editName edit (file, mtime)  = (edit file, mtime)
let rec modified = function (_, { contents = None }) -> true | (file, { contents = (Some time) }) -> (match Time.compare (time, OS.FileSys.modTime file) with Eq -> false | _ -> true)
let rec makeModified (_, mtime)  = mtime := None
let rec makeUnmodified (file, mtime)  = mtime := Some (OS.FileSys.modTime file)
 end
(* config = ["fileName1",...,"fileName<n>"] *)

(* Files will be read in the order given! *)

module Config = struct (* A configuration (pwdir, sources) consists of an absolute directory
         pwdir and a list of source file names (which are interpreted
         relative to pwdir) along with their modification times.
         pwdir will be the current working directory
         when a configuration is loaded, which may not be the
         directory in which the configuration file is located.

         This representation allows shorter file names in chatter and
         error messages.
      *)

type config = string * ModFile.mfile list
(* suffix of configuration files: "cfg" by default *)

let suffix = ref "cfg"
(* mkRel transforms a relative path into an absolute one
               by adding the specified prefix. If the path is already
               absolute, no prefix is added to it.
            *)

let rec mkRel (prefix, path)  = OS.Path.mkCanonical (if OS.Path.isAbsolute path then path else OS.Path.concat (prefix, path))
(* more efficient recursive version  Sat 08/26/2002 -rv *)

let rec read config  = ( (* appendUniq (list1, list2) appends list2 to list1, removing all
               elements of list2 which are already in list1.
            *)
(* isConfig (item) is true iff item has the suffix of a
               configuration file.
            *)
(* fromUnixPath path transforms path (assumed to be in Unix form)
               to the local OS conventions.
            *)
let rec appendUniq (l1, l2)  = ( let rec appendUniq' = function (x :: l2) -> if List.exists (fun y -> x = y) l1 then appendUniq' l2 else x :: appendUniq' (l2) | [] -> List.rev l1 in  List.rev (appendUniq' (List.rev l2)) ) in let rec isConfig item  = ( let suffix_size = (String.size (! suffix)) + 1 in let suffix_start = (String.size item) - suffix_size in  (suffix_start >= 0) && (String.substring (item, suffix_start, suffix_size) = ("." ^ ! suffix)) ) in let rec fromUnixPath path  = ( let vol = OS.Path.getVolume config in let isAbs = String.isPrefix "/" path in let arcs = String.tokens (fun c -> c = '/') path in  OS.Path.toString {isAbs = isAbs; vol = vol; arcs = arcs} ) in let rec read' (sources, configs) config  = withOpenIn config (fun instream -> ( let {dir = configDir; file = _} = OS.Path.splitDirFile config in let rec parseItem (sources, configs) item  = if isConfig item then if List.exists (fun config' -> item = config') configs then (sources, configs)(* we have already read this one *)
 else read' (sources, item :: configs) item else if List.exists (fun source' -> item = source') sources then (sources, configs)(* we have already collected this one *)
 else (sources @ [item], configs) in let rec parseLine (sources, configs) line  = if Substring.isEmpty line(* end of file *)
 then (sources, configs) else ( let line' = Substring.dropl Char.isSpace line in  parseLine' (sources, configs) line' )
and parseLine' (sources, configs) line  = if Substring.isEmpty line || (* empty line *)
 || Substring.sub (line, 0) = '%'(* comment *)
 then parseStream (sources, configs) else ( let line' = Substring.string (Substring.takel (not o Char.isSpace) line) in let item = mkRel (configDir, fromUnixPath line') in  parseStream (parseItem (sources, configs) item) )
and parseStream (sources, configs)  = ( let line = Compat.Substring.full (Compat.inputLine97 instream) in  parseLine (sources, configs) line ) in  parseStream (sources, configs) )) in let pwdir = OS.FileSys.getDir () in  (pwdir, List.map ModFile.create (1 (read' ([], [config]) config)))(*
            handle IO.Io (ioError) => (abortIO (configFile, ioError); raise IO.io (ioError))
          *)
 )
(* Read a config file s but omit everything that is already in config c
         XXX: naive and inefficient implementation *)

let rec readWithout (s, c)  = ( let (d, fs) = read s in let (d', fs') = c in let fns' = map (fun m -> mkRel (d', ModFile.fileName m)) fs' in let rec redundant m  = ( let n = mkRel (d, ModFile.fileName m) in  List.exists (fun n' -> n = n') fns' ) in  (d, List.filter (not o redundant) fs) )
let rec loadAbort = function (mfile, OK) -> ( let status = loadFile (ModFile.fileName mfile) in  match status with OK -> ModFile.makeUnmodified mfile | _ -> (); status ) | (_, ABORT) -> ABORT
(* load (config) = Status
         resets the global signature and then reads the files in config
         in order, stopping at the first error.
      *)

let rec load (config)  = (reset (); List.app ModFile.makeModified sources; append (config))
and append (pwdir, sources)  = ( let rec fromFirstModified = function [] -> [] | (sources) -> if ModFile.modified x then sources else fromFirstModified xs in let rec mkAbsolute p  = Compat.OS.Path.mkAbsolute {path = p; relativeTo = pwdir} in let sources' = (* allow shorter messages if safe *)
if pwdir = OS.FileSys.getDir () then sources else List.map (ModFile.editName mkAbsolute) sources in let sources'' = fromFirstModified sources' in  List.foldl loadAbort OK sources'' )
let rec define (sources)  = (OS.FileSys.getDir (), List.map ModFile.create sources)
 end
(* structure Config *)

(* make (configFile)
       read and then load configuration from configFile
    *)

let rec make (fileName)  = Config.load (Config.read fileName)
(* re-exporting environment parameters and utilities defined elsewhere *)

module Print : sig
  val implicit : bool ref
(* false, print implicit args *)
  val printInfix : bool ref
(* false, print fully explicit form infix when possible *)
  val depth : int option ref
(* NONE, limit print depth *)
  val length : int option ref
(* NONE, limit argument length *)
  val indent : int ref
(* 3, indentation of subterms *)
  val width : int ref
(* 80, line width *)
  val noShadow : bool ref
(* if true, don't print shadowed "%const%" *)
  val sgn : unit -> unit
(* print signature *)
  val prog : unit -> unit
(* print program *)
  val subord : unit -> unit
(* print subordination relation *)
  val def : unit -> unit
(* print information about definitions *)
  val domains : unit -> unit
(* print available constraint domains *)
  module TeX : (* print in TeX format *)
sig
  val sgn : unit -> unit
(* print signature *)
  val prog : unit -> unit
(* print program *)

end

end = struct let implicit = Print.implicit
let printInfix = Print.printInfix
let depth = Print.printDepth
let length = Print.printLength
let indent = Print.Formatter.Indent
let width = Print.Formatter.Pagewidth
let noShadow = Print.noShadow
let rec sgn ()  = Print.printSgn ()
let rec prog ()  = ClausePrint.printSgn ()
let rec subord ()  = Subordinate.show ()
let rec def ()  = Subordinate.showDef ()
let rec domains ()  = msg (CSInstaller.version)
module TeX = struct let rec sgn ()  = printSgnTeX ()
let rec prog ()  = printProgTeX ()
 end
 end
module Trace : sig
  type 'a spec = None | Some of 'a list | All
(* trace all clauses and families *)
  val trace : string spec -> unit
(* clauses and families *)
  val break : string spec -> unit
(* clauses and families *)
  val detail : int ref
(* 0 = none, 1 = default, 2 = unify *)
  val show : unit -> unit
(* show trace, break, and detail *)
  val reset : unit -> unit
(* reset trace, break, and detail *)

end = Trace
module Timers : sig
  val show : unit -> unit
(* show and reset timers *)
  val reset : unit -> unit
(* reset timers *)
  val check : unit -> unit
(* display, but not no reset *)

end = Timers
module OS : sig
  val chDir : string -> unit
(* change working directory *)
  val getDir : unit -> string
(* get working directory *)
  val exit : unit -> unit
(* exit Twelf and ML *)

end = struct let chDir = OS.FileSys.chDir
let getDir = OS.FileSys.getDir
let rec exit ()  = OS.Process.exit (OS.Process.success)
 end
module Compile : sig
  optCompSyn.opt
  val optimize : opt ref

end = struct optCompSyn.opt
let optimize = CompSyn.optimize
 end
module Recon : sig
  traceModeReconTerm.traceMode
  val trace : bool ref
  val traceMode : traceMode ref

end = struct traceModeReconTerm.traceMode
let trace = ReconTerm.trace
let traceMode = ReconTerm.traceMode
 end
module Recon : sig
  traceModeReconTerm.traceMode
  val trace : bool ref
  val traceMode : traceMode ref

end = struct traceModeReconTerm.traceMode
let trace = ReconTerm.trace
let traceMode = ReconTerm.traceMode
 end
module Prover : sig
(* F=Filling, R=Recursion, S=Splitting *)
  strategyMetaGlobal.strategy
(* FRS or RFS *)
  val strategy : strategy ref
(* FRS, strategy used for_sml %prove *)
  val maxSplit : int ref
(* 2, bound on splitting  *)
  val maxRecurse : int ref
(* 10, bound on recursion *)

end = struct strategyMetaGlobal.strategy
(* FRS or RFS *)

let strategy = MetaGlobal.strategy
let maxSplit = MetaGlobal.maxSplit
let maxRecurse = MetaGlobal.maxRecurse
 end
let chatter : int ref = Global.chatter
let doubleCheck : bool ref = Global.doubleCheck
let unsafe : bool ref = Global.unsafe
let autoFreeze : bool ref = Global.autoFreeze
let timeLimit : Time.time option ref = Global.timeLimit
statusstatus
let reset = reset
let loadFile = loadFile
let loadString = loadString
let readDecl = readDecl
let decl = decl
let top = top
module Config : sig
  type config
(* configuration *)
  val suffix : string ref
(* suffix of configuration files *)
  val read : string -> config
(* read configuration from config file *)
  val readWithout : string * config -> config
(* read config file, minus contents of another *)
  val load : config -> status
(* reset and load configuration *)
  val append : config -> status
(* load configuration (w/o reset) *)
  val define : string list -> config
(* explicitly define configuration *)

end = Config
let make = make
let version = Version.version_string
module Table : sig
  strategyTableParam.strategy
  val strategy : strategy ref
  val strengthen : bool ref
  val resetGlobalTable : unit -> unit
  val top : unit -> unit

end = struct strategyTableParam.strategy
let strategy = TableParam.strategy
let strengthen = TableParam.strengthen
let resetGlobalTable = TableParam.resetGlobalTable
(* top () = () starts interactive query loop *)

let rec top ()  = ( let rec sLoopT ()  = if Solve.qLoopT () then OK else ABORT in let rec topLoopT ()  = match (handleExceptions 0 "stdIn" sLoopT) ()(* "stdIn" as fake fileName *)
 with ABORT -> topLoopT () | OK -> () in  topLoopT () )
 end
(* local *)

 end


(* functor Twelf *)

