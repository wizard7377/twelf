(* Reconstruct signature entries *)


(* Author: Frank Pfenning *)


(* Modified: Roberto Virga, Jeff Polakow *)


module ReconConDec (Global : GLOBAL) (Names : NAMES) (Abstract : ABSTRACT) (ReconTerm' : RECON_TERM) (Constraints : CONSTRAINTS) (Strict : STRICT) (TypeCheck : TYPECHECK) (Timers : TIMERS) (Print : PRINT) (Msg : MSG) : RECON_CONDEC = struct (*! structure IntSyn = IntSyn' !*)

(*! structure Paths = Paths' !*)

module ExtSyn = ReconTerm'
exception Error of string
(* error (r, msg) raises a syntax error within region r with text msg *)

let rec error (r, msg)  = raise (Error (Paths.wrap (r, msg)))
type name = string
(* Constant declarations *)

type condec = Condec of name * ExtSyn.term | Condef of name option * ExtSyn.term * ExtSyn.term option | Blockdef of string * string list * string list | Blockdec of name * ExtSyn.dec list * ExtSyn.dec list
(* condecToConDec (condec, r) = (SOME(cd), SOME(ocd))
     if condec is a named constant declaration with occurrence tree ocd,
     NONE if name or occurrence tree is missing

     Free variables in condec are interpreted universally (as FVars)
     then implicit parameters.

     Only works properly when the declaration contains no EVars.
  *)

(* should printing of result be moved to frontend? *)

(* Wed May 20 08:08:50 1998 -fp *)

let rec condecToConDec = function (Condec (name, tm), Paths.Loc (fileName, r), abbFlag) -> ( let _ = Names.varReset IntSyn.Null in let _ = ExtSyn.resetErrors fileName in let ExtSyn.JClass ((V, oc), L) = (Timers.time Timers.recon ExtSyn.recon) (ExtSyn.jclass tm) in let _ = ExtSyn.checkErrors (r) in let (i, V') = try (Timers.time Timers.abstract Abstract.abstractDecImp) V with Abstract.Error (msg) -> raise (Abstract.Error (Paths.wrap (r, msg))) in let cd = Names.nameConDec (IntSyn.ConDec (name, None, i, IntSyn.Normal, V', L)) in let ocd = Paths.dec (i, oc) in let _ = if ! Global.chatter >= 3 then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n") else () in let _ = if ! Global.doubleCheck then (Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni L) else () in  (Some (cd), Some (ocd)) ) | (Condef (optName, tm1, tm2Opt), Paths.Loc (fileName, r), abbFlag) -> ( let _ = Names.varReset IntSyn.Null in let _ = ExtSyn.resetErrors fileName in let f = (match tm2Opt with None -> ExtSyn.jterm tm1 | Some tm2 -> ExtSyn.jof (tm1, tm2)) in let f' = (Timers.time Timers.recon ExtSyn.recon) f in let ((U, oc1), (V, oc2Opt), L) = (match f' with ExtSyn.JTerm ((U, oc1), V, L) -> ((U, oc1), (V, None), L) | ExtSyn.JOf ((U, oc1), (V, oc2), L) -> ((U, oc1), (V, Some oc2), L)) in let _ = ExtSyn.checkErrors (r) in let (i, (U'', V'')) = try (Timers.time Timers.abstract Abstract.abstractDef) (U, V) with Abstract.Error (msg) -> raise (Abstract.Error (Paths.wrap (r, msg))) in let name = match optName with None -> "_" | Some (name) -> name in let ocd = Paths.def (i, oc1, oc2Opt) in let cd = if abbFlag then Names.nameConDec (IntSyn.AbbrevDef (name, None, i, U'', V'', L)) else (Strict.check ((U'', V''), Some (ocd)); (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
(* (case optName of NONE => () | _ => Strict.checkType ((i, V''), SOME(ocd))); *)
(Names.nameConDec (IntSyn.ConDef (name, None, i, U'', V'', L, IntSyn.ancestor U'')))) in let _ = if ! Global.chatter >= 3 then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n") else () in let _ = if ! Global.doubleCheck then ((Timers.time Timers.checking TypeCheck.check) (V'', IntSyn.Uni L); (Timers.time Timers.checking TypeCheck.check) (U'', V'')) else () in let optConDec = match optName with None -> None | Some _ -> Some (cd) in  (optConDec, Some (ocd)) ) | (Blockdec (name, Lsome, Lblock), Paths.Loc (fileName, r), abbFlag) -> ( let rec makectx = function [] -> IntSyn.Null | (D :: L) -> IntSyn.Decl (makectx L, D) in let rec ctxToList = function (IntSyn.Null, acc) -> acc | (IntSyn.Decl (G, D), acc) -> ctxToList (G, D :: acc) in let rec ctxAppend = function (G, IntSyn.Null) -> G | (G, IntSyn.Decl (G', D)) -> IntSyn.Decl (ctxAppend (G, G'), D) in let rec ctxBlockToString (G0, (G1, G2))  = ( let _ = Names.varReset IntSyn.Null in let G0' = Names.ctxName G0 in let G1' = Names.ctxLUName G1 in let G2' = Names.ctxLUName G2 in  Print.ctxToString (IntSyn.Null, G0') ^ "\n" ^ (match G1' with IntSyn.Null -> "" | _ -> "some " ^ Print.ctxToString (G0', G1') ^ "\n") ^ "pi " ^ Print.ctxToString (ctxAppend (G0', G1'), G2') ) in let rec checkFreevars = function (IntSyn.Null, (G1, G2), r) -> () | (G0, (G1, G2), r) -> ( let _ = Names.varReset IntSyn.Null in let G0' = Names.ctxName G0 in let G1' = Names.ctxLUName G1 in let G2' = Names.ctxLUName G2 in  error (r, "Free variables in context block after term reconstruction:\n" ^ ctxBlockToString (G0', (G1', G2'))) ) in let (gsome, gblock) = (makectx Lsome, makectx Lblock) in let r' = (match (ExtSyn.ctxRegion gsome, ExtSyn.ctxRegion gblock) with (Some r1, Some r2) -> Paths.join (r1, r2) | (_, Some r2) -> r2) in let _ = Names.varReset IntSyn.Null in let _ = ExtSyn.resetErrors fileName in let j = ExtSyn.jwithctx (gsome, ExtSyn.jwithctx (gblock, ExtSyn.jnothing)) in let ExtSyn.JWithCtx (Gsome, ExtSyn.JWithCtx (Gblock, _)) = (Timers.time Timers.recon ExtSyn.recon) j in let _ = ExtSyn.checkErrors (r) in let (G0, [Gsome'; Gblock']) = (* closed nf *)
try Abstract.abstractCtxs [Gsome; Gblock] with Constraints.Error (C) -> (raise (error (r', "Constraints remain in context block after term reconstruction:\n" ^ ctxBlockToString (IntSyn.Null, (Gsome, Gblock)) ^ "\n" ^ Print.cnstrsToString C))) in let _ = checkFreevars (G0, (Gsome', Gblock'), r') in let bd = IntSyn.BlockDec (name, None, Gsome', ctxToList (Gblock', [])) in let _ = if ! Global.chatter >= 3 then Msg.message ((Timers.time Timers.printing Print.conDecToString) bd ^ "\n") else () in  (Some bd, None) ) | (Blockdef (name, W), Paths.Loc (fileName, r), abbFlag) -> ( let W' = List.map Names.Qid W in let W'' = (List.map (fun qid -> match Names.constLookup qid with None -> raise (Names.Error ("Undeclared label " ^ Names.qidToString (valOf (Names.constUndef qid)) ^ ".")) | Some cid -> cid) W') in let bd = IntSyn.BlockDef (name, None, W'') in let _ = if ! Global.chatter >= 3 then Msg.message ((Timers.time Timers.printing Print.conDecToString) bd ^ "\n") else () in  (Some bd, None) )
let rec internalInst _  = raise (Match)
let rec externalInst _  = raise (Match)
 end

(* functor ReconConDec *)

