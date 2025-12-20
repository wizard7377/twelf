(* Syntax for_sml elaborated modules *)


(* Author: Kevin Watkins *)


module ModSyn (Global : GLOBAL) (Names' : NAMES) (Origins : ORIGINS) (Whnf : WHNF) (Strict : STRICT) : MODSYN = struct (*! structure IntSyn = IntSyn' !*)

module Names = Names'
(*! structure Paths = Paths' !*)

module I = IntSyn
exception Error of string
type constInfo = ConstInfo of IntSyn.conDec * Names.Fixity.fixity * string list * string list option * (string * Paths.occConDec option)
type structInfo = StructInfo of IntSyn.strDec
(* A module consists of:
     1. a map from cids to constant entries containing
          a. a constant declaration entry (IntSyn.ConDec)
          b. the fixity of the constant
          c. the name preference for_sml the constant (if any)
     2. a map from mids to structure entries containing
          a. a structure declaration entry (IntSyn.StrDec)
          b. the namespace of the structure
     3. the top-level namespace of the module *)

type module = structInfo IntTree.table * constInfo IntTree.table * Names.namespace
type action = IntSyn.cid * (string * Paths.occConDec option) -> unit
type transform = IntSyn.cid * IntSyn.conDec -> IntSyn.conDec
(* invariant: U in nf, result in nf *)

let rec mapExpConsts f U  = ( open IntSyn in let rec trExp = function (Uni L) -> Uni L | (Pi ((D, P), V)) -> Pi ((trDec D, P), trExp V) | (Root (H, S)) -> Root (trHead H, trSpine S) | (Lam (D, U)) -> Lam (trDec D, trExp U) | (U) -> FgnExpStd.Map.apply csfe trExp
and trDec (Dec (name, V))  = Dec (name, trExp V)
and trSpine = function Nil -> Nil | (App (U, S)) -> App (trExp U, trSpine S)
and trHead = function (BVar n) -> BVar n | (Const cid) -> trConst cid | (Skonst cid) -> trConst cid | (Def cid) -> trConst cid | (NSDef cid) -> trConst cid | (FgnConst (csid, condec)) -> FgnConst (csid, mapConDecConsts f condec)
and trConst cid  = ( let cid' = f cid in  match IntSyn.sgnLookup cid' with IntSyn.ConDec _ -> Const cid' | IntSyn.SkoDec _ -> Skonst cid' | IntSyn.ConDef _ -> Def cid' | IntSyn.AbbrevDef _ -> NSDef cid' ) in  Whnf.normalize (trExp U, IntSyn.id) )
and mapConDecConsts = function (f, (IntSyn.ConDec (name, parent, i, status, V, L))) -> IntSyn.ConDec (name, parent, i, status, mapExpConsts f V, L) | (f, (IntSyn.ConDef (name, parent, i, U, V, L, Anc))) -> IntSyn.ConDef (name, parent, i, mapExpConsts f U, mapExpConsts f V, L, Anc) | (f, (IntSyn.AbbrevDef (name, parent, i, U, V, L))) -> IntSyn.AbbrevDef (name, parent, i, mapExpConsts f U, mapExpConsts f V, L) | (f, (IntSyn.SkoDec (name, parent, i, V, L))) -> IntSyn.SkoDec (name, parent, i, mapExpConsts f V, L)
let rec mapStrDecParent f (IntSyn.StrDec (name, parent))  = IntSyn.StrDec (name, f parent)
let rec mapConDecParent = function (f, (IntSyn.ConDec (name, parent, i, status, V, L))) -> IntSyn.ConDec (name, f parent, i, status, V, L) | (f, (IntSyn.ConDef (name, parent, i, U, V, L, Anc))) -> IntSyn.ConDef (name, f parent, i, U, V, L, Anc) | (f, (IntSyn.AbbrevDef (name, parent, i, U, V, L))) -> IntSyn.AbbrevDef (name, f parent, i, U, V, L) | (f, (IntSyn.SkoDec (name, parent, i, V, L))) -> IntSyn.SkoDec (name, f parent, i, V, L)
let rec strictify = function (condec) -> (try (Strict.check ((U, V), None); IntSyn.ConDef (name, parent, i, U, V, IntSyn.Type, IntSyn.ancestor (U))) with Strict.Error _ -> condec) | (condec) -> condec
let rec abbrevify (cid, condec)  = (match condec with I.ConDec (name, parent, i, _, V, L) -> ( let U = Whnf.normalize (I.Root (I.Const cid, I.Nil), I.id) in  I.AbbrevDef (name, parent, i, U, V, L) ) | I.SkoDec (name, parent, i, V, L) -> ( let U = Whnf.normalize (I.Root (I.Skonst cid, I.Nil), I.id) in  I.AbbrevDef (name, parent, i, U, V, L) ) | I.ConDef (name, parent, i, U, V, L, Anc) -> I.AbbrevDef (name, parent, i, U, V, L) | I.AbbrevDef data -> I.AbbrevDef data)
(* In order to install a module, we walk through the mids in preorder,
     assigning global mids and building up a translation map from local
     mids to global mids.  Then we walk through the cids in dependency
     order, assigning global cids, building up a translation map from
     local to global cids, and replacing the cids contained in the terms
     with their global equivalents.

     NOTE that a module might not be closed with respect to the local
     cids; that is, it might refer to global cids not defined by the
     module.  It is a global invariant that such cids will still be in
     scope whenever a module that refers to them is installed. *)

let rec installModule ((structTable, constTable, namespace), topOpt, nsOpt, installAction, transformConDec)  = ( let structMap : IntSyn.mid IntTree.table = IntTree.new_ (0) in let constMap : IntSyn.cid IntTree.table = IntTree.new_ (0) in let rec mapStruct mid  = valOf (IntTree.lookup structMap mid) in let rec mapParent = function None -> topOpt | (Some parent) -> Some (mapStruct parent) in let rec mapConst cid  = (match IntTree.lookup constMap cid with None -> cid | Some cid' -> cid') in let rec doStruct (mid, StructInfo strdec)  = ( let strdec' = mapStrDecParent mapParent strdec in let mid' = IntSyn.sgnStructAdd strdec' in let parent = IntSyn.strDecParent strdec' in let nsOpt = (match parent with None -> nsOpt | Some mid -> Some (Names.getComponents mid)) in let _ = (match nsOpt with Some ns -> Names.insertStruct (ns, mid') | _ -> ()) in let _ = (match parent with None -> Names.installStructName mid' | _ -> ()) in let ns = Names.newNamespace () in let _ = Names.installComponents (mid', ns) in  IntTree.insert structMap (mid, mid') ) in let rec doConst (cid, ConstInfo (condec, fixity, namePrefOpt, origin))  = ( let condec1 = mapConDecParent mapParent condec in let condec2 = mapConDecConsts mapConst condec1 in let condec3 = transformConDec (cid, condec2) in let cid' = IntSyn.sgnAdd condec3 in let parent = IntSyn.conDecParent condec3 in let nsOpt = (match parent with None -> nsOpt | Some mid -> Some (Names.getComponents mid)) in let _ = (match nsOpt with Some ns -> Names.insertConst (ns, cid') | _ -> ()) in let _ = (match parent with None -> Names.installConstName cid' | _ -> ()) in let _ = installAction (cid', origin) in let _ = (match fixity with Names.Fixity.Nonfix -> () | _ -> Names.installFixity (cid', fixity)) in let _ = (match namePrefOpt with None -> () | Some (n1, n2) -> Names.installNamePref (cid', (n1, n2))) in  IntTree.insert constMap (cid, cid') ) in  IntTree.app doStruct structTable; IntTree.app doConst constTable )
let decToDef = strictify o abbrevify
let rec installStruct (strdec, module_, nsOpt, installAction, isDef)  = ( let transformConDec = if isDef then decToDef else (fun (_, condec) -> condec) in let mid = IntSyn.sgnStructAdd strdec in let _ = match nsOpt with Some namespace -> Names.insertStruct (namespace, mid) | _ -> () in let _ = Names.installStructName mid in let ns = Names.newNamespace () in let _ = Names.installComponents (mid, ns) in  installModule (module_, Some mid, None, installAction, transformConDec) )
let rec installSig (module_, nsOpt, installAction, isDef)  = ( let transformConDec = if isDef then decToDef else (fun (_, condec) -> condec) in  installModule (module_, None, nsOpt, installAction, transformConDec) )
let rec abstractModule (namespace, topOpt)  = ( let structTable : structInfo IntTree.table = IntTree.new_ (0) in let constTable : constInfo IntTree.table = IntTree.new_ (0) in let mapParent = (match topOpt with None -> (fun parent -> parent) | Some mid -> (fun Some mid' -> if mid = mid' then None else Some mid')) in let rec doStruct (_, mid)  = ( let strdec = IntSyn.sgnStructLookup mid in let strdec' = mapStrDecParent mapParent strdec in let ns = Names.getComponents mid in  IntTree.insert structTable (mid, StructInfo strdec'); doNS ns )
and doConst (_, cid)  = ( let condec = IntSyn.sgnLookup cid in let condec' = mapConDecParent mapParent condec in let fixity = Names.getFixity cid in let namePref = Names.getNamePref cid in let origin = Origins.originLookup cid in  IntTree.insert constTable (cid, ConstInfo (condec', fixity, namePref, origin)) )
and doNS ns  = (Names.appStructs doStruct ns; Names.appConsts doConst ns) in  doNS namespace; (structTable, constTable, namespace) )
let rec instantiateModule (module_, transform)  = ( let transformConDec = transform namespace in let mid = IntSyn.sgnStructAdd (IntSyn.StrDec ("wheresubj", None)) in let ns = Names.newNamespace () in let _ = Names.installComponents (mid, ns) in let _ = installModule (module_, Some mid, None, fun _ -> (), transformConDec) in  abstractModule (ns, Some mid) )
let defList : string list ref = ref []
let defCount : int ref = ref 0
let defs : module HashTable.table = HashTable.new_ (4096)
let rec defsClear ()  = HashTable.clear defs
let defsInsert = HashTable.insertShadow defs
let defsLookup = HashTable.lookup defs
let defsDelete = HashTable.delete defs
let rec reset ()  = (defList := []; defCount := 0; defsClear ())
let rec resetFrom mark  = ( let rec ct (l, i)  = if i <= mark then l else ( let h :: t = l in  defsDelete h; ct (t, i - 1) ) in  defList := ct (! defList, ! defCount); defCount := mark )
let rec sigDefSize ()  = ! defCount
let rec installSigDef (id, module_)  = (match defsInsert (id, module_) with None -> (defList := id :: (! defList); defCount := ! defCount + 1) | Some entry -> (raise (Error ("Shadowing: A signature named " ^ id ^ "\nhas already been declared")); defsInsert entry; ()))
let lookupSigDef = defsLookup
 end
