(* Syntax for elaborated modules *)
(* Author: Kevin Watkins *)

module ModSyn
  (Global : GLOBAL)
   (*! module IntSyn' : INTSYN !*)
   module Names' : NAMES
   (*! sharing Names'.IntSyn = IntSyn' !*)
   (*! module Paths' : PATHS !*)
   (Origins : ORIGINS)
   (*! sharing Origins.Paths = Paths' !*)
   (Whnf : WHNF)
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   (Strict : STRICT)
   (*! sharing Strict.IntSyn = IntSyn' !*)
   (IntTree : TABLE with type key = int)
   (HashTable : TABLE with type key = string))
  : MODSYN =
struct

  (*! module IntSyn = IntSyn' !*)
  module Names = Names'
  (*! module Paths = Paths' !*)

  module I = IntSyn

  exception Error of string

  type constInfo =
      ConstInfo of IntSyn.ConDec * Names.Fixity.fixity * (string list * string list) option * (string * Paths.occConDec option)

  type structInfo =
      StructInfo of IntSyn.StrDec

  (* A module consists of:
     1. a map from cids to constant entries containing
          a. a constant declaration entry (IntSyn.ConDec)
          b. the fixity of the constant
          c. the name preference for the constant (if any)
     2. a map from mids to module entries containing
          a. a module declaration entry (IntSyn.StrDec)
          b. the namespace of the module
     3. the top-level namespace of the module *)

  type module =
      StructInfo IntTree.Table * ConstInfo IntTree.Table * Names.namespace

  type action = IntSyn.cid * (string * Paths.occConDec option) -> unit
  type transform = IntSyn.cid * IntSyn.ConDec -> IntSyn.ConDec

  (* invariant: U in nf, result in nf *)
  let rec mapExpConsts f U =
      let
        open IntSyn

        let rec trExp = function (Uni L) -> Uni L
          | (Pi ((D, P), V)) -> Pi ((trDec D, P), trExp V)
          | (Root (H, S)) -> Root (trHead H, trSpine S)
          | (Lam (D, U)) -> Lam (trDec D, trExp U)
          | (U as FgnExp csfe) -> FgnExpStd.Map.apply csfe trExp

        and trDec (Dec (name, V)) = Dec (name, trExp V)

        and trSpine Nil = Nil
          | trSpine (App (U, S)) = App (trExp U, trSpine S)

        and trHead (BVar n) = BVar n
          | trHead (Const cid) = trConst cid
          | trHead (Skonst cid) = trConst cid
          | trHead (Def cid) = trConst cid
          | trHead (NSDef cid) = trConst cid
          | trHead (FgnConst (csid, condec)) =
              FgnConst (csid, mapConDecConsts f condec)

        and trConst cid =
            let
              let cid' = f cid
            in
              case IntSyn.sgnLookup cid'
                of IntSyn.ConDec _ => Const cid'
                 | IntSyn.SkoDec _ => Skonst cid'
                 | IntSyn.ConDef _ => Def cid'
                 | IntSyn.AbbrevDef _ => NSDef cid'
            end
      in
        Whnf.normalize (trExp U, IntSyn.id)
      end

  and mapConDecConsts f (IntSyn.ConDec (name, parent, i, status, V, L)) =
        IntSyn.ConDec (name, parent, i, status, mapExpConsts f V, L)
    | mapConDecConsts f (IntSyn.ConDef (name, parent, i, U, V, L, Anc)) =
        IntSyn.ConDef (name, parent, i, mapExpConsts f U,
                       mapExpConsts f V, L, Anc) (* reconstruct Anc?? -fp *)
    | mapConDecConsts f (IntSyn.AbbrevDef (name, parent, i, U, V, L)) =
        IntSyn.AbbrevDef (name, parent, i, mapExpConsts f U,
                          mapExpConsts f V, L)
    | mapConDecConsts f (IntSyn.SkoDec (name, parent, i, V, L)) =
        IntSyn.SkoDec (name, parent, i, mapExpConsts f V, L)

  let rec mapStrDecParent f (IntSyn.StrDec (name, parent)) =
        IntSyn.StrDec (name, f parent)

  let rec mapConDecParent = function f (IntSyn.ConDec (name, parent, i, status, V, L)) -> 
        IntSyn.ConDec (name, f parent, i, status, V, L)
    | f (IntSyn.ConDef (name, parent, i, U, V, L, Anc)) -> 
        IntSyn.ConDef (name, f parent, i, U, V, L, Anc) (* reconstruct Anc?? -fp *)
    | f (IntSyn.AbbrevDef (name, parent, i, U, V, L)) -> 
        IntSyn.AbbrevDef (name, f parent, i, U, V, L)
    | f (IntSyn.SkoDec (name, parent, i, V, L)) -> 
        IntSyn.SkoDec (name, f parent, i, V, L)

  let rec strictify = function (condec as IntSyn.AbbrevDef (name, parent, i, U, V, IntSyn.Type)) -> 
      ((Strict.check ((U, V), NONE);
        IntSyn.ConDef (name, parent, i, U, V, IntSyn.Type, IntSyn.ancestor(U)))
       handle Strict.Error _ => condec)
    | (condec as IntSyn.AbbrevDef _) -> condec

  let rec abbrevify (cid, condec) =
      (case condec
         of I.ConDec (name, parent, i, _, V, L) =>
            let
              let U = Whnf.normalize (I.Root (I.Const cid, I.Nil), I.id)
            in
              I.AbbrevDef (name, parent, i, U, V, L)
            end
          | I.SkoDec (name, parent, i, V, L) =>
            let
              let U = Whnf.normalize (I.Root (I.Skonst cid, I.Nil), I.id)
            in
              I.AbbrevDef (name, parent, i, U, V, L)
            end
          | I.ConDef (name, parent, i, U, V, L, Anc) =>
              I.AbbrevDef (name, parent, i, U, V, L)
          | I.AbbrevDef data => I.AbbrevDef data)

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

  fun installModule ((structTable, constTable, namespace),
                     topOpt, nsOpt,
                     installAction, transformConDec) =
      let
        let structMap : IntSyn.mid IntTree.Table =
              IntTree.new (0)
        let constMap : IntSyn.cid IntTree.Table =
              IntTree.new (0)

        let rec mapStruct mid = valOf (IntTree.lookup structMap mid)

        let rec mapParent = function NONE -> topOpt
          | (SOME parent) -> SOME (mapStruct parent)

        let rec mapConst cid =
            (case IntTree.lookup constMap cid
               of NONE => cid
                | SOME cid' => cid')

        let rec doStruct (mid, StructInfo strdec) =
            let
              let strdec' = mapStrDecParent mapParent strdec
              let mid' = IntSyn.sgnStructAdd strdec'

              let parent = IntSyn.strDecParent strdec'
              let nsOpt = (case parent
                             of NONE => nsOpt
                              | SOME mid => SOME (Names.getComponents mid))
              let _ = (case nsOpt
                         of SOME ns => Names.insertStruct (ns, mid')
                          | _ => ())
              let _ = (case parent
                         of NONE => Names.installStructName mid'
                          | _ => ())

              let ns = Names.newNamespace ()
              let _ = Names.installComponents (mid', ns)
            in
              IntTree.insert structMap (mid, mid')
            end

        let rec doConst (cid, ConstInfo (condec, fixity, namePrefOpt, origin)) =
            let
              let condec1 = mapConDecParent mapParent condec
              let condec2 = mapConDecConsts mapConst condec1
              let condec3 = transformConDec (cid, condec2)
              let cid' = IntSyn.sgnAdd condec3

              let parent = IntSyn.conDecParent condec3
              let nsOpt = (case parent
                             of NONE => nsOpt
                              | SOME mid => SOME (Names.getComponents mid))
              let _ = (case nsOpt
                         of SOME ns => Names.insertConst (ns, cid')
                          | _ => ())
              let _ = (case parent
                         of NONE => Names.installConstName cid'
                          | _ => ())

              let _ = installAction (cid', origin)

              let _ = (case fixity
                         of Names.Fixity.Nonfix => ()
                          | _ => Names.installFixity (cid', fixity))
              let _ = (case namePrefOpt
                         of NONE => ()
                          | SOME (n1, n2) =>
                              Names.installNamePref (cid', (n1, n2)))
            in
              IntTree.insert constMap (cid, cid')
            end
      in
        IntTree.app doStruct structTable;
        IntTree.app doConst constTable
      end

  let decToDef = strictify o abbrevify

  let rec installStruct (strdec, module, nsOpt, installAction, isDef) =
      let
        let transformConDec = if isDef then decToDef
                              else (fn (_, condec) => condec)
        let mid = IntSyn.sgnStructAdd strdec
        let _ = case nsOpt
                  of SOME namespace => Names.insertStruct (namespace, mid)
                   | _ => ()
        let _ = Names.installStructName mid
        let ns = Names.newNamespace ()
        let _ = Names.installComponents (mid, ns)
      in
        installModule (module, SOME mid, NONE,
                       installAction, transformConDec)
      end

  let rec installSig (module, nsOpt, installAction, isDef) =
      let
        let transformConDec = if isDef then decToDef
                              else (fn (_, condec) => condec)
      in
        installModule (module, NONE, nsOpt,
                       installAction, transformConDec)
      end

  let rec abstractModule (namespace, topOpt) =
      let
        let structTable : StructInfo IntTree.Table =
              IntTree.new (0)
        let constTable : ConstInfo IntTree.Table =
              IntTree.new (0)

        let mapParent =
            (case topOpt
               of NONE => (fun parent -> parent)
                | SOME mid => (fn SOME mid' => if mid = mid' then NONE
                                               else SOME mid'))

        let rec doStruct (_, mid) =
            let
              let strdec = IntSyn.sgnStructLookup mid
              let strdec' = mapStrDecParent mapParent strdec
              let ns = Names.getComponents mid
            in
              IntTree.insert structTable (mid, StructInfo strdec');
              doNS ns
            end

        and doConst (_, cid) =
            let
              let condec = IntSyn.sgnLookup cid
              let condec' = mapConDecParent mapParent condec
              let fixity = Names.getFixity cid
              let namePref = Names.getNamePref cid
              let origin = Origins.originLookup cid
            in
              IntTree.insert constTable (cid, ConstInfo (condec', fixity, namePref, origin))
            end

        and doNS ns =
            (Names.appStructs doStruct ns;
             Names.appConsts doConst ns)
      in
        doNS namespace;
        (structTable, constTable, namespace)
      end

  let rec instantiateModule (module as (_, _, namespace), transform) =
      let
        let transformConDec = transform namespace
        let mid = IntSyn.sgnStructAdd (IntSyn.StrDec ("wheresubj", NONE))
        let ns = Names.newNamespace ()
        let _ = Names.installComponents (mid, ns)
        let _ = installModule (module, SOME mid, NONE,
                               fun _ -> (), transformConDec)
      in
        abstractModule (ns, SOME mid)
      end

  local
    let defList : string list ref = ref nil
    let defCount : int ref = ref 0
    let defs : module HashTable.Table = HashTable.new (4096)
    let rec defsClear () = HashTable.clear defs
    let defsInsert = HashTable.insertShadow defs
    let defsLookup = HashTable.lookup defs
    let defsDelete = HashTable.delete defs
  in

    let rec reset () = (defList := nil; defCount := 0;
                    defsClear ())

    let rec resetFrom mark =
        let
          let rec ct (l, i) = if i <= mark then l
                          else
                            let
                              let h::t = l
                            in
                              defsDelete h;
                              ct (t, i-1)
                            end
        in
          defList := ct (!defList, !defCount);
          defCount := mark
        end

    let rec sigDefSize () = !defCount

    let rec installSigDef (id, module) =
        (case defsInsert (id, module)
           of NONE => (defList := id::(!defList);
                       defCount := !defCount + 1)
            | SOME entry => (raise Error ("Shadowing: A module type named " ^ id
                                          ^ "\nhas already been declared");
                             defsInsert entry;
                             ()))

    let lookupSigDef = defsLookup

  end

end
