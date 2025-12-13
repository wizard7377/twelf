(* Syntax for elaborated modules *)
(* Author: Kevin Watkins *)

functor (* GEN BEGIN FUNCTOR DECL *) ModSyn
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   structure Names' : NAMES
   (*! sharing Names'.IntSyn = IntSyn' !*)
   (*! structure Paths' : PATHS !*)
   structure Origins : ORIGINS
   (*! sharing Origins.Paths = Paths' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Strict : STRICT
   (*! sharing Strict.IntSyn = IntSyn' !*)
   structure IntTree : TABLE where type key = int
   structure HashTable : TABLE where type key = string)
  : MODSYN =
struct

  (*! structure IntSyn = IntSyn' !*)
  structure Names = Names'
  (*! structure Paths = Paths' !*)

  structure I = IntSyn

  exception Error of string

  datatype const_info =
      ConstInfo of IntSyn.con_dec * Names.Fixity.fixity * (string list * string list) option * (string * Paths.occ_con_dec option)

  datatype struct_info =
      StructInfo of IntSyn.str_dec

  (* A module consists of:
     1. a map from cids to constant entries containing
          a. a constant declaration entry (IntSyn.ConDec)
          b. the fixity of the constant
          c. the name preference for the constant (if any)
     2. a map from mids to structure entries containing
          a. a structure declaration entry (IntSyn.StrDec)
          b. the namespace of the structure
     3. the top-level namespace of the module *)

  type module =
      struct_info IntTree.table * const_info IntTree.table * Names.namespace

  type action = IntSyn.cid * (string * Paths.occ_con_dec option) -> unit
  type transform = IntSyn.cid * IntSyn.con_dec -> IntSyn.con_dec

  (* invariant: U in nf, result in nf *)
  fun mapExpConsts f U =
      let
        open IntSyn
  
        fun (* GEN BEGIN FUN FIRST *) trExp (Uni L) = Uni L (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) trExp (Pi ((D, P), V)) = Pi ((trDec D, P), trExp V) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) trExp (Root (H, S)) = Root (trHead H, trSpine S) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) trExp (Lam (D, U)) = Lam (trDec D, trExp U) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) trExp (U as FgnExp csfe) = FgnExpStd.Map.apply csfe trExp (* GEN END FUN BRANCH *)
  
        and trDec (Dec (name, V)) = Dec (name, trExp V)
  
        and (* GEN BEGIN FUN FIRST *) trSpine Nil = Nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) trSpine (App (U, S)) = App (trExp U, trSpine S) (* GEN END FUN BRANCH *)
  
        and (* GEN BEGIN FUN FIRST *) trHead (BVar n) = BVar n (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) trHead (Const cid) = trConst cid (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) trHead (Skonst cid) = trConst cid (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) trHead (Def cid) = trConst cid (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) trHead (NSDef cid) = trConst cid (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) trHead (FgnConst (csid, condec)) =
              FgnConst (csid, mapConDecConsts f condec) (* GEN END FUN BRANCH *)
  
        and trConst cid =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val cid' = f cid (* GEN END TAG OUTSIDE LET *)
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

  and (* GEN BEGIN FUN FIRST *) mapConDecConsts f (IntSyn.ConDec (name, parent, i, status, V, L)) =
        IntSyn.ConDec (name, parent, i, status, mapExpConsts f V, L) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) mapConDecConsts f (IntSyn.ConDef (name, parent, i, U, V, L, Anc)) =
        IntSyn.ConDef (name, parent, i, mapExpConsts f U,
                       mapExpConsts f V, L, Anc) (* GEN END FUN BRANCH *) (* reconstruct Anc?? -fp *)
    | (* GEN BEGIN FUN BRANCH *) mapConDecConsts f (IntSyn.AbbrevDef (name, parent, i, U, V, L)) =
        IntSyn.AbbrevDef (name, parent, i, mapExpConsts f U,
                          mapExpConsts f V, L) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) mapConDecConsts f (IntSyn.SkoDec (name, parent, i, V, L)) =
        IntSyn.SkoDec (name, parent, i, mapExpConsts f V, L) (* GEN END FUN BRANCH *)

  fun mapStrDecParent f (IntSyn.StrDec (name, parent)) =
        IntSyn.StrDec (name, f parent)

  fun (* GEN BEGIN FUN FIRST *) mapConDecParent f (IntSyn.ConDec (name, parent, i, status, V, L)) =
        IntSyn.ConDec (name, f parent, i, status, V, L) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) mapConDecParent f (IntSyn.ConDef (name, parent, i, U, V, L, Anc)) =
        IntSyn.ConDef (name, f parent, i, U, V, L, Anc) (* GEN END FUN BRANCH *) (* reconstruct Anc?? -fp *)
    | (* GEN BEGIN FUN BRANCH *) mapConDecParent f (IntSyn.AbbrevDef (name, parent, i, U, V, L)) =
        IntSyn.AbbrevDef (name, f parent, i, U, V, L) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) mapConDecParent f (IntSyn.SkoDec (name, parent, i, V, L)) =
        IntSyn.SkoDec (name, f parent, i, V, L) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) strictify (condec as IntSyn.AbbrevDef (name, parent, i, U, V, IntSyn.Type)) =
      ((Strict.check ((U, V), NONE);
        IntSyn.ConDef (name, parent, i, U, V, IntSyn.Type, IntSyn.ancestor(U)))
       handle Strict.Error _ => condec) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) strictify (condec as IntSyn.AbbrevDef _) = condec (* GEN END FUN BRANCH *)

  fun abbrevify (cid, condec) =
      (case condec
         of I.ConDec (name, parent, i, _, V, L) =>
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val U = Whnf.normalize (I.Root (I.Const cid, I.Nil), I.id) (* GEN END TAG OUTSIDE LET *)
            in
              I.AbbrevDef (name, parent, i, U, V, L)
            end
          | I.SkoDec (name, parent, i, V, L) =>
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val U = Whnf.normalize (I.Root (I.Skonst cid, I.Nil), I.id) (* GEN END TAG OUTSIDE LET *)
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
        (* GEN BEGIN TAG OUTSIDE LET *) val structMap : IntSyn.mid IntTree.table =
              IntTree.new (0) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val constMap : IntSyn.cid IntTree.table =
              IntTree.new (0) (* GEN END TAG OUTSIDE LET *)
  
        fun mapStruct mid = valOf (IntTree.lookup structMap mid)
  
        fun (* GEN BEGIN FUN FIRST *) mapParent NONE = topOpt (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) mapParent (SOME parent) = SOME (mapStruct parent) (* GEN END FUN BRANCH *)
  
        fun mapConst cid =
            (case IntTree.lookup constMap cid
               of NONE => cid
                | SOME cid' => cid')
  
        fun doStruct (mid, StructInfo strdec) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val strdec' = mapStrDecParent mapParent strdec (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val mid' = IntSyn.sgnStructAdd strdec' (* GEN END TAG OUTSIDE LET *)
  
              (* GEN BEGIN TAG OUTSIDE LET *) val parent = IntSyn.strDecParent strdec' (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val nsOpt = (case parent
                             of NONE => nsOpt
                              | SOME mid => SOME (Names.getComponents mid)) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = (case nsOpt
                         of SOME ns => Names.insertStruct (ns, mid')
                          | _ => ()) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = (case parent
                         of NONE => Names.installStructName mid'
                          | _ => ()) (* GEN END TAG OUTSIDE LET *)
  
              (* GEN BEGIN TAG OUTSIDE LET *) val ns = Names.newNamespace () (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.installComponents (mid', ns) (* GEN END TAG OUTSIDE LET *)
            in
              IntTree.insert structMap (mid, mid')
            end
  
        fun doConst (cid, ConstInfo (condec, fixity, namePrefOpt, origin)) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val condec1 = mapConDecParent mapParent condec (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val condec2 = mapConDecConsts mapConst condec1 (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val condec3 = transformConDec (cid, condec2) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val cid' = IntSyn.sgnAdd condec3 (* GEN END TAG OUTSIDE LET *)
  
              (* GEN BEGIN TAG OUTSIDE LET *) val parent = IntSyn.conDecParent condec3 (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val nsOpt = (case parent
                             of NONE => nsOpt
                              | SOME mid => SOME (Names.getComponents mid)) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = (case nsOpt
                         of SOME ns => Names.insertConst (ns, cid')
                          | _ => ()) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = (case parent
                         of NONE => Names.installConstName cid'
                          | _ => ()) (* GEN END TAG OUTSIDE LET *)
  
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = installAction (cid', origin) (* GEN END TAG OUTSIDE LET *)
  
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = (case fixity
                         of Names.Fixity.Nonfix => ()
                          | _ => Names.installFixity (cid', fixity)) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = (case namePrefOpt
                         of NONE => ()
                          | SOME (n1, n2) =>
                              Names.installNamePref (cid', (n1, n2))) (* GEN END TAG OUTSIDE LET *)
            in
              IntTree.insert constMap (cid, cid')
            end
      in
        IntTree.app doStruct structTable;
        IntTree.app doConst constTable
      end

  (* GEN BEGIN TAG OUTSIDE LET *) val decToDef = strictify o abbrevify (* GEN END TAG OUTSIDE LET *)

  fun installStruct (strdec, module, nsOpt, installAction, isDef) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val transformConDec = if isDef then decToDef
                              else ((* GEN BEGIN FUNCTION EXPRESSION *) fn (_, condec) => condec (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val mid = IntSyn.sgnStructAdd strdec (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = case nsOpt
                  of SOME namespace => Names.insertStruct (namespace, mid)
                   | _ => () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.installStructName mid (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ns = Names.newNamespace () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.installComponents (mid, ns) (* GEN END TAG OUTSIDE LET *)
      in
        installModule (module, SOME mid, NONE,
                       installAction, transformConDec)
      end

  fun installSig (module, nsOpt, installAction, isDef) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val transformConDec = if isDef then decToDef
                              else ((* GEN BEGIN FUNCTION EXPRESSION *) fn (_, condec) => condec (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
      in
        installModule (module, NONE, nsOpt,
                       installAction, transformConDec)
      end

  fun abstractModule (namespace, topOpt) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val structTable : struct_info IntTree.table =
              IntTree.new (0) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val constTable : const_info IntTree.table =
              IntTree.new (0) (* GEN END TAG OUTSIDE LET *)
  
        (* GEN BEGIN TAG OUTSIDE LET *) val mapParent =
            (case topOpt
               of NONE => ((* GEN BEGIN FUNCTION EXPRESSION *) fn parent => parent (* GEN END FUNCTION EXPRESSION *))
                | SOME mid => ((* GEN BEGIN FUNCTION EXPRESSION *) fn SOME mid' => if mid = mid' then NONE
                                               else SOME mid' (* GEN END FUNCTION EXPRESSION *))) (* GEN END TAG OUTSIDE LET *)
  
        fun doStruct (_, mid) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val strdec = IntSyn.sgnStructLookup mid (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val strdec' = mapStrDecParent mapParent strdec (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val ns = Names.getComponents mid (* GEN END TAG OUTSIDE LET *)
            in
              IntTree.insert structTable (mid, StructInfo strdec');
              doNS ns
            end
  
        and doConst (_, cid) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val condec = IntSyn.sgnLookup cid (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val condec' = mapConDecParent mapParent condec (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val fixity = Names.getFixity cid (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val namePref = Names.getNamePref cid (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val origin = Origins.originLookup cid (* GEN END TAG OUTSIDE LET *)
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

  fun instantiateModule (module as (_, _, namespace), transform) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val transformConDec = transform namespace (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val mid = IntSyn.sgnStructAdd (IntSyn.StrDec ("wheresubj", NONE)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ns = Names.newNamespace () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.installComponents (mid, ns) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = installModule (module, SOME mid, NONE,
                               (* GEN BEGIN FUNCTION EXPRESSION *) fn _ => () (* GEN END FUNCTION EXPRESSION *), transformConDec) (* GEN END TAG OUTSIDE LET *)
      in
        abstractModule (ns, SOME mid)
      end

  local
    (* GEN BEGIN TAG OUTSIDE LET *) val defList : string list ref = ref nil (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val defCount : int ref = ref 0 (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val defs : module HashTable.table = HashTable.new (4096) (* GEN END TAG OUTSIDE LET *)
    fun defsClear () = HashTable.clear defs
    (* GEN BEGIN TAG OUTSIDE LET *) val defsInsert = HashTable.insertShadow defs (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val defsLookup = HashTable.lookup defs (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val defsDelete = HashTable.delete defs (* GEN END TAG OUTSIDE LET *)
  in

    fun reset () = (defList := nil; defCount := 0;
                    defsClear ())

    fun resetFrom mark =
        let
          fun ct (l, i) = if i <= mark then l
                          else
                            let
                              (* GEN BEGIN TAG OUTSIDE LET *) val h::t = l (* GEN END TAG OUTSIDE LET *)
                            in
                              defsDelete h;
                              ct (t, i-1)
                            end
        in
          defList := ct (!defList, !defCount);
          defCount := mark
        end

    fun sigDefSize () = !defCount

    fun installSigDef (id, module) =
        (case defsInsert (id, module)
           of NONE => (defList := id::(!defList);
                       defCount := !defCount + 1)
            | SOME entry => (raise Error ("Shadowing: A signature named " ^ id
                                          ^ "\nhas already been declared");
                             defsInsert entry;
                             ()))

    (* GEN BEGIN TAG OUTSIDE LET *) val lookupSigDef = defsLookup (* GEN END TAG OUTSIDE LET *)

  end

end (* GEN END FUNCTOR DECL *)
