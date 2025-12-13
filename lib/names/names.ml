(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

functor (* GEN BEGIN FUNCTOR DECL *) Names (structure Global : GLOBAL
               (*! structure IntSyn' : INTSYN !*)
               structure Constraints : CONSTRAINTS
               (*! sharing Constraints.IntSyn = IntSyn' !*)
               structure HashTable : TABLE where type key = string
               structure StringTree : TABLE where type key = string)
  : NAMES =
struct

  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  (*
     Unprintable is raised when trying to resolve the names
     of unnamed variables.  Usually, this signals an error
     in Twelf; the only exception is the use of anonymous
     bound variables [_] or {_} in the source.
  *)
  exception Unprintable

  (***********************)
  (* Operator Precedence *)
  (***********************)

  structure Fixity :> FIXITY =
  struct
    (* Associativity ascribed to infix operators
       assoc ::= left    e.g. `<-'
               | right   e.g. `->'
               | none    e.g. `==' from some object language
    *)
    datatype associativity = Left | Right | None

    (* Operator Precedence *)
    datatype precedence = Strength of int

    (* Maximal and minimal precedence which can be declared explicitly *)
    (* GEN BEGIN TAG OUTSIDE LET *) val maxPrecInt = 9999 (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val maxPrec = Strength(maxPrecInt) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val minPrecInt = 0 (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val minPrec = Strength(minPrecInt) (* GEN END TAG OUTSIDE LET *)

    fun less (Strength(p), Strength(q)) = (p < q)
    fun leq (Strength(p), Strength(q)) = (p <= q)
    fun compare (Strength(p), Strength(q)) = Int.compare (p, q)

    fun inc (Strength(p)) = Strength(p+1)
    fun dec (Strength(p)) = Strength(p-1)

    (* Fixities ascribed to constants *)
    datatype fixity =
        Nonfix
      | Infix of precedence * associativity
      | Prefix of precedence
      | Postfix of precedence

    (* returns integer for precedence such that lower values correspond to higher precedence, useful for exports *)
    fun (* GEN BEGIN FUN FIRST *) precToIntAsc(Infix(Strength n,_)) = maxPrecInt + 1 - n (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) precToIntAsc(Prefix(Strength n)) = maxPrecInt + 1 - n (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) precToIntAsc(Postfix(Strength n)) = maxPrecInt + 1 - n (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) precToIntAsc(Nonfix) = minPrecInt (* GEN END FUN BRANCH *)

    (* prec (fix) = precedence of fix *)
    fun (* GEN BEGIN FUN FIRST *) prec (Infix(p,_)) = p (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) prec (Prefix(p)) = p (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) prec (Postfix(p)) = p (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) prec (Nonfix) = inc (maxPrec) (* GEN END FUN BRANCH *)

    (* toString (fix) = declaration corresponding to fix *)
    fun (* GEN BEGIN FUN FIRST *) toString (Infix(Strength(p),Left)) = "%infix left " ^ Int.toString p (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) toString (Infix(Strength(p),Right)) = "%infix right " ^ Int.toString p (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) toString (Infix(Strength(p),None)) = "%infix none " ^ Int.toString p (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) toString (Prefix(Strength(p))) = "%prefix " ^ Int.toString p (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) toString (Postfix(Strength(p))) = "%postfix " ^ Int.toString p (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) toString (Nonfix) = "%nonfix" (* GEN END FUN BRANCH *)   (* not legal input *)

  end  (* structure Fixity *)

  (* argNumber (fix) = minimum # of explicit arguments required *)
  (* for operator with fixity fix (0 if there are no requirements) *)
  fun (* GEN BEGIN FUN FIRST *) argNumber (Fixity.Nonfix) = 0 (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) argNumber (Fixity.Infix _) = 2 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) argNumber (Fixity.Prefix _) = 1 (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) argNumber (Fixity.Postfix _) = 1 (* GEN END FUN BRANCH *)

  (* checkAtomic (name, V, n) = ()
     if V expects exactly n arguments,
     raises Error(msg) otherwise
  *)
  fun (* GEN BEGIN FUN FIRST *) checkAtomic (name, IntSyn.Pi (D, V), 0) = true (* GEN END FUN FIRST *)
      (* allow extraneous arguments, Sat Oct 23 14:18:27 1999 -fp *)
      (* raise Error ("Constant " ^ name ^ " takes too many explicit arguments for given fixity") *)
    | (* GEN BEGIN FUN BRANCH *) checkAtomic (name, IntSyn.Pi (D, V), n) =
        checkAtomic (name, V, n-1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) checkAtomic (_, IntSyn.Uni _, 0) = true (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) checkAtomic (_, IntSyn.Root _, 0) = true (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) checkAtomic (name, _, _) = false (* GEN END FUN BRANCH *)

  (* checkArgNumber (c, n) = ()
     if constant c expects exactly n explicit arguments,
     raises Error (msg) otherwise
  *)
  fun (* GEN BEGIN FUN FIRST *) checkArgNumber (IntSyn.ConDec (name, _, i, _, V, L), n) =
        checkAtomic (name, V, i+n) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) checkArgNumber (IntSyn.SkoDec (name, _, i, V, L), n) =
        checkAtomic (name, V, i+n) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) checkArgNumber (IntSyn.ConDef (name, _, i, _, V, L, _), n) =
        checkAtomic (name, V, i+n) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) checkArgNumber (IntSyn.AbbrevDef (name, _, i, _, V, L), n) =
        checkAtomic (name, V, i+n) (* GEN END FUN BRANCH *)

  (* checkFixity (name, cidOpt, n) = ()
     if n = 0 (no requirement on arguments)
     or name is declared and has n exactly explicit arguments,
     raises Error (msg) otherwise
  *)
  fun (* GEN BEGIN FUN FIRST *) checkFixity (name, _, 0) = () (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) checkFixity (name, cid, n) =
      if checkArgNumber (IntSyn.sgnLookup (cid), n) then ()
      else raise Error ("Constant " ^ name ^ " takes too few explicit arguments for given fixity") (* GEN END FUN BRANCH *)

  (****************************************)
  (* Constants Names and Name Preferences *)
  (****************************************)

  (*
     Names (strings) are associated with constants (cids) in two ways:
     (1) There is an array nameArray mapping constants to print names (string),
     (2) there is a hashtable sgnHashTable mapping identifiers (strings) to constants.

     The mapping from constants to their print names must be maintained
     separately from the global signature, since constants which have
     been shadowed must be marked as such when printing.  Otherwise,
     type checking can generate very strange error messages such as
     "Constant clash: c <> c".

     In the same table we also record the fixity property of constants,
     since it is more a syntactic then semantic property which would
     pollute the lambda-calculus core.

     The mapping from identifers (strings) to constants is used during
     parsing.

     There are global invariants which state the mappings must be
     consistent with each other.
  *)

  datatype qid = Qid of string list * string

  fun qidToString (Qid (ids, name)) =
        List.foldr ((* GEN BEGIN FUNCTION EXPRESSION *) fn (id, s) => id ^ "." ^ s (* GEN END FUNCTION EXPRESSION *)) name ids

  fun (* GEN BEGIN FUN FIRST *) validateQualName nil = NONE (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) validateQualName (l as id::ids) =
        if List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn s => s = "" (* GEN END FUNCTION EXPRESSION *)) l
          then NONE
        else SOME (Qid (rev ids, id)) (* GEN END FUN BRANCH *)

  fun stringToQid name =
        validateQualName (rev (String.fields ((* GEN BEGIN FUNCTION EXPRESSION *) fn c => c = #"." (* GEN END FUNCTION EXPRESSION *)) name))

  fun (* GEN BEGIN FUN FIRST *) unqualified (Qid (nil, id)) = SOME id (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) unqualified _ = NONE (* GEN END FUN BRANCH *)

  type namespace = IntSyn.mid StringTree.table * IntSyn.cid StringTree.table

  fun newNamespace () : namespace =
        (StringTree.new (0), StringTree.new (0))

  fun insertConst ((structTable, constTable), cid) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val condec = IntSyn.sgnLookup cid (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val id = IntSyn.conDecName condec (* GEN END TAG OUTSIDE LET *)
      in
        case StringTree.insertShadow constTable (id, cid)
          of NONE => ()
           | SOME _ =>
               raise Error ("Shadowing: A constant named " ^ id
                            ^ "\nhas already been declared in this signature")
      end

  fun insertStruct ((structTable, constTable), mid) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val strdec = IntSyn.sgnStructLookup mid (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val id = IntSyn.strDecName strdec (* GEN END TAG OUTSIDE LET *)
      in
        case StringTree.insertShadow structTable (id, mid)
          of NONE => ()
           | SOME _ =>
               raise Error ("Shadowing: A structure named " ^ id
                            ^ "\nhas already been declared in this signature")
      end

  fun appConsts f (structTable, constTable) =
        StringTree.app f constTable

  fun appStructs f (structTable, constTable) =
        StringTree.app f structTable

  local
    fun fromTo f (from, to) = if from >= to then ()
                              else (f from; fromTo f (from+1, to))

    (* GEN BEGIN TAG OUTSIDE LET *) val maxCid = Global.maxCid (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val shadowArray : IntSyn.cid option Array.array =
          Array.array (maxCid+1, NONE) (* GEN END TAG OUTSIDE LET *)
    fun shadowClear () = Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => NONE (* GEN END FUNCTION EXPRESSION *)) shadowArray
    (* GEN BEGIN TAG OUTSIDE LET *) val fixityArray : Fixity.fixity Array.array =
          Array.array (maxCid+1, Fixity.Nonfix) (* GEN END TAG OUTSIDE LET *)
    fun fixityClear () = Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => Fixity.Nonfix (* GEN END FUNCTION EXPRESSION *)) fixityArray
    (* GEN BEGIN TAG OUTSIDE LET *) val namePrefArray : (string list * string list) option Array.array =
          Array.array (maxCid+1, NONE) (* GEN END TAG OUTSIDE LET *)
    fun namePrefClear () = Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => NONE (* GEN END FUNCTION EXPRESSION *)) namePrefArray

    (* GEN BEGIN TAG OUTSIDE LET *) val topNamespace : IntSyn.cid HashTable.table = HashTable.new (4096) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val topInsert = HashTable.insertShadow topNamespace (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val topLookup = HashTable.lookup topNamespace (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val topDelete = HashTable.delete topNamespace (* GEN END TAG OUTSIDE LET *)
    fun topClear () = HashTable.clear topNamespace

    (* GEN BEGIN TAG OUTSIDE LET *) val dummyNamespace = (StringTree.new (0), StringTree.new (0)) : namespace (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val maxMid = Global.maxMid (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val structShadowArray : IntSyn.mid option Array.array =
          Array.array (maxMid+1, NONE) (* GEN END TAG OUTSIDE LET *)
    fun structShadowClear () = Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => NONE (* GEN END FUNCTION EXPRESSION *)) structShadowArray
    (* GEN BEGIN TAG OUTSIDE LET *) val componentsArray : namespace Array.array =
          Array.array (maxMid+1, dummyNamespace) (* GEN END TAG OUTSIDE LET *)
    fun componentsClear () = Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => dummyNamespace (* GEN END FUNCTION EXPRESSION *)) componentsArray

    (* GEN BEGIN TAG OUTSIDE LET *) val topStructNamespace : IntSyn.mid HashTable.table =
          HashTable.new (4096) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val topStructInsert = HashTable.insertShadow topStructNamespace (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val topStructLookup = HashTable.lookup topStructNamespace (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val topStructDelete = HashTable.delete topStructNamespace (* GEN END TAG OUTSIDE LET *)
    fun topStructClear () = HashTable.clear topStructNamespace

  in

    (* installName (name, cid) = ()
       Effect: update mapping from identifiers
               to constants, taking into account shadowing
    *)
    fun installConstName cid =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val condec = IntSyn.sgnLookup cid (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val id = IntSyn.conDecName condec (* GEN END TAG OUTSIDE LET *)
        in
          case topInsert (id, cid)
            of NONE => ()
             | SOME (_, cid') => Array.update (shadowArray, cid, SOME cid')
        end

    fun uninstallConst cid =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val condec = IntSyn.sgnLookup cid (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val id = IntSyn.conDecName condec (* GEN END TAG OUTSIDE LET *)
        in
          case Array.sub (shadowArray, cid)
            of NONE => (if topLookup id = SOME cid
                          then topDelete id
                        else ())
             | SOME cid' => (topInsert (id, cid');
                             Array.update (shadowArray, cid, NONE));
          Array.update (fixityArray, cid, Fixity.Nonfix);
          Array.update (namePrefArray, cid, NONE)
        end

    fun installStructName mid =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val strdec = IntSyn.sgnStructLookup mid (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val id = IntSyn.strDecName strdec (* GEN END TAG OUTSIDE LET *)
        in
          case topStructInsert (id, mid)
            of NONE => ()
             | SOME (_, mid') => Array.update (structShadowArray, mid, SOME mid')
        end

    fun uninstallStruct mid =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val strdec = IntSyn.sgnStructLookup mid (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val id = IntSyn.strDecName strdec (* GEN END TAG OUTSIDE LET *)
        in
          case Array.sub (structShadowArray, mid)
            of NONE => if topStructLookup id = SOME mid
                         then topStructDelete id
                       else ()
             | SOME mid' => (topStructInsert (id, mid');
                             Array.update (structShadowArray, mid, NONE));
          Array.update (componentsArray, mid, dummyNamespace)
        end

    fun resetFrom (mark, markStruct) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (limit, limitStruct) = IntSyn.sgnSize () (* GEN END TAG OUTSIDE LET *)
          fun ct f (i, j) = if j < i then ()
                            else (f j; ct f (i, j-1))
        in
          ct uninstallConst (mark, limit-1);
          ct uninstallStruct (markStruct, limitStruct-1)
        end

    (* reset () = ()
       Effect: clear name tables related to constants
    *)
    fun reset () = (topClear (); topStructClear ();
                    shadowClear (); structShadowClear ();
                    fixityClear (); namePrefClear ();
                    componentsClear ())

    fun structComps mid = #1 (Array.sub (componentsArray, mid))
    fun constComps mid = #2 (Array.sub (componentsArray, mid))

    fun (* GEN BEGIN FUN FIRST *) findStruct (structTable, [id]) =
          StringTree.lookup structTable id (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findStruct (structTable, id::ids) =
        (case StringTree.lookup structTable id
           of NONE => NONE
            | SOME mid => findStruct (structComps mid, ids)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) findTopStruct [id] =
          HashTable.lookup topStructNamespace id (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findTopStruct (id::ids) =
        (case HashTable.lookup topStructNamespace id
           of NONE => NONE
            | SOME mid => findStruct (structComps mid, ids)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) findUndefStruct (structTable, [id], ids') =
        (case StringTree.lookup structTable id
           of NONE => SOME (Qid (rev ids', id))
            | SOME _ => NONE) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findUndefStruct (structTable, id::ids, ids') =
        (case StringTree.lookup structTable id
           of NONE => SOME (Qid (rev ids', id))
            | SOME mid => findUndefStruct (structComps mid, ids, id::ids')) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) findTopUndefStruct [id] =
        (case HashTable.lookup topStructNamespace id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findTopUndefStruct (id::ids) =
        (case HashTable.lookup topStructNamespace id
           of NONE => SOME (Qid (nil, id))
            | SOME mid => findUndefStruct (structComps mid, ids, [id])) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) constLookupIn ((structTable, constTable), Qid (nil, id)) =
          StringTree.lookup constTable id (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) constLookupIn ((structTable, constTable), Qid (ids, id)) =
        (case findStruct (structTable, ids)
           of NONE => NONE
            | SOME mid => StringTree.lookup (constComps mid) id) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) structLookupIn ((structTable, constTable), Qid (nil, id)) =
          StringTree.lookup structTable id (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) structLookupIn ((structTable, constTable), Qid (ids, id)) =
        (case findStruct (structTable, ids)
           of NONE => NONE
            | SOME mid => StringTree.lookup (structComps mid) id) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) constUndefIn ((structTable, constTable), Qid (nil, id)) =
        (case StringTree.lookup constTable id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) constUndefIn ((structTable, constTable), Qid (ids, id)) =
        (case findUndefStruct (structTable, ids, nil)
           of opt as SOME _ => opt
            | NONE =>
        (case StringTree.lookup (constComps (valOf (findStruct (structTable, ids)))) id
           of NONE => SOME (Qid (ids, id))
            | SOME _ => NONE)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) structUndefIn ((structTable, constTable), Qid (nil, id)) =
        (case StringTree.lookup structTable id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) structUndefIn ((structTable, constTable), Qid (ids, id)) =
        (case findUndefStruct (structTable, ids, nil)
           of opt as SOME _ => opt
            | NONE =>
        (case StringTree.lookup (structComps (valOf (findStruct (structTable, ids)))) id
           of NONE => SOME (Qid (ids, id))
            | SOME _ => NONE)) (* GEN END FUN BRANCH *)

    (* nameLookup (qid) = SOME(cid),  if qid refers to cid in the current context,
                        = NONE,       if there is no such constant
    *)
    fun (* GEN BEGIN FUN FIRST *) constLookup (Qid (nil, id)) =
          HashTable.lookup topNamespace id (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) constLookup (Qid (ids, id)) =
        (case findTopStruct ids
           of NONE => NONE
            | SOME mid => StringTree.lookup (constComps mid) id) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) structLookup (Qid (nil, id)) =
          HashTable.lookup topStructNamespace id (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) structLookup (Qid (ids, id)) =
        (case findTopStruct ids
           of NONE => NONE
            | SOME mid => StringTree.lookup (structComps mid) id) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) constUndef (Qid (nil, id)) =
        (case HashTable.lookup topNamespace id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) constUndef (Qid (ids, id)) =
        (case findTopUndefStruct ids
           of opt as SOME _ => opt
            | NONE =>
        (case StringTree.lookup (constComps (valOf (findTopStruct ids))) id
           of NONE => SOME (Qid (ids, id))
            | SOME _ => NONE)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) structUndef (Qid (nil, id)) =
        (case HashTable.lookup topStructNamespace id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) structUndef (Qid (ids, id)) =
        (case findTopUndefStruct ids
           of opt as SOME _ => opt
            | NONE =>
        (case StringTree.lookup (structComps (valOf (findTopStruct ids))) id
           of NONE => SOME (Qid (ids, id))
            | SOME _ => NONE)) (* GEN END FUN BRANCH *)

    fun structPath (mid, ids) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val strdec = IntSyn.sgnStructLookup mid (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ids' = IntSyn.strDecName strdec::ids (* GEN END TAG OUTSIDE LET *)
        in
          case IntSyn.strDecParent strdec
            of NONE => ids'
             | SOME mid' => structPath (mid', ids')
        end

    fun (* GEN BEGIN FUN FIRST *) maybeShadow (qid, false) = qid (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) maybeShadow (Qid (nil, id), true) = Qid (nil, "%" ^ id ^ "%") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) maybeShadow (Qid (id::ids, name), true) = Qid ("%" ^ id ^ "%"::ids, name) (* GEN END FUN BRANCH *)

    fun conDecQid condec =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val id = IntSyn.conDecName condec (* GEN END TAG OUTSIDE LET *)
        in
          case IntSyn.conDecParent condec
            of NONE => Qid (nil, id)
             | SOME mid => Qid (structPath (mid, nil), id)
        end

    (* constQid (cid) = qid,
       where `qid' is the print name of cid
    *)
    fun constQid cid =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val condec = IntSyn.sgnLookup cid (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val qid = conDecQid condec (* GEN END TAG OUTSIDE LET *)
        in
          maybeShadow (qid, constLookup qid <> SOME cid)
        end

    fun structQid mid =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val strdec = IntSyn.sgnStructLookup mid (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val id = IntSyn.strDecName strdec (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val qid = case IntSyn.strDecParent strdec
                      of NONE => Qid (nil, id)
                       | SOME mid => Qid (structPath (mid, nil), id) (* GEN END TAG OUTSIDE LET *)
        in
          maybeShadow (qid, structLookup qid <> SOME mid)
        end

    (* installFixity (cid, fixity) = ()
       Effect: install fixity for constant cid,
               possibly print declaration depending on chatter level
    *)
    fun installFixity (cid, fixity) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val name = qidToString (constQid cid) (* GEN END TAG OUTSIDE LET *)
        in
          checkFixity (name, cid, argNumber fixity);
          Array.update (fixityArray, cid, fixity)
        end

    (* getFixity (cid) = fixity
       fixity defaults to Fixity.Nonfix, if nothing has been declared
    *)
    fun getFixity (cid) = Array.sub (fixityArray, cid)

    (* fixityLookup qid = fixity
       where fixity is the fixity associated with constant named qid,
       defaults to Fixity.Nonfix if qid or fixity are undeclared
    *)
    fun fixityLookup qid =
        (case constLookup qid
           of NONE => Fixity.Nonfix
            | SOME cid => getFixity cid)

    (* Name Preferences *)
    (* ePref is the name preference for existential variables of given type *)
    (* uPref is the name preference for universal variables of given type *)

    (* installNamePref' (cid, (ePref, uPref)) see installNamePref *)
    fun installNamePref' (cid, (ePref, uPref)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val L = IntSyn.constUni (cid) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = case L
                    of IntSyn.Type =>
                       raise Error ("Object constant " ^ qidToString (constQid cid) ^ " cannot be given name preference\n"
                                    ^ "Name preferences can only be established for type families")
                     | IntSyn.Kind => () (* GEN END TAG OUTSIDE LET *)
        in
          Array.update (namePrefArray, cid, SOME (ePref, uPref))
        end

    (* installNamePref (cid, (ePref, uPrefOpt)) = ()
       Effect: install name preference for type family cid
       raise Error if cid does not refer to a type family
    *)
    fun (* GEN BEGIN FUN FIRST *) installNamePref (cid, (ePref, nil)) =
          installNamePref' (cid, (ePref, [String.map Char.toLower (hd ePref)])) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) installNamePref (cid, (ePref, uPref)) =
          installNamePref' (cid, (ePref, uPref)) (* GEN END FUN BRANCH *)

    fun getNamePref cid = Array.sub (namePrefArray, cid)

    fun installComponents (mid, namespace) =
          Array.update (componentsArray, mid, namespace)

    fun getComponents mid =
          Array.sub (componentsArray, mid)

    (* local names are more easily re-used: they don't increment the
       counter associated with a name
    *)
    datatype extent = Local | Global
    datatype role = Exist | Univ of extent

    fun (* GEN BEGIN FUN FIRST *) extent (Exist) = Global (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) extent (Univ (ext)) = ext (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) namePrefOf'' (Exist, NONE) = "X" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) namePrefOf'' (Univ _, NONE) = "x" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) namePrefOf'' (Exist, SOME(ePref, uPref)) = hd ePref (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) namePrefOf'' (Univ _, SOME(ePref, uPref)) = hd uPref (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) namePrefOf' (Exist, NONE) = "X" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) namePrefOf' (Univ _, NONE) = "x" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) namePrefOf' (role, SOME(IntSyn.Const cid)) = namePrefOf'' (role, Array.sub (namePrefArray, cid)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) namePrefOf' (role, SOME(IntSyn.Def cid)) = namePrefOf'' (role, Array.sub (namePrefArray, cid)) (* GEN END FUN BRANCH *)
        (* the following only needed because reconstruction replaces
           undetermined types with FVars *)
      | (* GEN BEGIN FUN BRANCH *) namePrefOf' (role, SOME(IntSyn.FVar _)) = namePrefOf'' (role, NONE) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) namePrefOf' (role, SOME(IntSyn.NSDef cid)) = namePrefOf'' (role, Array.sub (namePrefArray, cid)) (* GEN END FUN BRANCH *)

    (* namePrefOf (role, V) = name
       where name is the preferred base name for a variable with type V

       V should be a type, but the code is robust, returning the default "X" or "x"
    *)
    fun namePrefOf (role, V) = namePrefOf' (role, IntSyn.targetHeadOpt V)

  end  (* local ... *)

  (******************)
  (* Variable Names *)
  (******************)

  (*
     Picking variable names is tricky, since we need to avoid capturing.
     This is entirely a matter of parsing and printing, since the
     internal representation relies on deBruijn indices and explicit
     substitutions.

     During parsing, a name is resolved as follows:
       lower case id => bound variable, constant, error
       upper case id => bound variable, constant, free variable
     where a free variable could become either an FVar
     (in constant declarations) or an EVar (in queries).

     Names are either given by the declaration or query itself, or
     assigned as late as possible.  For example, EVars which are never
     printed are never assigned a name.

     This may be a problem for contexts: if a name is not assigned when
     a declaration is entered into the context, terms in this context
     may not be printable.  Function decName below guarantees that new
     names are assigned to variables added to a context.
  *)

  (*
     There are three data structures:
     1. varTable mapping names (strings) to EVars and FVar types
          -- Actually, FVar types now handled entirely in recon-term.fun
          -- where there needs to be more info for approximate types.
          -- I don't see why EVar/BVar names should be generated apart from
          -- FVar names anyway, since the latter are printed with "`".
          -- -kw
     2. evarList mapping EVars to names (string)
     3. indexTable mapping base names B to integer suffixes to generate
        new names B1, B2, ...

     These are reset for each declaration or query, since
     EVars and FVars are local.
  *)
  local
    datatype var_entry = EVAR of IntSyn.exp (* X *)
      (* remove this datatype? -kw *)

    (* varTable mapping identifiers (strings) to EVars and FVars *)
    (* A hashtable is too inefficient, since it is cleared too often; *)
    (* so we use a red/black trees instead *)
    (* GEN BEGIN TAG OUTSIDE LET *) val varTable : var_entry StringTree.table = StringTree.new (0) (* GEN END TAG OUTSIDE LET *) (* initial size hint *)
    (* GEN BEGIN TAG OUTSIDE LET *) val varInsert = StringTree.insert varTable (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val varLookup = StringTree.lookup varTable (* GEN END TAG OUTSIDE LET *)
    fun varClear () = StringTree.clear varTable

    (* what is this for?  -kw *)
    (* GEN BEGIN TAG OUTSIDE LET *) val varContext : IntSyn.dctx ref = ref IntSyn.Null (* GEN END TAG OUTSIDE LET *)

    (* evarList mapping EVars to names *)
    (* names are assigned only when EVars are parsed or printed *)
    (* the mapping must be implemented as an association list *)
    (* since EVars are identified by reference *)
    (* an alternative becomes possible if time stamps are introduced *)
    (* GEN BEGIN TAG OUTSIDE LET *) val evarList : (IntSyn.exp * string) list ref = ref nil (* GEN END TAG OUTSIDE LET *)

    fun evarReset () = (evarList := nil)
    fun evarLookup (X) =
        let fun (* GEN BEGIN FUN FIRST *) evlk (r, nil) = NONE (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) evlk (r, (IntSyn.EVar(r',_,_,_), name)::l) =
                if r = r' then SOME(name) else evlk (r, l) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) evlk (r, ((IntSyn.AVar(r'), name)::l)) =
                if r = r' then SOME(name) else evlk (r, l) (* GEN END FUN BRANCH *)
        in
          case X of
            IntSyn.EVar(r,_,_,_) => evlk (r, (!evarList))
          | IntSyn.AVar(r) => evlk (r, (!evarList))
        end
    fun evarInsert entry = (evarList := entry::(!evarList))

    fun namedEVars () = !evarList

    (* Since constraints are not printable at present, we only *)
    (* return a list of names of EVars that have constraints on them *)
    (* Note that EVars which don't have names, will not be considered! *)
    fun (* GEN BEGIN FUN FIRST *) evarCnstr' (nil, acc) = acc (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) evarCnstr' ((Xn as (IntSyn.EVar(ref(NONE), _, _, cnstrs), name))::l, acc) =
          (case Constraints.simplify (!cnstrs)
             of nil => evarCnstr' (l, acc)
              | (_::_) => evarCnstr' (l, Xn::acc)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) evarCnstr' (_::l, acc) = evarCnstr' (l, acc) (* GEN END FUN BRANCH *)
    fun evarCnstr () = evarCnstr' (!evarList, nil)

    (* The indexTable maps a name to the last integer suffix used for it.
       The resulting identifer is not guaranteed to be new, and must be
       checked against the names of constants, FVars, EVars, and BVars.
    *)
    (* GEN BEGIN TAG OUTSIDE LET *) val indexTable : int StringTree.table = StringTree.new (0) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val indexInsert = StringTree.insert indexTable (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val indexLookup = StringTree.lookup indexTable (* GEN END TAG OUTSIDE LET *)
    fun indexClear () = StringTree.clear indexTable

    fun (* GEN BEGIN FUN FIRST *) nextIndex' (name, NONE) = (indexInsert (name, 1); 1) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nextIndex' (name, SOME(i)) = (indexInsert (name, i+1); i+1) (* GEN END FUN BRANCH *)

    (* nextIndex (name) = i
       where i is the next available integer suffix for name,
       starting at 1.
       Effect: initialize or increment the indexTable entry for name
    *)
    fun nextIndex (name) = nextIndex' (name, indexLookup (name))
  in
    (* varReset () = ()
       Effect: clear variable tables
       This must be called for each declaration or query
    *)
    fun varReset G = (varClear (); evarReset (); indexClear ();
                      varContext := G)

    (* addEVar (X, name) = ()
       effect: adds (X, name) to varTable and evarList
       assumes name not already used *)
    fun addEVar (X, name) =
        (evarInsert (X, name);
         varInsert (name, EVAR(X)))

    fun getEVarOpt (name) =
        (case varLookup name
          of NONE => NONE
           | SOME(EVAR(X)) => SOME(X))

    (* varDefined (name) = true iff `name' refers to a free variable, *)
    (* which could be an EVar for constant declarations or FVar for queries *)
    fun varDefined (name) =
        (case varLookup name
           of NONE => false
            | SOME _ => true)

    (* conDefined (name) = true iff `name' refers to a constant *)
    fun conDefined (name) =
        (case constLookup (Qid (nil, name))
           of NONE => false
            | SOME _ => true)

    (* ctxDefined (G, name) = true iff `name' is declared in context G *)
    fun ctxDefined (G, name) =
        let fun (* GEN BEGIN FUN FIRST *) cdfd (IntSyn.Null) = false (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) cdfd (IntSyn.Decl(G', IntSyn.Dec(SOME(name'),_))) =
                  name = name' orelse cdfd G' (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) cdfd (IntSyn.Decl(G', IntSyn.BDec(SOME(name'),_))) =
                  name = name' orelse cdfd G' (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) cdfd (IntSyn.Decl(G', IntSyn.NDec(SOME(name')))) =
                  name = name' orelse cdfd G' (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) cdfd (IntSyn.Decl(G', _)) = cdfd G' (* GEN END FUN BRANCH *)
        in
          cdfd G
        end

    (* tryNextName (G, base) = baseN
       where N is the next suffix such that baseN is unused in
       G, as a variable, or as a constant.
    *)
    fun tryNextName (G, base) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val name = base ^ Int.toString (nextIndex (base)) (* GEN END TAG OUTSIDE LET *)
        in
          if varDefined name orelse conDefined name
             orelse ctxDefined (G,name)
            then tryNextName (G, base)
          else name
        end

    fun findNameLocal (G, base, i) =
        let (* GEN BEGIN TAG OUTSIDE LET *) val name = base ^ (if i = 0 then "" else Int.toString (i)) (* GEN END TAG OUTSIDE LET *)
        in
          if varDefined name orelse conDefined name
             orelse ctxDefined (G, name)
            then findNameLocal (G, base, i+1)
          else name
        end

    fun (* GEN BEGIN FUN FIRST *) findName (G, base, Local) = findNameLocal (G, base, 0) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findName (G, base, Global) = tryNextName (G, base) (* GEN END FUN BRANCH *)


    (* GEN BEGIN TAG OUTSIDE LET *) val takeNonDigits = Substring.takel (not o Char.isDigit) (* GEN END TAG OUTSIDE LET *)

    (* baseOf (name) = name',
       where name' is the prefix of name not containing a digit
    *)
    fun baseOf (name) = Substring.string (takeNonDigits (Compat.Substring.full name))

    (* newEvarName (G, X) = name
       where name is the next unused name appropriate for X,
       based on the name preference declaration for A if X:A
    *)
    fun (* GEN BEGIN FUN FIRST *) newEVarName (G, X as IntSyn.EVar(r, _, V, Cnstr)) =
        let
          (* use name preferences below *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = tryNextName (G, namePrefOf (Exist, V)) (* GEN END TAG OUTSIDE LET *)
        in
          (evarInsert (X, name);
           name)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) newEVarName (G, X as IntSyn.AVar(r)) =
        let
          (* use name preferences below *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = tryNextName (G, namePrefOf' (Exist, NONE)) (* GEN END TAG OUTSIDE LET *)
        in
          (evarInsert (X, name);
           name)
        end (* GEN END FUN BRANCH *)

    (* evarName (G, X) = name
       where `name' is the print name X.
       If no name has been assigned yet, assign a new one.
       Effect: if a name is assigned, update varTable
    *)
    fun evarName (G, X) =
        (case evarLookup X
           of NONE => let
                        (* GEN BEGIN TAG OUTSIDE LET *) val name = newEVarName (G, X) (* GEN END TAG OUTSIDE LET *)
                      in
                        (varInsert (name, EVAR(X));
                         name)
                      end
            | SOME (name) => name)


    (* bvarName (G, k) = name
       where `name' is the print name for variable with deBruijn index k.
       Invariant: 1 <= k <= |G|
                  G_k must assign a name
       If no name has been assigned, the context might be built the wrong
       way---check decName below instread of IntSyn.Dec
    *)
    fun bvarName (G, k) =
        case IntSyn.ctxLookup (G, k)
          of IntSyn.Dec(SOME(name), _) => name
           | IntSyn.ADec(SOME(name), _) =>  name
           | IntSyn.NDec(SOME(name)) =>  name (* Evars can depend on NDec :-( *)
           | IntSyn.ADec(None, _) => "ADec_"
           | IntSyn.Dec(None, _) => "Dec_"
           | _ => raise Unprintable

    (* decName' role (G, D) = G,D'
       where D' is a possible renaming of the declaration D
       in order to avoid shadowing other variables or constants
       If D does not assign a name, this picks, based on the name
       preference declaration.
    *)
    fun (* GEN BEGIN FUN FIRST *) decName' role (G, IntSyn.Dec (NONE, V)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val name = findName (G, namePrefOf (role, V), extent (role)) (* GEN END TAG OUTSIDE LET *)
        in
          IntSyn.Dec (SOME(name), V)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decName' role (G, D as IntSyn.Dec (SOME(name), V)) =
        if varDefined name orelse conDefined name
          orelse ctxDefined (G, name)
          then IntSyn.Dec (SOME (tryNextName (G, baseOf name)), V)
        else D (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) decName' role (G, D as IntSyn.BDec (NONE, b as (cid, t))) =
        (* use #l as base name preference for label l *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val name = findName (G, "#" ^ IntSyn.conDecName (IntSyn.sgnLookup cid), Local) (* GEN END TAG OUTSIDE LET *)
        in
          IntSyn.BDec (SOME(name), b)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) decName' role (G, D as IntSyn.BDec (SOME(name), b as (cid, t))) =
        if varDefined name orelse conDefined name
          orelse ctxDefined (G, name)
          then IntSyn.BDec (SOME (tryNextName (G, baseOf name)), b)
        else D (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) decName' role (G, IntSyn.ADec (NONE, d)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val name = findName (G, namePrefOf' (role, NONE), extent (role)) (* GEN END TAG OUTSIDE LET *)
        in
          IntSyn.ADec (SOME(name), d)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) decName' role (G, D as IntSyn.ADec (SOME(name), d)) =
      (*      IntSyn.ADec(SOME(name), d) *)
        if varDefined name orelse conDefined name
          orelse ctxDefined (G, name)
          then IntSyn.ADec (SOME (tryNextName (G, baseOf name)), d)
        else D (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) decName' role (G, D as IntSyn.NDec NONE) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val name = findName (G, "@x", Local) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = print name (* GEN END TAG OUTSIDE LET *)
      
        in
          IntSyn.NDec (SOME name)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) decName' role (G, D as IntSyn.NDec (SOME name)) =
        if varDefined name orelse conDefined name
          orelse ctxDefined (G, name)
          then IntSyn.NDec (SOME (tryNextName (G, baseOf name)))
        else D (* GEN END FUN BRANCH *)

    (* GEN BEGIN TAG OUTSIDE LET *) val decName = decName' Exist (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val decEName = decName' Exist (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val decUName = decName' (Univ (Global)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val decLUName = decName' (Univ (Local)) (* GEN END TAG OUTSIDE LET *)

    (* ctxName G = G'

        Invariant:
        |- G == G' ctx
        where some Declaration in G' have been named/renamed
    *)
    fun (* GEN BEGIN FUN FIRST *) ctxName (IntSyn.Null) = IntSyn.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxName (IntSyn.Decl (G, D)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val G' = ctxName G (* GEN END TAG OUTSIDE LET *)
        in
          IntSyn.Decl (G', decName (G', D))
        end (* GEN END FUN BRANCH *)

    (* ctxLUName G = G'
       like ctxName, but names assigned are local universal names.
    *)
    fun (* GEN BEGIN FUN FIRST *) ctxLUName (IntSyn.Null) = IntSyn.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxLUName (IntSyn.Decl (G, D)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val G' = ctxLUName G (* GEN END TAG OUTSIDE LET *)
        in
          IntSyn.Decl (G', decLUName (G', D))
        end (* GEN END FUN BRANCH *)

    (* pisEName' (G, i, V) = V'
       Assigns names to dependent Pi prefix of V with i implicit abstractions
       Used for implicit EVar in constant declarations after abstraction.
    *)
    fun (* GEN BEGIN FUN FIRST *) pisEName' (G, 0, V) = V (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) pisEName' (G, i, IntSyn.Pi ((D, IntSyn.Maybe), V)) =
        (* i > 0 *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = decEName (G, D) (* GEN END TAG OUTSIDE LET *)
        in
          IntSyn.Pi ((D', IntSyn.Maybe),
                     pisEName' (IntSyn.Decl (G, D'), i-1, V))
        end (* GEN END FUN BRANCH *)
      (* | pisEName' (G, i, V) = V *)

    fun pisEName (i, V) = pisEName' (IntSyn.Null, i, V)

    (* defEName' (G, i, (U,V)) = (U',V')
       Invariant: G |- U : V  and G |- U' : V' since U == U' and V == V'.
       Assigns name to dependent Pi prefix of V and corresponding lam prefix of U
       with i implicit abstractions
       Used for implicit EVar in constant definitions after abstraction.
    *)
    fun (* GEN BEGIN FUN FIRST *) defEName' (G, 0, UV) = UV (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) defEName' (G, i, (IntSyn.Lam (D, U), IntSyn.Pi ((_ (* = D *), P), V))) =
        (* i > 0 *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = decEName (G, D) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (U', V') = defEName' (IntSyn.Decl (G, D'), i-1, (U, V)) (* GEN END TAG OUTSIDE LET *)
        in
          (IntSyn.Lam (D', U'), IntSyn.Pi ((D', P), V'))
        end (* GEN END FUN BRANCH *)
      (* | defEName' (G, i, (U, V)) = (U, V) *)

    fun defEName (imp, UV) = defEName' (IntSyn.Null, imp, UV)

    fun (* GEN BEGIN FUN FIRST *) nameConDec' (IntSyn.ConDec (name, parent, imp, status, V, L)) =
          IntSyn.ConDec (name, parent, imp, status, pisEName (imp, V), L) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nameConDec' (IntSyn.ConDef (name, parent, imp, U, V, L, Anc)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (U', V') = defEName (imp, (U, V)) (* GEN END TAG OUTSIDE LET *)
        in
          IntSyn.ConDef (name, parent, imp, U', V', L, Anc)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nameConDec' (IntSyn.AbbrevDef (name, parent, imp, U, V, L)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (U', V') = defEName (imp, (U, V)) (* GEN END TAG OUTSIDE LET *)
        in
          IntSyn.AbbrevDef (name, parent, imp, U', V', L)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) nameConDec' (skodec) = skodec (* GEN END FUN BRANCH *) (* fix ??? *)

    (* Assigns names to variables in a constant declaration *)
    (* The varReset (); is necessary so that explicitly named variables keep their name *)
    fun nameConDec (conDec) =
        (varReset IntSyn.Null;                  (* declaration is always closed *)
         nameConDec' conDec)

    fun skonstName (name) =
          tryNextName (IntSyn.Null, name)

    (* GEN BEGIN TAG OUTSIDE LET *) val namedEVars = namedEVars (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val evarCnstr = evarCnstr (* GEN END TAG OUTSIDE LET *)

  end  (* local varTable ... *)

end (* GEN END FUNCTOR DECL *);  (* functor Names *)
