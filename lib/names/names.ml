(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

module Names (Global : GLOBAL)
               (*! module IntSyn' : INTSYN !*)
               (Constraints : CONSTRAINTS)
               (*! sharing Constraints.IntSyn = IntSyn' !*)
               (HashTable : TABLE with type key = string)
               (StringTree : TABLE with type key = string))
  : NAMES =
struct

  (*! module IntSyn = IntSyn' !*)

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

  (Fixity : FIXITY) =
  struct
    (* Associativity ascribed to infix operators
       assoc ::= left    e.g. `<-'
               | right   e.g. `->'
               | none    e.g. `==' from some object language
    *)
    type associativity = Left | Right | None

    (* Operator Precedence *)
    type precedence = Strength of int

    (* Maximal and minimal precedence which can be declared explicitly *)
    let maxPrecInt = 9999
    let maxPrec = Strength(maxPrecInt)
    let minPrecInt = 0
    let minPrec = Strength(minPrecInt)

    let rec less (Strength(p), Strength(q)) = (p < q)
    let rec leq (Strength(p), Strength(q)) = (p <= q)
    let rec compare (Strength(p), Strength(q)) = Int.compare (p, q)

    let rec inc (Strength(p)) = Strength(p+1)
    let rec dec (Strength(p)) = Strength(p-1)

    (* Fixities ascribed to constants *)
    type fixity =
        Nonfix
      | Infix of precedence * associativity
      | Prefix of precedence
      | Postfix of precedence

    (* returns integer for precedence such that lower values correspond to higher precedence, useful for exports *)
    let rec precToIntAsc(Infix(Strength n,_)) = maxPrecInt + 1 - n
      | precToIntAsc(Prefix(Strength n)) = maxPrecInt + 1 - n
      | precToIntAsc(Postfix(Strength n)) = maxPrecInt + 1 - n
      | precToIntAsc(Nonfix) = minPrecInt

    (* prec (fix) = precedence of fix *)
    let rec prec = function (Infix(p,_)) -> p
      | (Prefix(p)) -> p
      | (Postfix(p)) -> p
      | (Nonfix) -> inc (maxPrec)

    (* toString (fix) = declaration corresponding to fix *)
    let rec toString = function (Infix(Strength(p),Left)) -> "%infix left " ^ Int.toString p
      | (Infix(Strength(p),Right)) -> "%infix right " ^ Int.toString p
      | (Infix(Strength(p),None)) -> "%infix none " ^ Int.toString p
      | (Prefix(Strength(p))) -> "%prefix " ^ Int.toString p
      | (Postfix(Strength(p))) -> "%postfix " ^ Int.toString p
      | (Nonfix) -> "%nonfix"   (* not legal input *)

  end  (* module Fixity *)

  (* argNumber (fix) = minimum # of explicit arguments required *)
  (* for operator with fixity fix (0 if there are no requirements) *)
  let rec argNumber = function (Fixity.Nonfix) -> 0
    | (Fixity.Infix _) -> 2
    | (Fixity.Prefix _) -> 1
    | (Fixity.Postfix _) -> 1

  (* checkAtomic (name, V, n) = ()
     if V expects exactly n arguments,
     raises Error(msg) otherwise
  *)
  let rec checkAtomic = function (name, IntSyn.Pi (D, V), 0) -> true
      (* allow extraneous arguments, Sat Oct 23 14:18:27 1999 -fp *)
      (* raise Error ("Constant " ^ name ^ " takes too many explicit arguments for given fixity") *)
    | (name, IntSyn.Pi (D, V), n) -> 
        checkAtomic (name, V, n-1)
    | (_, IntSyn.Uni _, 0) -> true
    | (_, IntSyn.Root _, 0) -> true
    | (name, _, _) -> false

  (* checkArgNumber (c, n) = ()
     if constant c expects exactly n explicit arguments,
     raises Error (msg) otherwise
  *)
  let rec checkArgNumber = function (IntSyn.ConDec (name, _, i, _, V, L), n) -> 
        checkAtomic (name, V, i+n)
    | (IntSyn.SkoDec (name, _, i, V, L), n) -> 
        checkAtomic (name, V, i+n)
    | (IntSyn.ConDef (name, _, i, _, V, L, _), n) -> 
        checkAtomic (name, V, i+n)
    | (IntSyn.AbbrevDef (name, _, i, _, V, L), n) -> 
        checkAtomic (name, V, i+n)

  (* checkFixity (name, cidOpt, n) = ()
     if n = 0 (no requirement on arguments)
     or name is declared and has n exactly explicit arguments,
     raises Error (msg) otherwise
  *)
  let rec checkFixity = function (name, _, 0) -> ()
    | (name, cid, n) -> 
      if checkArgNumber (IntSyn.sgnLookup (cid), n) then ()
      else raise Error ("Constant " ^ name ^ " takes too few explicit arguments for given fixity")

  (****************************************)
  (* Constants Names and Name Preferences *)
  (****************************************)

  (*
     Names (strings) are associated with constants (cids) in two ways:
     (1) There is an array nameArray mapping constants to print names (string),
     (2) there is a hashtable sgnHashTable mapping identifiers (strings) to constants.

     The mapping from constants to their print names must be maintained
     separately from the global module type, since constants which have
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

  type qid = Qid of string list * string

  let rec qidToString (Qid (ids, name)) =
        List.foldr (fn (id, s) => id ^ "." ^ s) name ids

  let rec validateQualName = function nil -> NONE
    | (l as id::ids) -> 
        if List.exists (fun s -> s = "") l
          then NONE
        else SOME (Qid (rev ids, id))

  let rec stringToQid name =
        validateQualName (rev (String.fields (fun c -> c = #".") name))

  let rec unqualified = function (Qid (nil, id)) -> SOME id
    | _ -> NONE

  type namespace = IntSyn.mid StringTree.Table * IntSyn.cid StringTree.Table

  let rec newNamespace () : namespace =
        (StringTree.new (0), StringTree.new (0))

  let rec insertConst ((structTable, constTable), cid) =
      let
        let condec = IntSyn.sgnLookup cid
        let id = IntSyn.conDecName condec
      in
        case StringTree.insertShadow constTable (id, cid)
          of NONE => ()
           | SOME _ =>
               raise Error ("Shadowing: A constant named " ^ id
                            ^ "\nhas already been declared in this module type")
      end

  let rec insertStruct ((structTable, constTable), mid) =
      let
        let strdec = IntSyn.sgnStructLookup mid
        let id = IntSyn.strDecName strdec
      in
        case StringTree.insertShadow structTable (id, mid)
          of NONE => ()
           | SOME _ =>
               raise Error ("Shadowing: A module named " ^ id
                            ^ "\nhas already been declared in this module type")
      end

  let rec appConsts f (structTable, constTable) =
        StringTree.app f constTable

  let rec appStructs f (structTable, constTable) =
        StringTree.app f structTable

  local
    let rec fromTo f (from, to) = if from >= to then ()
                              else (f from; fromTo f (from+1, to))

    let maxCid = Global.maxCid
    let shadowArray : IntSyn.cid option Array.array =
          Array.array (maxCid+1, NONE)
    let rec shadowClear () = Array.modify (fun _ -> NONE) shadowArray
    let fixityArray : Fixity.fixity Array.array =
          Array.array (maxCid+1, Fixity.Nonfix)
    let rec fixityClear () = Array.modify (fun _ -> Fixity.Nonfix) fixityArray
    let namePrefArray : (string list * string list) option Array.array =
          Array.array (maxCid+1, NONE)
    let rec namePrefClear () = Array.modify (fun _ -> NONE) namePrefArray

    let topNamespace : IntSyn.cid HashTable.Table = HashTable.new (4096)
    let topInsert = HashTable.insertShadow topNamespace
    let topLookup = HashTable.lookup topNamespace
    let topDelete = HashTable.delete topNamespace
    let rec topClear () = HashTable.clear topNamespace

    let dummyNamespace = (StringTree.new (0), StringTree.new (0)) : namespace

    let maxMid = Global.maxMid
    let structShadowArray : IntSyn.mid option Array.array =
          Array.array (maxMid+1, NONE)
    let rec structShadowClear () = Array.modify (fun _ -> NONE) structShadowArray
    let componentsArray : namespace Array.array =
          Array.array (maxMid+1, dummyNamespace)
    let rec componentsClear () = Array.modify (fun _ -> dummyNamespace) componentsArray

    let topStructNamespace : IntSyn.mid HashTable.Table =
          HashTable.new (4096)
    let topStructInsert = HashTable.insertShadow topStructNamespace
    let topStructLookup = HashTable.lookup topStructNamespace
    let topStructDelete = HashTable.delete topStructNamespace
    let rec topStructClear () = HashTable.clear topStructNamespace

  in

    (* installName (name, cid) = ()
       Effect: update mapping from identifiers
               to constants, taking into account shadowing
    *)
    let rec installConstName cid =
        let
          let condec = IntSyn.sgnLookup cid
          let id = IntSyn.conDecName condec
        in
          case topInsert (id, cid)
            of NONE => ()
             | SOME (_, cid') => Array.update (shadowArray, cid, SOME cid')
        end

    let rec uninstallConst cid =
        let
          let condec = IntSyn.sgnLookup cid
          let id = IntSyn.conDecName condec
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

    let rec installStructName mid =
        let
          let strdec = IntSyn.sgnStructLookup mid
          let id = IntSyn.strDecName strdec
        in
          case topStructInsert (id, mid)
            of NONE => ()
             | SOME (_, mid') => Array.update (structShadowArray, mid, SOME mid')
        end

    let rec uninstallStruct mid =
        let
          let strdec = IntSyn.sgnStructLookup mid
          let id = IntSyn.strDecName strdec
        in
          case Array.sub (structShadowArray, mid)
            of NONE => if topStructLookup id = SOME mid
                         then topStructDelete id
                       else ()
             | SOME mid' => (topStructInsert (id, mid');
                             Array.update (structShadowArray, mid, NONE));
          Array.update (componentsArray, mid, dummyNamespace)
        end

    let rec resetFrom (mark, markStruct) =
        let
          let (limit, limitStruct) = IntSyn.sgnSize ()
          let rec ct f (i, j) = if j < i then ()
                            else (f j; ct f (i, j-1))
        in
          ct uninstallConst (mark, limit-1);
          ct uninstallStruct (markStruct, limitStruct-1)
        end

    (* reset () = ()
       Effect: clear name tables related to constants
    *)
    let rec reset () = (topClear (); topStructClear ();
                    shadowClear (); structShadowClear ();
                    fixityClear (); namePrefClear ();
                    componentsClear ())

    let rec structComps mid = #1 (Array.sub (componentsArray, mid))
    let rec constComps mid = #2 (Array.sub (componentsArray, mid))

    let rec findStruct = function (structTable, [id]) -> 
          StringTree.lookup structTable id
      | (structTable, id::ids) -> 
        (case StringTree.lookup structTable id
           of NONE => NONE
            | SOME mid => findStruct (structComps mid, ids))

    let rec findTopStruct = function [id] -> 
          HashTable.lookup topStructNamespace id
      | (id::ids) -> 
        (case HashTable.lookup topStructNamespace id
           of NONE => NONE
            | SOME mid => findStruct (structComps mid, ids))

    let rec findUndefStruct = function (structTable, [id], ids') -> 
        (case StringTree.lookup structTable id
           of NONE => SOME (Qid (rev ids', id))
            | SOME _ => NONE)
      | (structTable, id::ids, ids') -> 
        (case StringTree.lookup structTable id
           of NONE => SOME (Qid (rev ids', id))
            | SOME mid => findUndefStruct (structComps mid, ids, id::ids'))

    let rec findTopUndefStruct = function [id] -> 
        (case HashTable.lookup topStructNamespace id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE)
      | (id::ids) -> 
        (case HashTable.lookup topStructNamespace id
           of NONE => SOME (Qid (nil, id))
            | SOME mid => findUndefStruct (structComps mid, ids, [id]))

    let rec constLookupIn = function ((structTable, constTable), Qid (nil, id)) -> 
          StringTree.lookup constTable id
      | ((structTable, constTable), Qid (ids, id)) -> 
        (case findStruct (structTable, ids)
           of NONE => NONE
            | SOME mid => StringTree.lookup (constComps mid) id)

    let rec structLookupIn = function ((structTable, constTable), Qid (nil, id)) -> 
          StringTree.lookup structTable id
      | ((structTable, constTable), Qid (ids, id)) -> 
        (case findStruct (structTable, ids)
           of NONE => NONE
            | SOME mid => StringTree.lookup (structComps mid) id)

    let rec constUndefIn = function ((structTable, constTable), Qid (nil, id)) -> 
        (case StringTree.lookup constTable id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE)
      | ((structTable, constTable), Qid (ids, id)) -> 
        (case findUndefStruct (structTable, ids, nil)
           of opt as SOME _ => opt
            | NONE =>
        (case StringTree.lookup (constComps (valOf (findStruct (structTable, ids)))) id
           of NONE => SOME (Qid (ids, id))
            | SOME _ => NONE))

    let rec structUndefIn = function ((structTable, constTable), Qid (nil, id)) -> 
        (case StringTree.lookup structTable id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE)
      | ((structTable, constTable), Qid (ids, id)) -> 
        (case findUndefStruct (structTable, ids, nil)
           of opt as SOME _ => opt
            | NONE =>
        (case StringTree.lookup (structComps (valOf (findStruct (structTable, ids)))) id
           of NONE => SOME (Qid (ids, id))
            | SOME _ => NONE))

    (* nameLookup (qid) = SOME(cid),  if qid refers to cid in the current context,
                        = NONE,       if there is no such constant
    *)
    let rec constLookup = function (Qid (nil, id)) -> 
          HashTable.lookup topNamespace id
      | (Qid (ids, id)) -> 
        (case findTopStruct ids
           of NONE => NONE
            | SOME mid => StringTree.lookup (constComps mid) id)

    let rec structLookup = function (Qid (nil, id)) -> 
          HashTable.lookup topStructNamespace id
      | (Qid (ids, id)) -> 
        (case findTopStruct ids
           of NONE => NONE
            | SOME mid => StringTree.lookup (structComps mid) id)

    let rec constUndef = function (Qid (nil, id)) -> 
        (case HashTable.lookup topNamespace id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE)
      | (Qid (ids, id)) -> 
        (case findTopUndefStruct ids
           of opt as SOME _ => opt
            | NONE =>
        (case StringTree.lookup (constComps (valOf (findTopStruct ids))) id
           of NONE => SOME (Qid (ids, id))
            | SOME _ => NONE))

    let rec structUndef = function (Qid (nil, id)) -> 
        (case HashTable.lookup topStructNamespace id
           of NONE => SOME (Qid (nil, id))
            | SOME _ => NONE)
      | (Qid (ids, id)) -> 
        (case findTopUndefStruct ids
           of opt as SOME _ => opt
            | NONE =>
        (case StringTree.lookup (structComps (valOf (findTopStruct ids))) id
           of NONE => SOME (Qid (ids, id))
            | SOME _ => NONE))

    let rec structPath (mid, ids) =
        let
          let strdec = IntSyn.sgnStructLookup mid
          let ids' = IntSyn.strDecName strdec::ids
        in
          case IntSyn.strDecParent strdec
            of NONE => ids'
             | SOME mid' => structPath (mid', ids')
        end

    let rec maybeShadow = function (qid, false) -> qid
      | (Qid (nil, id), true) -> Qid (nil, "%" ^ id ^ "%")
      | (Qid (id::ids, name), true) -> Qid ("%" ^ id ^ "%"::ids, name)

    let rec conDecQid condec =
        let
          let id = IntSyn.conDecName condec
        in
          case IntSyn.conDecParent condec
            of NONE => Qid (nil, id)
             | SOME mid => Qid (structPath (mid, nil), id)
        end

    (* constQid (cid) = qid,
       where `qid' is the print name of cid
    *)
    let rec constQid cid =
        let
          let condec = IntSyn.sgnLookup cid
          let qid = conDecQid condec
        in
          maybeShadow (qid, constLookup qid <> SOME cid)
        end

    let rec structQid mid =
        let
          let strdec = IntSyn.sgnStructLookup mid
          let id = IntSyn.strDecName strdec
          let qid = case IntSyn.strDecParent strdec
                      of NONE => Qid (nil, id)
                       | SOME mid => Qid (structPath (mid, nil), id)
        in
          maybeShadow (qid, structLookup qid <> SOME mid)
        end

    (* installFixity (cid, fixity) = ()
       Effect: install fixity for constant cid,
               possibly print declaration depending on chatter level
    *)
    let rec installFixity (cid, fixity) =
        let
          let name = qidToString (constQid cid)
        in
          checkFixity (name, cid, argNumber fixity);
          Array.update (fixityArray, cid, fixity)
        end

    (* getFixity (cid) = fixity
       fixity defaults to Fixity.Nonfix, if nothing has been declared
    *)
    let rec getFixity (cid) = Array.sub (fixityArray, cid)

    (* fixityLookup qid = fixity
       where fixity is the fixity associated with constant named qid,
       defaults to Fixity.Nonfix if qid or fixity are undeclared
    *)
    let rec fixityLookup qid =
        (case constLookup qid
           of NONE => Fixity.Nonfix
            | SOME cid => getFixity cid)

    (* Name Preferences *)
    (* ePref is the name preference for existential variables of given type *)
    (* uPref is the name preference for universal variables of given type *)

    (* installNamePref' (cid, (ePref, uPref)) see installNamePref *)
    let rec installNamePref' (cid, (ePref, uPref)) =
        let
          let L = IntSyn.constUni (cid)
          let _ = case L
                    of IntSyn.Type =>
                       raise Error ("Object constant " ^ qidToString (constQid cid) ^ " cannot be given name preference\n"
                                    ^ "Name preferences can only be established for type families")
                     | IntSyn.Kind => ()
        in
          Array.update (namePrefArray, cid, SOME (ePref, uPref))
        end

    (* installNamePref (cid, (ePref, uPrefOpt)) = ()
       Effect: install name preference for type family cid
       raise Error if cid does not refer to a type family
    *)
    let rec installNamePref = function (cid, (ePref, nil)) -> 
          installNamePref' (cid, (ePref, [String.map Char.toLower (hd ePref)]))
      | (cid, (ePref, uPref)) -> 
          installNamePref' (cid, (ePref, uPref))

    let rec getNamePref cid = Array.sub (namePrefArray, cid)

    let rec installComponents (mid, namespace) =
          Array.update (componentsArray, mid, namespace)

    let rec getComponents mid =
          Array.sub (componentsArray, mid)

    (* local names are more easily re-used: they don't increment the
       counter associated with a name
    *)
    type Extent = Local | Global
    type Role = Exist | Univ of Extent

    let rec extent = function (Exist) -> Global
      | (Univ (ext)) -> ext

    let rec namePrefOf'' = function (Exist, NONE) -> "X"
      | (Univ _, NONE) -> "x"
      | (Exist, SOME(ePref, uPref)) -> hd ePref
      | (Univ _, SOME(ePref, uPref)) -> hd uPref

    let rec namePrefOf' = function (Exist, NONE) -> "X"
      | (Univ _, NONE) -> "x"
      | (role, SOME(IntSyn.Const cid)) -> namePrefOf'' (role, Array.sub (namePrefArray, cid))
      | (role, SOME(IntSyn.Def cid)) -> namePrefOf'' (role, Array.sub (namePrefArray, cid))
        (* the following only needed because reconstruction replaces
           undetermined types with FVars *)
      | (role, SOME(IntSyn.FVar _)) -> namePrefOf'' (role, NONE)

      | (role, SOME(IntSyn.NSDef cid)) -> namePrefOf'' (role, Array.sub (namePrefArray, cid))

    (* namePrefOf (role, V) = name
       where name is the preferred base name for a variable with type V

       V should be a type, but the code is robust, returning the default "X" or "x"
    *)
    let rec namePrefOf (role, V) = namePrefOf' (role, IntSyn.targetHeadOpt V)

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
    type varEntry = EVAR of IntSyn.exp (* X *)
      (* remove this type? -kw *)

    (* varTable mapping identifiers (strings) to EVars and FVars *)
    (* A hashtable is too inefficient, since it is cleared too often; *)
    (* so we use a red/black trees instead *)
    let varTable : varEntry StringTree.Table = StringTree.new (0) (* initial size hint *)
    let varInsert = StringTree.insert varTable
    let varLookup = StringTree.lookup varTable
    let rec varClear () = StringTree.clear varTable

    (* what is this for?  -kw *)
    let varContext : IntSyn.dctx ref = ref IntSyn.Null

    (* evarList mapping EVars to names *)
    (* names are assigned only when EVars are parsed or printed *)
    (* the mapping must be implemented as an association list *)
    (* since EVars are identified by reference *)
    (* an alternative becomes possible if time stamps are introduced *)
    let evarList : (IntSyn.exp * string) list ref = ref nil

    let rec evarReset () = (evarList := nil)
    let rec evarLookup (X) =
        let fun evlk (r, nil) = NONE
              | evlk (r, (IntSyn.EVar(r',_,_,_), name)::l) =
                if r = r' then SOME(name) else evlk (r, l)
              | evlk (r, ((IntSyn.AVar(r'), name)::l)) =
                if r = r' then SOME(name) else evlk (r, l)
        in
          case X of
            IntSyn.EVar(r,_,_,_) => evlk (r, (!evarList))
          | IntSyn.AVar(r) => evlk (r, (!evarList))
        end
    let rec evarInsert entry = (evarList := entry::(!evarList))

    let rec namedEVars () = !evarList

    (* Since constraints are not printable at present, we only *)
    (* return a list of names of EVars that have constraints on them *)
    (* Note that EVars which don't have names, will not be considered! *)
    let rec evarCnstr' = function (nil, acc) -> acc
      | ((Xn as (IntSyn.EVar(ref(NONE), _, _, cnstrs), name))::l, acc) -> 
          (case Constraints.simplify (!cnstrs)
             of nil => evarCnstr' (l, acc)
              | (_::_) => evarCnstr' (l, Xn::acc))
      | (_::l, acc) -> evarCnstr' (l, acc)
    let rec evarCnstr () = evarCnstr' (!evarList, nil)

    (* The indexTable maps a name to the last integer suffix used for it.
       The resulting identifer is not guaranteed to be new, and must be
       checked against the names of constants, FVars, EVars, and BVars.
    *)
    let indexTable : int StringTree.Table = StringTree.new (0)
    let indexInsert = StringTree.insert indexTable
    let indexLookup = StringTree.lookup indexTable
    let rec indexClear () = StringTree.clear indexTable

    let rec nextIndex' = function (name, NONE) -> (indexInsert (name, 1); 1)
      | (name, SOME(i)) -> (indexInsert (name, i+1); i+1)

    (* nextIndex (name) = i
       where i is the next available integer suffix for name,
       starting at 1.
       Effect: initialize or increment the indexTable entry for name
    *)
    let rec nextIndex (name) = nextIndex' (name, indexLookup (name))
  in
    (* varReset () = ()
       Effect: clear variable tables
       This must be called for each declaration or query
    *)
    let rec varReset G = (varClear (); evarReset (); indexClear ();
                      varContext := G)

    (* addEVar (X, name) = ()
       effect: adds (X, name) to varTable and evarList
       assumes name not already used *)
    let rec addEVar (X, name) =
        (evarInsert (X, name);
         varInsert (name, EVAR(X)))

    let rec getEVarOpt (name) =
        (case varLookup name
          of NONE => NONE
           | SOME(EVAR(X)) => SOME(X))

    (* varDefined (name) = true iff `name' refers to a free variable, *)
    (* which could be an EVar for constant declarations or FVar for queries *)
    let rec varDefined (name) =
        (case varLookup name
           of NONE => false
            | SOME _ => true)

    (* conDefined (name) = true iff `name' refers to a constant *)
    let rec conDefined (name) =
        (case constLookup (Qid (nil, name))
           of NONE => false
            | SOME _ => true)

    (* ctxDefined (G, name) = true iff `name' is declared in context G *)
    let rec ctxDefined (G, name) =
        let fun cdfd (IntSyn.Null) = false
              | cdfd (IntSyn.Decl(G', IntSyn.Dec(SOME(name'),_))) =
                  name = name' orelse cdfd G'
              | cdfd (IntSyn.Decl(G', IntSyn.BDec(SOME(name'),_))) =
                  name = name' orelse cdfd G'
              | cdfd (IntSyn.Decl(G', IntSyn.NDec(SOME(name')))) =
                  name = name' orelse cdfd G'
              | cdfd (IntSyn.Decl(G', _)) = cdfd G'
        in
          cdfd G
        end

    (* tryNextName (G, base) = baseN
       where N is the next suffix such that baseN is unused in
       G, as a variable, or as a constant.
    *)
    let rec tryNextName (G, base) =
        let
          let name = base ^ Int.toString (nextIndex (base))
        in
          if varDefined name orelse conDefined name
             orelse ctxDefined (G,name)
            then tryNextName (G, base)
          else name
        end

    let rec findNameLocal (G, base, i) =
        let let name = base ^ (if i = 0 then "" else Int.toString (i))
        in
          if varDefined name orelse conDefined name
             orelse ctxDefined (G, name)
            then findNameLocal (G, base, i+1)
          else name
        end

    let rec findName = function (G, base, Local) -> findNameLocal (G, base, 0)
      | (G, base, Global) -> tryNextName (G, base)


    let takeNonDigits = Substring.takel (not o Char.isDigit)

    (* baseOf (name) = name',
       where name' is the prefix of name not containing a digit
    *)
    let rec baseOf (name) = Substring.string (takeNonDigits (Compat.Substring.full name))

    (* newEvarName (G, X) = name
       where name is the next unused name appropriate for X,
       based on the name preference declaration for A if X:A
    *)
    let rec newEVarName = function (G, X as IntSyn.EVar(r, _, V, Cnstr)) -> 
        let
          (* use name preferences below *)
          let name = tryNextName (G, namePrefOf (Exist, V))
        in
          (evarInsert (X, name);
           name)
        end
      | (G, X as IntSyn.AVar(r)) -> 
        let
          (* use name preferences below *)
          let name = tryNextName (G, namePrefOf' (Exist, NONE))
        in
          (evarInsert (X, name);
           name)
        end

    (* evarName (G, X) = name
       where `name' is the print name X.
       If no name has been assigned yet, assign a new one.
       Effect: if a name is assigned, update varTable
    *)
    let rec evarName (G, X) =
        (case evarLookup X
           of NONE => let
                        let name = newEVarName (G, X)
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
    let rec bvarName (G, k) =
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
    let rec decName' = function role (G, IntSyn.Dec (NONE, V)) -> 
        let
          let name = findName (G, namePrefOf (role, V), extent (role))
        in
          IntSyn.Dec (SOME(name), V)
        end
      | role (G, D as IntSyn.Dec (SOME(name), V)) -> 
        if varDefined name orelse conDefined name
          orelse ctxDefined (G, name)
          then IntSyn.Dec (SOME (tryNextName (G, baseOf name)), V)
        else D
      | role (G, D as IntSyn.BDec (NONE, b as (cid, t))) -> 
        (* use #l as base name preference for label l *)
        let
          let name = findName (G, "#" ^ IntSyn.conDecName (IntSyn.sgnLookup cid), Local)
        in
          IntSyn.BDec (SOME(name), b)
        end
      | role (G, D as IntSyn.BDec (SOME(name), b as (cid, t))) -> 
        if varDefined name orelse conDefined name
          orelse ctxDefined (G, name)
          then IntSyn.BDec (SOME (tryNextName (G, baseOf name)), b)
        else D
      | role (G, IntSyn.ADec (NONE, d)) -> 
        let
          let name = findName (G, namePrefOf' (role, NONE), extent (role))
        in
          IntSyn.ADec (SOME(name), d)
        end
      | role (G, D as IntSyn.ADec (SOME(name), d)) -> 
(*      IntSyn.ADec(SOME(name), d) *)
        if varDefined name orelse conDefined name
          orelse ctxDefined (G, name)
          then IntSyn.ADec (SOME (tryNextName (G, baseOf name)), d)
        else D
      | decName' role (G, D as IntSyn.NDec NONE) =
        let
          let name = findName (G, "@x", Local)
            let _ = print name

        in
          IntSyn.NDec (SOME name)
        end
      | decName' role (G, D as IntSyn.NDec (SOME name)) =
        if varDefined name orelse conDefined name
          orelse ctxDefined (G, name)
          then IntSyn.NDec (SOME (tryNextName (G, baseOf name)))
        else D

    let decName = decName' Exist
    let decEName = decName' Exist
    let decUName = decName' (Univ (Global))
    let decLUName = decName' (Univ (Local))

    (* ctxName G = G'

        Invariant:
        |- G == G' ctx
        where some Declaration in G' have been named/renamed
    *)
    let rec ctxName = function (IntSyn.Null) -> IntSyn.Null
      | (IntSyn.Decl (G, D)) -> 
        let
          let G' = ctxName G
        in
          IntSyn.Decl (G', decName (G', D))
        end

    (* ctxLUName G = G'
       like ctxName, but names assigned are local universal names.
    *)
    let rec ctxLUName = function (IntSyn.Null) -> IntSyn.Null
      | (IntSyn.Decl (G, D)) -> 
        let
          let G' = ctxLUName G
        in
          IntSyn.Decl (G', decLUName (G', D))
        end

    (* pisEName' (G, i, V) = V'
       Assigns names to dependent Pi prefix of V with i implicit abstractions
       Used for implicit EVar in constant declarations after abstraction.
    *)
    let rec pisEName' = function (G, 0, V) -> V
      | (G, i, IntSyn.Pi ((D, IntSyn.Maybe), V)) -> 
        (* i > 0 *)
        let
          let D' = decEName (G, D)
        in
          IntSyn.Pi ((D', IntSyn.Maybe),
                     pisEName' (IntSyn.Decl (G, D'), i-1, V))
        end
      (* | pisEName' (G, i, V) = V *)

    let rec pisEName (i, V) = pisEName' (IntSyn.Null, i, V)

    (* defEName' (G, i, (U,V)) = (U',V')
       Invariant: G |- U : V  and G |- U' : V' since U == U' and V == V'.
       Assigns name to dependent Pi prefix of V and corresponding lam prefix of U
       with i implicit abstractions
       Used for implicit EVar in constant definitions after abstraction.
    *)
    let rec defEName' = function (G, 0, UV) -> UV
      | (G, i, (IntSyn.Lam (D, U), IntSyn.Pi ((_ (* -> D *), P), V))) =
        (* i > 0 *)
        let
          let D' = decEName (G, D)
          let (U', V') = defEName' (IntSyn.Decl (G, D'), i-1, (U, V))
        in
          (IntSyn.Lam (D', U'), IntSyn.Pi ((D', P), V'))
        end
      (* | defEName' (G, i, (U, V)) = (U, V) *)

    let rec defEName (imp, UV) = defEName' (IntSyn.Null, imp, UV)

    let rec nameConDec' = function (IntSyn.ConDec (name, parent, imp, status, V, L)) -> 
          IntSyn.ConDec (name, parent, imp, status, pisEName (imp, V), L)
      | (IntSyn.ConDef (name, parent, imp, U, V, L, Anc)) -> 
        let
          let (U', V') = defEName (imp, (U, V))
        in
          IntSyn.ConDef (name, parent, imp, U', V', L, Anc)
        end
      | (IntSyn.AbbrevDef (name, parent, imp, U, V, L)) -> 
        let
          let (U', V') = defEName (imp, (U, V))
        in
          IntSyn.AbbrevDef (name, parent, imp, U', V', L)
        end
      | (skodec) -> skodec (* fix ??? *)

    (* Assigns names to variables in a constant declaration *)
    (* The varReset (); is necessary so that explicitly named variables keep their name *)
    let rec nameConDec (conDec) =
        (varReset IntSyn.Null;                  (* declaration is always closed *)
         nameConDec' conDec)

    let rec skonstName (name) =
          tryNextName (IntSyn.Null, name)

    let namedEVars = namedEVars
    let evarCnstr = evarCnstr

  end  (* local varTable ... *)

end;; (* functor Names *)
