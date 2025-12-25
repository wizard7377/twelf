open Basis
(* Subordination *)

(* Author: Carsten Schuermann *)

(* Modified: Frank Pfenning *)

module type SUBORDINATE = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> unit
  val installDef : IntSyn.cid -> unit
  val installBlock : IntSyn.cid -> unit

  (* val installFrozen : IntSyn.cid list -> unit *)
  (* superseded by freeze *)
  val freeze : IntSyn.cid list -> IntSyn.cid list

  (* transitive freeze, returns frozen cids *)
  val thaw : IntSyn.cid list -> IntSyn.cid list

  (* reverse transitive thaw, returns thawed cids *)
  val frozen : IntSyn.cid list -> bool

  (* any cid in list frozen? *)
  val addSubord : IntSyn.cid * IntSyn.cid -> unit
  val below : IntSyn.cid * IntSyn.cid -> bool

  (* transitive closure *)
  val belowEq : IntSyn.cid * IntSyn.cid -> bool

  (* refl. transitive closure *)
  val equiv : IntSyn.cid * IntSyn.cid -> bool

  (* mutual dependency *)
  val respects : IntSyn.dctx * IntSyn.eclo -> unit

  (* respects current subordination? *)
  val respectsN : IntSyn.dctx * IntSyn.exp -> unit

  (* respectsN(G, V), V in nf *)
  val checkNoDef : IntSyn.cid -> unit

  (* not involved in type-level definition? *)
  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.sub
  val show : unit -> unit
  val showDef : unit -> unit
end

(* signature SUBORDINATE *)
(* Subordination a la Virga [Technical Report 96] *)

(* Author: Carsten Schuermann *)

(* Reverse subordination order *)

module Subordinate
    (Global : Global.GLOBAL)
    (Whnf : Whnf.WHNF)
    (Names : Names.NAMES)
    (IntSet : Intset.INTSET) : SUBORDINATE = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  module I = IntSyn
  (* Subordination graph

       soGraph is valid
       iff for_sml any type families a and b
       if b > a then there a path from b to a in the graph.

       Subordination is transitive, but not necessarily reflexive.
    *)

  let soGraph : IntSet.intset Table.table = Table.new_ 32
  let insert = Table.insert soGraph
  let rec adjNodes a = valOf (Table.lookup soGraph a)
  (* must be defined! *)

  let rec insertNewFam a = Table.insert soGraph (a, IntSet.empty)
  let updateFam = Table.insert soGraph
  (* memotable to avoid repeated graph traversal *)

  (* think of hash-table model *)

  let memoTable : bool * int MemoTable.table = MemoTable.new_ 2048
  let memoInsert = MemoTable.insert memoTable
  let memoLookup = MemoTable.lookup memoTable
  let memoClear = fun () -> MemoTable.clear memoTable
  let memoCounter = ref 0
  (* Apply f to every node reachable from b *)

  (* Includes the node itself (reflexive) *)

  let rec appReachable f b =
    let rec rch (b, visited) =
      if IntSet.member (b, visited) then visited
      else (
        f b;
        IntSet.foldl rch (IntSet.insert (b, visited)) (adjNodes b))
    in
    rch (b, IntSet.empty);
    ()

  exception Reachable

  let rec reach (b, a, visited) =
    let rec rch (b, visited) =
      if IntSet.member (b, visited) then visited
      else
        let adj = adjNodes b in
        if IntSet.member (a, adj) then raise Reachable
        else IntSet.foldl rch (IntSet.insert (b, visited)) adj
    in
    rch (b, visited)

  let rec reachable (b, a) = reach (b, a, IntSet.empty)
  (* b must be new *)

  (* this is sometimes violated below, is this a bug? *)

  (* Thu Mar 10 13:13:01 2005 -fp *)

  let rec addNewEdge (b, a) =
    memoCounter := !memoCounter + 1;
    memoInsert ((b, a), (true, !memoCounter));
    updateFam (b, IntSet.insert (a, adjNodes b))

  let fTable : bool Table.table = Table.new_ 32
  let fLookup = Table.lookup fTable
  let fInsert = Table.insert fTable
  (*
       Freezing type families

       Frozen type families cannot be extended later with additional
       constructors.
     *)

  let rec fGet a = match fLookup a with Some frozen -> frozen | None -> false

  let rec fSet (a, frozen) =
    let _ =
      Global.chPrint 5 (fun () ->
          (if frozen then "Freezing " else "Thawing ")
          ^ Names.qidToString (Names.constQid a)
          ^ "\n")
    in
    fInsert (a, frozen)
  (* pre: a is not a type definition *)

  let rec checkFreeze (c, a) =
    if fGet a then
      raise
        (Error
           ("Freezing violation: constant "
           ^ Names.qidToString (Names.constQid c)
           ^ "\nextends type family "
           ^ Names.qidToString (Names.constQid a)))
    else ()
  (* no longer needed since freeze is now transitive *)

  (* Sat Mar 12 21:40:15 2005 -fp *)

  (*
    fun frozenSubError (a, b) =
        raise Error ("Freezing violation: frozen type family "
                     ^ Names.qidToString (Names.constQid b)
                     ^ "\nwould depend on unfrozen type family "
                     ^ Names.qidToString (Names.constQid a))
    *)

  (* no longer needed since freeze is now transitive *)

  (* Sat Mar 12 21:40:15 2005 -fp *)

  (* pre: a, b are not type definitions *)

  (*
    fun checkFrozenSub (a, b) =
        (case (fGet a, fGet b)
           of (false, true) => frozenSubError (a, b)
            | _ => ())
    *)

  (* pre: b is not a type definition *)

  (* no longer needed since freeze is transitive *)

  (* Sat Mar 12 21:38:58 2005 -fp *)

  (*
    fun checkMakeFrozen (b, otherFrozen) =
        (* Is this broken ??? *)
        (* Mon Nov 11 16:54:29 2002 -fp *)
        (* Example:
           a : type.
           b : type.
           %freeze a b.
           h : (a -> b) -> type.
           is OK, b |> a in its subordination
        *)
        let
          fun check a =
            if fGet a orelse List.exists (fn x => x = a) otherFrozen
              then ()
            else frozenSubError (a, b)
        in
          if fGet b then ()
          else appReachable check b
        end
    *)

  let rec expandFamilyAbbrevs a =
    match I.constUni a with
    | I.Type ->
        raise
          (Error
             ("Constant "
             ^ Names.qidToString (Names.constQid a)
             ^ " must be a type family to be frozen or thawed"))
    | I.Kind -> (
        match IntSyn.sgnLookup a with
        | IntSyn.ConDec _ -> a
        | IntSyn.ConDef _ -> IntSyn.targetFam (IntSyn.constDef a)
        | IntSyn.SkoDec _ -> a
        | IntSyn.AbbrevDef _ -> IntSyn.targetFam (IntSyn.constDef a))
  (* superseded by freeze *)

  (*
    fun installFrozen (L) =
        let
          val L = map expandFamilyAbbrevs L
          (* val _ = print ("L = " ^ (foldl (fn (c,s) => Names.qidToString (Names.constQid c) ^ s) "\n" L)); *)
        in
          List.app (fn a => checkMakeFrozen (a, L)) L;
          List.app (fn a => fSet (a, true)) L
        end
    *)

  (* freeze L = ()
       freezes all families in L, and all families transitively
       reachable from families in L

       Intended to be called from programs
    *)

  let freezeList : IntSet.intset ref = ref IntSet.empty

  let rec freeze L =
    let _ = freezeList := IntSet.empty in
    let L' = map expandFamilyAbbrevs L in
    let _ =
      List.app
        (fun a ->
          appReachable
            (fun b ->
              fSet (b, true);
              freezeList := IntSet.insert (b, !freezeList))
            a)
        L'
    in
    let cids = IntSet.foldl ( :: ) [] !freezeList in
    cids
  (* frozen L = true if one of the families in L is frozen *)

  let rec frozen L =
    let L' = map expandFamilyAbbrevs L in
    List.exists (fun a -> fGet a) L'
  (* a <| b = true iff a is (transitively) subordinate to b

       Invariant: a, b families
    *)

  let rec computeBelow (a, b) =
    try
      reachable (b, a);
      memoInsert ((b, a), (false, !memoCounter));
      false
    with Reachable ->
      memoInsert ((b, a), (true, !memoCounter));
      true

  let rec below (a, b) =
    match memoLookup (b, a) with
    | None -> computeBelow (a, b)
    | Some (true, c) -> true (* true entries remain valid *)
    | Some (false, c) -> if c = !memoCounter then false else computeBelow (a, b)
  (* false entries are invalidated *)

  (* a <* b = true iff a is transitively and reflexively subordinate to b

       Invariant: a, b families
    *)

  let rec belowEq (a, b) = a = b || below (a, b)
  (* a == b = true iff a and b subordinate each other

       Invariant: a, b families
    *)

  let rec equiv (a, b) = belowEq (a, b) && belowEq (b, a)

  let rec addSubord (a, b) =
    if below (a, b) then ()
    else if fGet b (* if b is frozen and not already b #> a *)
    (* subordination would change; signal error *)
    then
      raise
        (Error
           ("Freezing violation: "
           ^ Names.qidToString (Names.constQid b)
           ^ " would depend on "
           ^ Names.qidToString (Names.constQid a)))
    else addNewEdge (b, a)
  (* Thawing frozen families *)

  (* Returns list of families that were thawed *)

  let aboveList : IntSyn.cid list ref = ref []

  let rec addIfBelowEq a's =
   fun b ->
    if List.exists (fun a -> belowEq (a, b)) a's then
      aboveList := b :: !aboveList
    else ()

  let rec thaw a's =
    let a's' = map expandFamilyAbbrevs a's in
    let _ = aboveList := [] in
    let _ = Table.app (fun (b, _) -> addIfBelowEq a's' b) soGraph in
    let _ = List.app (fun b -> fSet (b, false)) !aboveList in
    !aboveList
  (*
       Definition graph
       The definitions graph keeps track of chains of
       definitions for_sml type families (not object-level definitions)

       We say b <# a if b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S

       The definition graph should be interpreted transitively.
       It can never be reflexive.

       The #> relation is stored in order to prevent totality
       checking on type families involved in definitions, because
       in the present implementation this would yield unsound
       results.

       NOTE: presently, the head "a" is always expanded until it is
       no longer a definition.  So if a #> b then a is always declared,
       never defined and b is always defined, never declared.

       Fri Dec 27 08:37:42 2002 -fp (just before 1.4 alpha)
    *)

  let defGraph : IntSet.intset Table.table = Table.new_ 32
  (* occursInDef a = true
       iff there is a b such that a #> b
    *)

  let rec occursInDef a =
    match Table.lookup defGraph a with None -> false | Some _ -> true
  (* insertNewDef (b, a) = ()
       Effect: update definition graph.

       Call this upon seeing a type-level definition
           b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S : K
       to record a #> b.
    *)

  let rec insertNewDef (b, a) =
    match Table.lookup defGraph a with
    | None -> Table.insert defGraph (a, IntSet.insert (b, IntSet.empty))
    | Some bs -> Table.insert defGraph (a, IntSet.insert (b, bs))
  (* installDef (c) = ()
       Effect: if c is a type-level definition,
               update definition graph.
    *)

  let rec installConDec = function
    | b, I.ConDef (_, _, _, A, K, I.Kind, _) -> insertNewDef (b, I.targetFam A)
    | _ -> ()

  let rec installDef c = installConDec (c, I.sgnLookup c)
  (* checkNoDef a = ()
       Effect: raises Error(msg) if there exists a b such that b <# a
               or b <# a' for_sml some a' < a.
    *)

  let rec checkNoDef a =
    if occursInDef a then
      raise
        (Error
           ("Definition violation: family "
           ^ Names.qidToString (Names.constQid a)
           ^ "\right-hand side of type-level definition"))
    else
      appReachable
        (fun a' ->
          if occursInDef a' then
            raise
              (Error
                 ("Definition violation: family "
                 ^ Names.qidToString (Names.constQid a)
                 ^ " |> "
                 ^ Names.qidToString (Names.constQid a')
                 ^ ",\nwhich right-hand side of a type-level definition"))
          else ())
        a
  (* reset () = ()

       Effect: Empties soGraph, fTable, defGraph
    *)

  let rec reset () =
    Table.clear soGraph;
    Table.clear fTable;
    MemoTable.clear memoTable;
    Table.clear defGraph

  and installTypeN' = function
    | I.Pi ((D, _), V2), a ->
        addSubord (I.targetFam V1, a);
        installTypeN V1;
        installTypeN' (V2, a)
    | V, a ->
        let V' = Whnf.normalize (Whnf.expandDef (V, I.id)) in
        installTypeN' (V', a)
    | I.Root _, _ -> ()

  and installTypeN V = installTypeN' (V, I.targetFam V)
  (* installKindN (V, a) = ()
       V nf, a : {x1:A1}...{xn:An} type, V = {xi:Ai}...{xn:An}type
       Effect: add subordination info from V into table
    *)

  (* there are no kind-level definitions *)

  let rec installKindN = function
    | I.Uni L, a -> ()
    | I.Pi ((I.Dec (_, V1), P), V2), a ->
        addSubord (I.targetFam V1, a);
        installTypeN V1;
        installKindN (V2, a)
  (* install c = ()

       Effect: if c : V, add subordination from V into table
    *)

  let rec install c =
    let V = I.constType c in
    match I.targetFamOpt V with
    | None ->
        insertNewFam c;
        installKindN (V, c)
    | Some a -> (
        match IntSyn.sgnLookup c with
        | IntSyn.ConDec _ -> checkFreeze (c, a)
        | IntSyn.SkoDec _ ->
            checkFreeze (c, a)
            (* FIX: skolem types should probably be created frozen -kw *)
        | _ ->
            ();
            (* simplified  Tue Mar 27 20:58:31 2001 -fp *)
            installTypeN' (V, a))
  (* installBlock b = ()
       Effect: if b : Block, add subordination from Block into table
    *)

  (* BDec, ADec, NDec are disallowed here *)

  let rec installDec (I.Dec (_, V)) = installTypeN V

  let rec installSome = function
    | I.Null -> ()
    | I.Decl (G, D) ->
        installSome G;
        installDec D
  (* b must be block *)

  let rec installBlock b =
    let (I.BlockDec (_, _, G, Ds)) = I.sgnLookup b in
    installSome G;
    List.app (fun D -> installDec D) Ds
  (* Respecting subordination *)

  (* checkBelow (a, b) = () iff a <| b
       Effect: raise Error(msg) otherwise
    *)

  let rec checkBelow (a, b) =
    if not (below (a, b)) then
      raise
        (Error
           ("Subordination violation: "
           ^ Names.qidToString (Names.constQid a)
           ^ " not <| "
           ^ Names.qidToString (Names.constQid b)))
    else ()
  (* respectsTypeN' (V, a) = () iff V respects current subordination
       respectsTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: raise Error (msg)
    *)

  let rec respectsTypeN' = function
    | I.Pi ((D, _), V2), a ->
        checkBelow (I.targetFam V1, a);
        respectsTypeN V1;
        respectsTypeN' (V2, a)
    | V, a ->
        let V' = Whnf.normalize (Whnf.expandDef (V, I.id)) in
        respectsTypeN' (V', a)
    | I.Root _, _ -> ()

  and respectsTypeN V = respectsTypeN' (V, I.targetFam V)

  let rec respects (G, (V, s)) = respectsTypeN (Whnf.normalize (V, s))
  let rec respectsN (G, V) = respectsTypeN V
  (* Printing *)

  (* Right now, AL is in always reverse order *)

  (* Reverse again --- do not sort *)

  (* Right now, Table.app will pick int order -- do not sort *)

  let rec famsToString (bs, msg) =
    IntSet.foldl
      (fun (a, msg) -> Names.qidToString (Names.constQid a) ^ " " ^ msg)
      "\n" bs
  (*
    fun famsToString (nil, msg) = msg
      | famsToString (a::AL, msg) = famsToString (AL, Names.qidToString (Names.constQid a) ^ " " ^ msg)
    *)

  let rec showFam (a, bs) =
    print
      (Names.qidToString (Names.constQid a)
      ^ (if fGet a then " #> " else " |> ")
      ^ famsToString (bs, "\n"))

  let rec show () = Table.app showFam soGraph
  (* weaken (G, a) = (w') *)

  let rec weaken = function
    | I.Null, a -> I.id
    | I.Decl (G', D), a ->
        let w' = weaken (G', a) in
        if belowEq (I.targetFam V, a) then I.dot1 w' else I.comp (w', I.shift)
  (* showDef () = ()
       Effect: print some statistics about constant definitions
    *)

  let declared = ref 0
  let defined = ref 0
  let abbrev = ref 0
  let other = ref 0
  let heightArray = Array.array (32, 0)
  let maxHeight = ref 0
  let rec inc r = r := !r + 1

  let rec incArray h =
    Array.update (heightArray, h, Array.sub (heightArray, h) + 1)
  (* ignore blocks and skolem constants *)

  let rec max h = maxHeight := Int.max (h, !maxHeight)

  let rec reset () =
    declared := 0;
    defined := 0;
    abbrev := 0;
    other := 0;
    Array.modify (fun i -> 0) heightArray;
    maxHeight := 0

  let rec analyzeAnc = function
    | I.Anc (None, _, _) -> incArray 0
    | I.Anc (_, h, _) ->
        incArray h;
        max h

  let rec analyze = function
    | I.ConDec (_, _, _, _, _, L) -> inc declared
    | I.ConDef (_, _, _, _, _, L, ancestors) ->
        inc defined;
        analyzeAnc ancestors
    | I.AbbrevDef (_, _, _, _, _, L) -> inc abbrev
    | _ -> inc other

  let rec showDef () =
    let _ = reset () in
    let _ = I.sgnApp (fun c -> analyze (I.sgnLookup c)) in
    let _ = print ("Declared: " ^ Int.toString !declared ^ "\n") in
    let _ = print ("Defined : " ^ Int.toString !defined ^ "\n") in
    let _ = print ("Abbrevs : " ^ Int.toString !abbrev ^ "\n") in
    let _ = print ("Other   : " ^ Int.toString !other ^ "\n") in
    let _ =
      print ("Max definition height: " ^ Int.toString !maxHeight ^ "\n")
    in
    let _ =
      ArraySlice.appi
        (fun (h, i) ->
          print
            (" Height " ^ Int.toString h ^ ": " ^ Int.toString i
           ^ " definitions\n"))
        (ArraySlice.slice (heightArray, 0, Some (!maxHeight + 1)))
    in
    ()

  let reset = reset
  let install = install
  let installDef = installDef
  let installBlock = installBlock
  (* val installFrozen = installFrozen *)

  let freeze = freeze
  let frozen = frozen
  let thaw = thaw
  let addSubord = addSubord
  let below = below
  let belowEq = belowEq
  let equiv = equiv
  let checkNoDef = checkNoDef
  let respects = respects
  let respectsN = respectsN
  let weaken = weaken
  let show = show
  let showDef = showDef
  (* local *)
end

(* functor Subordinate *)
