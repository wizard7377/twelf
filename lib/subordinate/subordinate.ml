(* Subordination a la Virga [Technical Report 96] *)
(* Author: Carsten Schuermann *)

(* Reverse subordination order *)

module Subordinate
  (Global : GLOBAL)
   (*! module IntSyn' : INTSYN !*)
   (Whnf : WHNF)
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   (Names : NAMES)
   (*! sharing Names.IntSyn = IntSyn' !*)
   (Table : TABLE with type key = int)
   (MemoTable : TABLE with type key = int * int)
   (IntSet : INTSET): SUBORDINATE =
struct
  (*! module IntSyn = IntSyn' !*)

  exception Error of string

  local
    module I = IntSyn

    (* Subordination graph

       soGraph is valid
       iff for any type families a and b
       if b > a then there a path from b to a in the graph.

       Subordination is transitive, but not necessarily reflexive.
    *)
    let soGraph : (IntSet.intset) Table.Table = Table.new (32)
    let insert = Table.insert soGraph
    let rec adjNodes a = valOf (Table.lookup soGraph a)  (* must be defined! *)
    let rec insertNewFam a =
           Table.insert soGraph (a, IntSet.empty)
    let updateFam = Table.insert soGraph

    (* memotable to avoid repeated graph traversal *)
    (* think of hash-table model *)
    let memoTable : (bool * int) MemoTable.Table = MemoTable.new (2048)
    let memoInsert = MemoTable.insert memoTable
    let memoLookup = MemoTable.lookup memoTable
    let memoClear = fn () => MemoTable.clear memoTable
    let memoCounter = ref 0

    (* Apply f to every node reachable from b *)
    (* Includes the node itself (reflexive) *)
    let rec appReachable f b =
        let fun rch (b, visited) =
                if IntSet.member (b, visited)
                  then visited
                else (f b ;
                      IntSet.foldl rch (IntSet.insert (b, visited)) (adjNodes b))
        in
          (rch (b, IntSet.empty) ; ())
        end

    exception Reachable
    let rec reach (b, a, visited) =
        let fun rch (b, visited) =
                if IntSet.member (b, visited)
                  then visited
                else let let adj = adjNodes b
                     in
                       if IntSet.member (a, adj)
                         then raise Reachable
                       else IntSet.foldl rch (IntSet.insert (b, visited)) adj
                     end
        in
          rch  (b, visited)
        end

    let rec reachable (b, a) = reach (b, a, IntSet.empty)

    (* b must be new *)
    (* this is sometimes violated below, is this a bug? *)
    (* Thu Mar 10 13:13:01 2005 -fp *)
    let rec addNewEdge (b, a) =
        ( memoCounter := !memoCounter+1 ;
          memoInsert ((b,a), (true, !memoCounter)) ;
          updateFam (b, IntSet.insert(a,adjNodes(b))) )

    let fTable : bool Table.Table = Table.new (32)
    let fLookup = Table.lookup fTable
    let fInsert = Table.insert fTable

    (*
       Freezing type families

       Frozen type families cannot be extended later with additional
       constructors.
     *)
    let rec fGet (a) =
        (case fLookup a
           of SOME frozen => frozen
            | NONE => false)

    let rec fSet (a, frozen) =
        let let _ = Global.chPrint 5
                    (fn () => (if frozen then "Freezing " else "Thawing ")
                              ^ Names.qidToString (Names.constQid a) ^ "\n")
        in
          fInsert (a, frozen)
        end

    (* pre: a is not a type definition *)
    let rec checkFreeze (c, a) =
        if fGet a
        then raise Error ("Freezing violation: constant "
                          ^ Names.qidToString (Names.constQid (c))
                          ^ "\nextends type family "
                          ^ Names.qidToString (Names.constQid (a)))
        else ()

    (* no longer needed since freeze is now transitive *)
    (* Sat Mar 12 21:40:15 2005 -fp *)
    (*
    let rec frozenSubError (a, b) =
        raise Error ("Freezing violation: frozen type family "
                     ^ Names.qidToString (Names.constQid b)
                     ^ "\nwould depend on unfrozen type family "
                     ^ Names.qidToString (Names.constQid a))
    *)

    (* no longer needed since freeze is now transitive *)
    (* Sat Mar 12 21:40:15 2005 -fp *)
    (* pre: a, b are not type definitions *)
    (*
    let rec checkFrozenSub (a, b) =
        (case (fGet a, fGet b)
           of (false, true) => frozenSubError (a, b)
            | _ => ())
    *)

    (* pre: b is not a type definition *)
    (* no longer needed since freeze is transitive *)
    (* Sat Mar 12 21:38:58 2005 -fp *)
    (*
    let rec checkMakeFrozen (b, otherFrozen) =
        (* Is this broken ??? *)
        (* Mon Nov 11 16:54:29 2002 -fp *)
        (* Example:
           a : type.
           b : type.
           %freeze a b.
           h : (a -> b) -> type.
           is OK, but as b |> a in its subordination
        *)
        let
          let rec check a =
            if fGet a orelse List.exists (fun x -> x = a) otherFrozen
              then ()
            else frozenSubError (a, b)
        in
          if fGet b then ()
          else appReachable check b
        end
    *)

    let rec expandFamilyAbbrevs a =
        (case I.constUni a
           of I.Type => raise Error ("Constant " ^ Names.qidToString (Names.constQid a)
                                     ^ " must be a type family to be frozen or thawed")
            | I.Kind =>
        (case IntSyn.sgnLookup a
           of IntSyn.conDec _ => a
            | IntSyn.ConDef _ =>
                IntSyn.targetFam (IntSyn.constDef a)
            | IntSyn.SkoDec _ => a
            | IntSyn.AbbrevDef _ =>
                IntSyn.targetFam (IntSyn.constDef a)))

    (* superseded by freeze *)
    (*
    let rec installFrozen (L) =
        let
          let L = map expandFamilyAbbrevs L
          (* let _ = print ("L = " ^ (foldl (fn (c,s) => Names.qidToString (Names.constQid c) ^ s) "\n" L)); *)
        in
          List.app (fun a -> checkMakeFrozen (a, L)) L;
          List.app (fun a -> fSet (a, true)) L
        end
    *)

    (* freeze L = ()
       freezes all families in L, and all families transitively
       reachable from families in L

       Intended to be called from programs
    *)
    let freezeList : IntSet.intset ref = ref IntSet.empty
    let rec freeze (L) =
        let
          let _ = freezeList := IntSet.empty
          let L' = map expandFamilyAbbrevs L
          let _ = List.app (fun a ->
                            appReachable (fun b ->
                                          (fSet (b, true);
                                           freezeList := IntSet.insert(b, !freezeList))) a)
                  L'
          let cids = IntSet.foldl (op::) nil (!freezeList)
        in
          cids
        end

    (* frozen L = true if one of the families in L is frozen *)
    let rec frozen (L) =
        let
          let L' = map expandFamilyAbbrevs L
        in
          List.exists (fun a -> fGet a) L'
        end

    (* a <| b = true iff a is (transitively) subordinate to b

       Invariant: a, b families
    *)
    let rec computeBelow (a, b) =
        (reachable (b, a); memoInsert ((b,a), (false,!memoCounter)); false)
        handle Reachable => (memoInsert ((b,a), (true, !memoCounter)); true)

    let rec below (a, b) =
        case memoLookup (b, a)
          of NONE => computeBelow (a, b)
           | SOME(true,c) => true       (* true entries remain valid *)
           | SOME(false,c) => if c = !memoCounter then false
                              else computeBelow (a, b) (* false entries are invalidated *)

    (* a <* b = true iff a is transitively and reflexively subordinate to b

       Invariant: a, b families
    *)
    let rec belowEq (a, b) = (a = b) orelse below (a, b)

    (* a == b = true iff a and b subordinate each other

       Invariant: a, b families
    *)
    let rec equiv (a, b) = belowEq (a, b) andalso belowEq (b, a)

    let rec addSubord (a, b) =
        if below (a, b) then ()
        else if fGet b
               (* if b is frozen and not already b #> a *)
               (* subordination would change; signal error *)
               then raise Error ("Freezing violation: "
                                 ^ Names.qidToString (Names.constQid b)
                                 ^ " would depend on "
                                 ^ Names.qidToString (Names.constQid a))
             else addNewEdge (b, a)

    (* Thawing frozen families *)
    (* Returns list of families that were thawed *)
    let aboveList : IntSyn.cid list ref = ref nil
    let rec addIfBelowEq a's =
        fun b -> if List.exists (fun a -> belowEq (a, b)) a's
                  then aboveList := b::(!aboveList)
                else ()

    let rec thaw a's =
        let
          let a's' = map expandFamilyAbbrevs a's
          let _ = aboveList := nil
          let _ = Table.app (fn (b,_) => addIfBelowEq a's' b) soGraph;
          let _ = List.app (fun b -> fSet(b, false)) (!aboveList)
        in
          !aboveList
        end

    (*
       Definition graph
       The definitions graph keeps track of chains of
       definitions for type families (not object-level definitions)

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
    let defGraph : (IntSet.intset) Table.Table = Table.new (32)

    (* occursInDef a = true
       iff there is a b such that a #> b
    *)
    let rec occursInDef a =
        (case Table.lookup defGraph a
           of NONE => false
            | SOME _ => true)

    (* insertNewDef (b, a) = ()
       Effect: update definition graph.

       Call this upon seeing a type-level definition
           b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S : K
       to record a #> b.
    *)
    let rec insertNewDef (b, a) =
        (case Table.lookup defGraph a
           of NONE => Table.insert defGraph (a, IntSet.insert (b, IntSet.empty))
            | SOME(bs) => Table.insert defGraph (a, IntSet.insert (b, bs)))

    (* installDef (c) = ()
       Effect: if c is a type-level definition,
               update definition graph.
    *)
    let rec installConDec = function (b, I.ConDef (_, _, _, A, K, I.Kind, _)) -> 
          (* I.targetFam must be defined, but expands definitions! *)
          insertNewDef (b, I.targetFam A)
      | _ -> ()

    let rec installDef c = installConDec (c, I.sgnLookup c)

    (* checkNoDef a = ()
       Effect: raises Error(msg) if there exists a b such that b <# a
               or b <# a' for some a' < a.
    *)
    let rec checkNoDef a =
        if occursInDef a
          then raise Error ("Definition violation: family "
                            ^ Names.qidToString (Names.constQid a)
                            ^ "\noccurs as right-hand side of type-level definition")
        else appReachable (fn a' =>
             if occursInDef a'
               then raise Error ("Definition violation: family "
                                 ^ Names.qidToString (Names.constQid a)
                                 ^ " |> "
                                 ^ Names.qidToString (Names.constQid a')
                                 ^ ",\nwhich occurs as right-hand side of a type-level definition")
             else ())
             a

    (* reset () = ()

       Effect: Empties soGraph, fTable, defGraph
    *)
    let rec reset () = (Table.clear soGraph;
                    Table.clear fTable;
                    MemoTable.clear memoTable;
                    Table.clear defGraph)

    (*
       Subordination checking no longer traverses spines,
       so approximate types are no longer necessary.
       This takes stronger advantage of the normal form invariant.
       Mon Nov 11 16:59:52 2002  -fp
    *)

    (* installTypeN' (V, a) = ()
       installTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: add subordination info from V into table
    *)
    and installTypeN' (I.Pi ((D as I.Dec (_, V1), _), V2), a) =
          (addSubord (I.targetFam V1, a);
           installTypeN (V1);
           installTypeN' (V2, a))
      | installTypeN' (V as I.Root (I.Def _, _), a) =
        (* this looks like blatant overkill ... *)
        (* Sun Nov 10 11:15:47 2002 -fp *)
        let
          let V' = Whnf.normalize (Whnf.expandDef (V, I.id))
        in
          installTypeN' (V', a)
        end
      | installTypeN' (I.Root _, _) = ()
    and installTypeN (V) = installTypeN' (V, I.targetFam V)

    (* installKindN (V, a) = ()
       V nf, a : {x1:A1}...{xn:An} type, V = {xi:Ai}...{xn:An}type
       Effect: add subordination info from V into table
    *)
    (* there are no kind-level definitions *)
    let rec installKindN = function (I.Uni(L), a) -> ()
      | (I.Pi ((I.Dec (_, V1), P), V2), a) -> 
          (addSubord (I.targetFam V1, a);
           installTypeN (V1);
           installKindN (V2, a))

    (* install c = ()

       Effect: if c : V, add subordination from V into table
    *)
    let rec install c =
        let
          let V = I.constType c
        in
          case I.targetFamOpt V
            of NONE => (insertNewFam (c);
                        installKindN (V, c))
             | SOME a => (case IntSyn.sgnLookup c
                            of IntSyn.conDec _ => checkFreeze (c, a)
                             | IntSyn.SkoDec _ => checkFreeze (c, a)
                               (* FIX: skolem types should probably be created frozen -kw *)
                             | _ => ();
                          (* simplified  Tue Mar 27 20:58:31 2001 -fp *)
                          installTypeN' (V, a))
        end

    (* installBlock b = ()
       Effect: if b : Block, add subordination from Block into table
    *)
    (* BDec, ADec, NDec are disallowed here *)
    let rec installDec (I.Dec(_,V)) = installTypeN V

    let rec installSome = function (I.Null) -> ()
      | (I.Decl(G, D)) -> 
        ( installSome G; installDec D )

    (* b must be block *)
    let rec installBlock b =
        let
          let I.BlockDec(_, _, G, Ds) = I.sgnLookup b
        in
          installSome G;
          List.app (fun D -> installDec D) Ds
        end

    (* Respecting subordination *)

    (* checkBelow (a, b) = () iff a <| b
       Effect: raise Error(msg) otherwise
    *)
    let rec checkBelow (a, b) =
        if not (below (a, b))
          then raise Error ("Subordination violation: "
                            ^ Names.qidToString (Names.constQid (a)) ^ " not <| " ^ Names.qidToString (Names.constQid (b)))
        else ()

    (* respectsTypeN' (V, a) = () iff V respects current subordination
       respectsTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: raise Error (msg)
    *)
    let rec respectsTypeN' = function (I.Pi ((D as I.Dec (_, V1), _), V2), a) -> 
          (checkBelow (I.targetFam V1, a);
           respectsTypeN (V1);
           respectsTypeN' (V2, a))
      | (V as I.Root (I.Def _, _), a) -> 
        (* this looks like blatant overkill ... *)
        (* Sun Nov 10 11:15:47 2002 -fp *)
        let
          let V' = Whnf.normalize (Whnf.expandDef (V, I.id))
        in
          respectsTypeN' (V', a)
        end
      | (I.Root _, _) -> ()
    and respectsTypeN (V) = respectsTypeN' (V, I.targetFam V)

    let rec respects (G, (V, s)) = respectsTypeN (Whnf.normalize (V, s))
    let rec respectsN (G, V) = respectsTypeN (V)

    (* Printing *)

    (* Right now, AL is in always reverse order *)
    (* Reverse again --- do not sort *)
    (* Right now, Table.app will pick int order -- do not sort *)
    let rec famsToString (bs, msg) =
        IntSet.foldl (fn (a, msg) => Names.qidToString (Names.constQid a) ^ " " ^ msg) "\n" bs
    (*
    let rec famsToString = function (nil, msg) -> msg
      | (a::AL, msg) -> famsToString (AL, Names.qidToString (Names.constQid a) ^ " " ^ msg)
    *)

    let rec showFam (a, bs) =
        (print (Names.qidToString (Names.constQid a)
                ^ (if fGet a then " #> " else " |> ")
                ^ famsToString (bs, "\n")))

    let rec show () = Table.app showFam soGraph;


    (* weaken (G, a) = (w') *)
    let rec weaken = function (I.Null, a) -> I.id
      | (I.Decl (G', D as I.Dec (name, V)), a) -> 
        let
          let w' = weaken (G', a)
        in
          if belowEq (I.targetFam V, a) then I.dot1 w'
          else I.comp (w', I.shift)
        end


    (* showDef () = ()
       Effect: print some statistics about constant definitions
    *)
    local
      let declared = ref 0
      let defined = ref 0
      let abbrev = ref 0
      let other = ref 0
      let heightArray = Array.array (32, 0)
      let maxHeight = ref 0

      let rec inc (r) = (r := !r+1)
      let rec incArray (h) = (Array.update (heightArray, h, Array.sub (heightArray, h)+1))
      (* ignore blocks and skolem constants *)
      let rec max (h) = (maxHeight := Int.max (h, !maxHeight))
      let rec reset () = (declared := 0; defined := 0; abbrev := 0; other := 0;
                      Array.modify (fun i -> 0) heightArray;
                      maxHeight := 0)
    in
      let rec analyzeAnc (I.Anc (NONE, _, _)) = ( incArray 0 )
        | analyzeAnc (I.Anc (_, h, _)) = ( incArray h ; max h )
      let rec analyze (I.ConDec (_, _, _, _, _, L)) =
          ( inc declared )
        | analyze (I.ConDef (_, _, _, _, _, L, ancestors)) =
          ( inc defined ; analyzeAnc ancestors )
        | analyze (I.AbbrevDef (_, _, _, _, _, L)) =
          ( inc abbrev )
        | analyze _ = ( inc other )
      let rec showDef () =
          let
            let _ = reset ()
            let _ = I.sgnApp (fun c -> analyze (I.sgnLookup c))
            let _ = print ("Declared: " ^ Int.toString (!declared) ^ "\n")
            let _ = print ("Defined : " ^ Int.toString (!defined) ^ "\n")
            let _ = print ("Abbrevs : " ^ Int.toString (!abbrev) ^ "\n")
            let _ = print ("Other   : " ^ Int.toString (!other) ^ "\n")
            let _ = print ("Max definition height: " ^ Int.toString (!maxHeight) ^ "\n")
            let _ = ArraySlice.appi
                      (fn (h, i) => print (" Height " ^ Int.toString h ^ ": "
                                           ^ Int.toString i ^ " definitions\n"))
                      (ArraySlice.slice (heightArray, 0, SOME(!maxHeight+1)))
          in
            ()
          end
    end
  in
    let reset = reset

    let install = install
    let installDef = installDef
    let installBlock = installBlock

    (* let installFrozen = installFrozen *)

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

  end (* local *)
end;; (* functor Subordinate *)
