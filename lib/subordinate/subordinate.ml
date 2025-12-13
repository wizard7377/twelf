(* Subordination a la Virga [Technical Report 96] *)
(* Author: Carsten Schuermann *)

(* Reverse subordination order *)

functor (* GEN BEGIN FUNCTOR DECL *) Subordinate
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Table : TABLE where type key = int
   structure MemoTable : TABLE where type key = int * int
   structure IntSet : INTSET
     )
  : SUBORDINATE =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  local
    structure I = IntSyn

    (* Subordination graph

       soGraph is valid
       iff for any type families a and b
       if b > a then there a path from b to a in the graph.

       Subordination is transitive, but not necessarily reflexive.
    *)
    (* GEN BEGIN TAG OUTSIDE LET *) val soGraph : (IntSet.intset) Table.table = Table.new (32) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val insert = Table.insert soGraph (* GEN END TAG OUTSIDE LET *)
    fun adjNodes a = valOf (Table.lookup soGraph a)  (* must be defined! *)
    fun insertNewFam a =
           Table.insert soGraph (a, IntSet.empty)
    (* GEN BEGIN TAG OUTSIDE LET *) val updateFam = Table.insert soGraph (* GEN END TAG OUTSIDE LET *)

    (* memotable to avoid repeated graph traversal *)
    (* think of hash-table model *)
    (* GEN BEGIN TAG OUTSIDE LET *) val memoTable : (bool * int) MemoTable.table = MemoTable.new (2048) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val memoInsert = MemoTable.insert memoTable (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val memoLookup = MemoTable.lookup memoTable (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val memoClear = (* GEN BEGIN FUNCTION EXPRESSION *) fn () => MemoTable.clear memoTable (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val memoCounter = ref 0 (* GEN END TAG OUTSIDE LET *)

    (* Apply f to every node reachable from b *)
    (* Includes the node itself (reflexive) *)
    fun appReachable f b =
        let fun rch (b, visited) =
                if IntSet.member (b, visited)
                  then visited
                else (f b ;
                      IntSet.foldl rch (IntSet.insert (b, visited)) (adjNodes b))
        in
          (rch (b, IntSet.empty) ; ())
        end

    exception Reachable
    fun reach (b, a, visited) =
        let fun rch (b, visited) =
                if IntSet.member (b, visited)
                  then visited
                else let (* GEN BEGIN TAG OUTSIDE LET *) val adj = adjNodes b (* GEN END TAG OUTSIDE LET *)
                     in
                       if IntSet.member (a, adj)
                         then raise Reachable
                       else IntSet.foldl rch (IntSet.insert (b, visited)) adj
                     end
        in
          rch  (b, visited)
        end

    fun reachable (b, a) = reach (b, a, IntSet.empty)

    (* b must be new *)
    (* this is sometimes violated below, is this a bug? *)
    (* Thu Mar 10 13:13:01 2005 -fp *)
    fun addNewEdge (b, a) =
        ( memoCounter := !memoCounter+1 ;
          memoInsert ((b,a), (true, !memoCounter)) ;
          updateFam (b, IntSet.insert(a,adjNodes(b))) )

    (* GEN BEGIN TAG OUTSIDE LET *) val fTable : bool Table.table = Table.new (32) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val fLookup = Table.lookup fTable (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val fInsert = Table.insert fTable (* GEN END TAG OUTSIDE LET *)

    (*
       Freezing type families

       Frozen type families cannot be extended later with additional
       constructors.
     *)
    fun fGet (a) =
        (case fLookup a
           of SOME frozen => frozen
            | NONE => false)

    fun fSet (a, frozen) =
        let (* GEN BEGIN TAG OUTSIDE LET *) val _ = Global.chPrint 5
                    ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (if frozen then "Freezing " else "Thawing ")
                              ^ Names.qidToString (Names.constQid a) ^ "\n" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          fInsert (a, frozen)
        end

    (* pre: a is not a type definition *)
    fun checkFreeze (c, a) =
        if fGet a
        then raise Error ("Freezing violation: constant "
                          ^ Names.qidToString (Names.constQid (c))
                          ^ "\nextends type family "
                          ^ Names.qidToString (Names.constQid (a)))
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
           is OK, but as b |> a in its subordination
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

    fun expandFamilyAbbrevs a =
        (case I.constUni a
           of I.Type => raise Error ("Constant " ^ Names.qidToString (Names.constQid a)
                                     ^ " must be a type family to be frozen or thawed")
            | I.Kind =>
        (case IntSyn.sgnLookup a
           of IntSyn.ConDec _ => a
            | IntSyn.ConDef _ =>
                IntSyn.targetFam (IntSyn.constDef a)
            | IntSyn.SkoDec _ => a
            | IntSyn.AbbrevDef _ =>
                IntSyn.targetFam (IntSyn.constDef a)))

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
    (* GEN BEGIN TAG OUTSIDE LET *) val freezeList : IntSet.intset ref = ref IntSet.empty (* GEN END TAG OUTSIDE LET *)
    fun freeze (L) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = freezeList := IntSet.empty (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val L' = map expandFamilyAbbrevs L (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = List.app ((* GEN BEGIN FUNCTION EXPRESSION *) fn a =>
                            appReachable ((* GEN BEGIN FUNCTION EXPRESSION *) fn b =>
                                          (fSet (b, true);
                                           freezeList := IntSet.insert(b, !freezeList)) (* GEN END FUNCTION EXPRESSION *)) a (* GEN END FUNCTION EXPRESSION *))
                  L' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val cids = IntSet.foldl (op::) nil (!freezeList) (* GEN END TAG OUTSIDE LET *)
        in
          cids
        end

    (* frozen L = true if one of the families in L is frozen *)
    fun frozen (L) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val L' = map expandFamilyAbbrevs L (* GEN END TAG OUTSIDE LET *)
        in
          List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn a => fGet a (* GEN END FUNCTION EXPRESSION *)) L'
        end

    (* a <| b = true iff a is (transitively) subordinate to b

       Invariant: a, b families
    *)
    fun computeBelow (a, b) =
        (reachable (b, a); memoInsert ((b,a), (false,!memoCounter)); false)
        handle Reachable => (memoInsert ((b,a), (true, !memoCounter)); true)

    fun below (a, b) =
        case memoLookup (b, a)
          of NONE => computeBelow (a, b)
           | SOME(true,c) => true       (* true entries remain valid *)
           | SOME(false,c) => if c = !memoCounter then false
                              else computeBelow (a, b) (* false entries are invalidated *)

    (* a <* b = true iff a is transitively and reflexively subordinate to b

       Invariant: a, b families
    *)
    fun belowEq (a, b) = (a = b) orelse below (a, b)

    (* a == b = true iff a and b subordinate each other

       Invariant: a, b families
    *)
    fun equiv (a, b) = belowEq (a, b) andalso belowEq (b, a)

    fun addSubord (a, b) =
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
    (* GEN BEGIN TAG OUTSIDE LET *) val aboveList : IntSyn.cid list ref = ref nil (* GEN END TAG OUTSIDE LET *)
    fun addIfBelowEq a's =
        (* GEN BEGIN FUNCTION EXPRESSION *) fn b => if List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn a => belowEq (a, b) (* GEN END FUNCTION EXPRESSION *)) a's
                  then aboveList := b::(!aboveList)
                else () (* GEN END FUNCTION EXPRESSION *)

    fun thaw a's =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val a's' = map expandFamilyAbbrevs a's (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = aboveList := nil (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Table.app ((* GEN BEGIN FUNCTION EXPRESSION *) fn (b,_) => addIfBelowEq a's' b (* GEN END FUNCTION EXPRESSION *)) soGraph (* GEN END TAG OUTSIDE LET *);
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = List.app ((* GEN BEGIN FUNCTION EXPRESSION *) fn b => fSet(b, false) (* GEN END FUNCTION EXPRESSION *)) (!aboveList) (* GEN END TAG OUTSIDE LET *)
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
    (* GEN BEGIN TAG OUTSIDE LET *) val defGraph : (IntSet.intset) Table.table = Table.new (32) (* GEN END TAG OUTSIDE LET *)

    (* occursInDef a = true
       iff there is a b such that a #> b
    *)
    fun occursInDef a =
        (case Table.lookup defGraph a
           of NONE => false
            | SOME _ => true)

    (* insertNewDef (b, a) = ()
       Effect: update definition graph.

       Call this upon seeing a type-level definition
           b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S : K
       to record a #> b.
    *)
    fun insertNewDef (b, a) =
        (case Table.lookup defGraph a
           of NONE => Table.insert defGraph (a, IntSet.insert (b, IntSet.empty))
            | SOME(bs) => Table.insert defGraph (a, IntSet.insert (b, bs)))

    (* installDef (c) = ()
       Effect: if c is a type-level definition,
               update definition graph.
    *)
    fun (* GEN BEGIN FUN FIRST *) installConDec (b, I.ConDef (_, _, _, A, K, I.Kind, _)) =
          (* I.targetFam must be defined, but expands definitions! *)
          insertNewDef (b, I.targetFam A) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) installConDec _ = () (* GEN END FUN BRANCH *)

    fun installDef c = installConDec (c, I.sgnLookup c)

    (* checkNoDef a = ()
       Effect: raises Error(msg) if there exists a b such that b <# a
               or b <# a' for some a' < a.
    *)
    fun checkNoDef a =
        if occursInDef a
          then raise Error ("Definition violation: family "
                            ^ Names.qidToString (Names.constQid a)
                            ^ "\noccurs as right-hand side of type-level definition")
        else appReachable ((* GEN BEGIN FUNCTION EXPRESSION *) fn a' =>
             if occursInDef a'
               then raise Error ("Definition violation: family "
                                 ^ Names.qidToString (Names.constQid a)
                                 ^ " |> "
                                 ^ Names.qidToString (Names.constQid a')
                                 ^ ",\nwhich occurs as right-hand side of a type-level definition")
             else () (* GEN END FUNCTION EXPRESSION *))
             a

    (* reset () = ()

       Effect: Empties soGraph, fTable, defGraph
    *)
    fun reset () = (Table.clear soGraph;
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
    and (* GEN BEGIN FUN FIRST *) installTypeN' (I.Pi ((D as I.Dec (_, V1), _), V2), a) =
          (addSubord (I.targetFam V1, a);
           installTypeN (V1);
           installTypeN' (V2, a)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) installTypeN' (V as I.Root (I.Def _, _), a) =
        (* this looks like blatant overkill ... *)
        (* Sun Nov 10 11:15:47 2002 -fp *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = Whnf.normalize (Whnf.expandDef (V, I.id)) (* GEN END TAG OUTSIDE LET *)
        in
          installTypeN' (V', a)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) installTypeN' (I.Root _, _) = () (* GEN END FUN BRANCH *)
    and installTypeN (V) = installTypeN' (V, I.targetFam V)

    (* installKindN (V, a) = ()
       V nf, a : {x1:A1}...{xn:An} type, V = {xi:Ai}...{xn:An}type
       Effect: add subordination info from V into table
    *)
    (* there are no kind-level definitions *)
    fun (* GEN BEGIN FUN FIRST *) installKindN (I.Uni(L), a) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) installKindN (I.Pi ((I.Dec (_, V1), P), V2), a) =
          (addSubord (I.targetFam V1, a);
           installTypeN (V1);
           installKindN (V2, a)) (* GEN END FUN BRANCH *)

    (* install c = ()

       Effect: if c : V, add subordination from V into table
    *)
    fun install c =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V = I.constType c (* GEN END TAG OUTSIDE LET *)
        in
          case I.targetFamOpt V
            of NONE => (insertNewFam (c);
                        installKindN (V, c))
             | SOME a => (case IntSyn.sgnLookup c
                            of IntSyn.ConDec _ => checkFreeze (c, a)
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
    fun installDec (I.Dec(_,V)) = installTypeN V

    fun (* GEN BEGIN FUN FIRST *) installSome (I.Null) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) installSome (I.Decl(G, D)) =
        ( installSome G; installDec D ) (* GEN END FUN BRANCH *)

    (* b must be block *)
    fun installBlock b =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val I.BlockDec(_, _, G, Ds) = I.sgnLookup b (* GEN END TAG OUTSIDE LET *)
        in
          installSome G;
          List.app ((* GEN BEGIN FUNCTION EXPRESSION *) fn D => installDec D (* GEN END FUNCTION EXPRESSION *)) Ds
        end

    (* Respecting subordination *)

    (* checkBelow (a, b) = () iff a <| b
       Effect: raise Error(msg) otherwise
    *)
    fun checkBelow (a, b) =
        if not (below (a, b))
          then raise Error ("Subordination violation: "
                            ^ Names.qidToString (Names.constQid (a)) ^ " not <| " ^ Names.qidToString (Names.constQid (b)))
        else ()

    (* respectsTypeN' (V, a) = () iff V respects current subordination
       respectsTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: raise Error (msg)
    *)
    fun (* GEN BEGIN FUN FIRST *) respectsTypeN' (I.Pi ((D as I.Dec (_, V1), _), V2), a) =
          (checkBelow (I.targetFam V1, a);
           respectsTypeN (V1);
           respectsTypeN' (V2, a)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) respectsTypeN' (V as I.Root (I.Def _, _), a) =
        (* this looks like blatant overkill ... *)
        (* Sun Nov 10 11:15:47 2002 -fp *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = Whnf.normalize (Whnf.expandDef (V, I.id)) (* GEN END TAG OUTSIDE LET *)
        in
          respectsTypeN' (V', a)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) respectsTypeN' (I.Root _, _) = () (* GEN END FUN BRANCH *)
    and respectsTypeN (V) = respectsTypeN' (V, I.targetFam V)

    fun respects (G, (V, s)) = respectsTypeN (Whnf.normalize (V, s))
    fun respectsN (G, V) = respectsTypeN (V)

    (* Printing *)

    (* Right now, AL is in always reverse order *)
    (* Reverse again --- do not sort *)
    (* Right now, Table.app will pick int order -- do not sort *)
    fun famsToString (bs, msg) =
        IntSet.foldl ((* GEN BEGIN FUNCTION EXPRESSION *) fn (a, msg) => Names.qidToString (Names.constQid a) ^ " " ^ msg (* GEN END FUNCTION EXPRESSION *)) "\n" bs
    (*
    fun famsToString (nil, msg) = msg
      | famsToString (a::AL, msg) = famsToString (AL, Names.qidToString (Names.constQid a) ^ " " ^ msg)
    *)

    fun showFam (a, bs) =
        (print (Names.qidToString (Names.constQid a)
                ^ (if fGet a then " #> " else " |> ")
                ^ famsToString (bs, "\n")))

    fun show () = Table.app showFam soGraph;


    (* weaken (G, a) = (w') *)
    fun (* GEN BEGIN FUN FIRST *) weaken (I.Null, a) = I.id (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) weaken (I.Decl (G', D as I.Dec (name, V)), a) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val w' = weaken (G', a) (* GEN END TAG OUTSIDE LET *)
        in
          if belowEq (I.targetFam V, a) then I.dot1 w'
          else I.comp (w', I.shift)
        end (* GEN END FUN BRANCH *)


    (* showDef () = ()
       Effect: print some statistics about constant definitions
    *)
    local
      (* GEN BEGIN TAG OUTSIDE LET *) val declared = ref 0 (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val defined = ref 0 (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val abbrev = ref 0 (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val other = ref 0 (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val heightArray = Array.array (32, 0) (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val maxHeight = ref 0 (* GEN END TAG OUTSIDE LET *)

      fun inc (r) = (r := !r+1)
      fun incArray (h) = (Array.update (heightArray, h, Array.sub (heightArray, h)+1))
      (* ignore blocks and skolem constants *)
      fun max (h) = (maxHeight := Int.max (h, !maxHeight))
      fun reset () = (declared := 0; defined := 0; abbrev := 0; other := 0;
                      Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn i => 0 (* GEN END FUNCTION EXPRESSION *)) heightArray;
                      maxHeight := 0)
    in
      fun (* GEN BEGIN FUN FIRST *) analyzeAnc (I.Anc (NONE, _, _)) = ( incArray 0 ) (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) analyzeAnc (I.Anc (_, h, _)) = ( incArray h ; max h ) (* GEN END FUN BRANCH *)
      fun (* GEN BEGIN FUN FIRST *) analyze (I.ConDec (_, _, _, _, _, L)) =
          ( inc declared ) (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) analyze (I.ConDef (_, _, _, _, _, L, ancestors)) =
          ( inc defined ; analyzeAnc ancestors ) (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) analyze (I.AbbrevDef (_, _, _, _, _, L)) =
          ( inc abbrev ) (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) analyze _ = ( inc other ) (* GEN END FUN BRANCH *)
      fun showDef () =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = reset () (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = I.sgnApp ((* GEN BEGIN FUNCTION EXPRESSION *) fn c => analyze (I.sgnLookup c) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = print ("Declared: " ^ Int.toString (!declared) ^ "\n") (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = print ("Defined : " ^ Int.toString (!defined) ^ "\n") (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = print ("Abbrevs : " ^ Int.toString (!abbrev) ^ "\n") (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = print ("Other   : " ^ Int.toString (!other) ^ "\n") (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = print ("Max definition height: " ^ Int.toString (!maxHeight) ^ "\n") (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = ArraySlice.appi
                      ((* GEN BEGIN FUNCTION EXPRESSION *) fn (h, i) => print (" Height " ^ Int.toString h ^ ": "
                                           ^ Int.toString i ^ " definitions\n") (* GEN END FUNCTION EXPRESSION *))
                      (ArraySlice.slice (heightArray, 0, SOME(!maxHeight+1))) (* GEN END TAG OUTSIDE LET *)
          in
            ()
          end
    end
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val install = install (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val installDef = installDef (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val installBlock = installBlock (* GEN END TAG OUTSIDE LET *)

    (* val installFrozen = installFrozen *)

    (* GEN BEGIN TAG OUTSIDE LET *) val freeze = freeze (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val frozen = frozen (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val thaw = thaw (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val addSubord = addSubord (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val below = below (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val belowEq = belowEq (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val equiv = equiv (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val checkNoDef = checkNoDef (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val respects = respects (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val respectsN = respectsN (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val weaken = weaken (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val show = show (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val showDef = showDef (* GEN END TAG OUTSIDE LET *)

  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor Subordinate *)
