StrategyFRS  MetaGlobal METAGLOBAL    MetaSyn' METASYN    Filling FILLING    Filling MetaSyn  MetaSyn'   Splitting SPLITTING    Splitting MetaSyn  MetaSyn'   Recursion RECURSION    Recursion MetaSyn  MetaSyn'   Lemma LEMMA    Lemma MetaSyn  MetaSyn'   Qed QED    Qed MetaSyn  MetaSyn'   MetaPrint METAPRINT    MetaPrint MetaSyn  MetaSyn'   Timers TIMERS     STRATEGY  struct module module let rec printInit() if ! chatter > 3 then print "Strategy 1.0: FRS\n" else ()let rec printFinish(state (name,  , _,  , _)) if ! chatter > 5 then print ("[Finished: " ^ name ^ "]\n") else if ! chatter > 4 then print ("[" ^ name ^ "]\n") else if ! chatter > 3 then print ("[" ^ name ^ "]") else ()let rec printFilling() if ! chatter > 5 then print ("[Filling ... ") else if ! chatter > 4 then print ("F") else ()let rec printRecursion() if ! chatter > 5 then print ("[Recursion ...") else if ! chatter > 4 then print ("R") else ()let rec printSplitting() if ! chatter > 5 then print ("[Splitting ...") else if ! chatter > 4 then print ("S") else ()let rec printCloseBracket() if ! chatter > 5 then print ("]\n") else ()let rec printQed() if ! chatter > 3 then print ("[QED]\n") else ()(* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
let rec findMinnil nONE findMin(o :: l) let let rec findMin'(nil,  , k,  , result) result findMin'(o' :: l',  , k,  , result) let let  in in if index o' < k then findMin' (l',  , k',  , sOME o') else findMin' (l',  , k,  , result) in findMin' (l,  , index o,  , sOME o)(* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
         contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and
         contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
    *)
let rec split(s :: givenStates,  , os as (openStates,  , solvedStates)) match findMin ((time splitting expand) s) with nONE -> fill (givenStates,  , (s :: openStates,  , solvedStates)) sOME splitOp -> let let  inlet  inlet  in in (try  with ) recurse(s :: givenStates,  , os as (openStates,  , solvedStates)) match (time recursion expandEager) s with nil -> split (s :: givenStates,  , os) (recursionOp :: _) -> let let  inlet  inlet  in in (try  with ) fill(nil,  , os) os fill(s :: givenStates,  , os as (openStates,  , solvedStates)) let let rec fillOp() match (time filling expand) s with (_,  , fillingOp) -> (try  with ) in try  with (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
let rec rungivenStates let let  inlet  inlet  in in oslet  in(* local *)
end    StrategyRFS  MetaGlobal METAGLOBAL    MetaSyn' METASYN    Filling FILLING    Filling MetaSyn  MetaSyn'   Splitting SPLITTING    Splitting MetaSyn  MetaSyn'   Recursion RECURSION    Recursion MetaSyn  MetaSyn'   Lemma LEMMA    Lemma MetaSyn  MetaSyn'   Qed QED    Qed MetaSyn  MetaSyn'   MetaPrint METAPRINT    MetaPrint MetaSyn  MetaSyn'   Timers TIMERS     STRATEGY  struct module module let rec printInit() if ! chatter > 3 then print "Strategy 1.0: RFS\n" else ()let rec printFinish(state (name,  , _,  , _)) if ! chatter > 5 then print ("[Finished: " ^ name ^ "]\n") else if ! chatter > 4 then print ("[" ^ name ^ "]\n") else if ! chatter > 3 then print ("[" ^ name ^ "]") else ()let rec printFilling() if ! chatter > 5 then print ("[Filling ... ") else if ! chatter > 4 then print ("F") else ()let rec printRecursion() if ! chatter > 5 then print ("[Recursion ...") else if ! chatter > 4 then print ("R") else ()let rec printSplitting() if ! chatter > 5 then print ("[Splitting ...") else if ! chatter > 4 then print ("S") else ()let rec printCloseBracket() if ! chatter > 5 then print ("]\n") else ()let rec printQed() if ! chatter > 3 then print ("[QED]\n") else ()(* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
let rec findMinnil nONE findMin(o :: l) let let rec findMin'(nil,  , k,  , result) result findMin'(o' :: l',  , k,  , result) let let  in in if index o' < k then findMin' (l',  , k',  , sOME o') else findMin' (l',  , k,  , result) in findMin' (l,  , index o,  , sOME o)(* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
         contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and
         contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
    *)
let rec split(s :: givenStates,  , os as (openStates,  , solvedStates)) match findMin ((time splitting expand) s) with nONE -> recurse (givenStates,  , (s :: openStates,  , solvedStates)) sOME splitOp -> let let  inlet  inlet  in in (try  with ) fill(nil,  , os) os fill(s :: givenStates,  , os as (openStates,  , solvedStates)) match (time filling expand) s with (_,  , fillingOp) -> (try  with ) recurse(nil,  , os) os recurse(s :: givenStates,  , os as (openStates,  , solvedStates)) match (time recursion expandEager) s with nil -> fill (s :: givenStates,  , os) (recursionOp :: _) -> let let  inlet  inlet  in in (try  with )(* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
let rec rungivenStates let let  inlet  inlet  in in oslet  in(* local *)
end    Strategy  MetaGlobal METAGLOBAL    MetaSyn' METASYN    StrategyFRS STRATEGY    StrategyFRS MetaSyn  MetaSyn'   StrategyRFS STRATEGY    StrategyRFS MetaSyn  MetaSyn'    STRATEGY  struct module let rec runsL match ! strategy with rFS -> run sL fRS -> run sLend