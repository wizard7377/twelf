MTPStrategy  MTPGlobal MTPGLOBAL    StateSyn' STATESYN    MTPFilling MTPFILLING    MTPFilling StateSyn  StateSyn'   MTPData MTPDATA    MTPSplitting MTPSPLITTING    MTPSplitting StateSyn  StateSyn'   MTPRecursion MTPRECURSION    MTPRecursion StateSyn  StateSyn'   Inference INFERENCE    Inference StateSyn  StateSyn'   MTPrint MTPRINT    MTPrint StateSyn  StateSyn'   Timers TIMERS     MTPSTRATEGY  struct module module let rec printInit() if ! chatter > 3 then print "Strategy\n" else ()let rec printFilling() if ! chatter > 5 then print ("[Filling ... ") else if ! chatter > 4 then print ("F") else ()let rec printRecursion() if ! chatter > 5 then print ("[Recursion ...") else if ! chatter > 4 then print ("R") else ()let rec printInference() if ! chatter > 5 then print ("[Inference ...") else if ! chatter > 4 then print ("I") else ()let rec printSplittingsplitOp if ! chatter > 5 then print ("[Splitting ...") else if ! chatter > 4 then print ("S") else ()let rec printCloseBracket() if ! chatter > 5 then print ("]\n") else ()let rec printQed() (if ! chatter > 3 then print ("[QED]\n") else (); if ! chatter > 4 then print ("Statistics: required Twelf.Prover.maxFill := " ^ (toString (! maxFill)) ^ "\n") else ())(* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
let rec findMinnil nONE findMinl let let rec findMin'(nil,  , result) result findMin'(o' :: l',  , nONE) if applicable o' then findMin' (l',  , sOME o') else findMin' (l',  , nONE) findMin'(o' :: l',  , sOME o) if applicable o' then match compare (o',  , o) with lESS -> findMin' (l',  , sOME o') _ -> findMin' (l',  , sOME o) else findMin' (l',  , sOME o) in findMin' (l,  , nONE)(* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
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
let rec split(s :: givenStates,  , os as (openStates,  , solvedStates)) match findMin ((time splitting expand) s) with nONE -> fill (givenStates,  , (s :: openStates,  , solvedStates)) sOME splitOp -> let let  inlet  inlet  inlet  inlet  inlet  inlet  in in fill (sL'' @ givenStates,  , os) fill(nil,  , os) os fill(s :: givenStates,  , os as (openStates,  , solvedStates)) (match (time recursion expand) s with fillingOp -> try  with )(* Note: calling splitting in case filling fails, may cause the prover to succeed
              if there are no cases to split -- however this may in fact be wrong -bp*)
(* for comparing depth-first search (logic programming) with iterative deepening search
              in the meta-theorem prover, we must disallow splitting :

                handle TimeLimit.TimeOut =>  raise Filling.Error "Time Out: Time limit exceeded\n"
                handle MTPFilling.Error msg =>  raise Filling.Error msg
                  ) handle MTPFilling.Error msg =>  raise Filling.Error msg
            *)
(* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
let rec rungivenStates (let let  inlet  inlet  inlet  inlet  in in (openStates',  , solvedStates'))let  in(* local *)
end