Prover  MetaGlobal METAGLOBAL    MetaSyn' METASYN    Init INIT    Init MetaSyn  MetaSyn'   Strategy STRATEGY    Strategy MetaSyn  MetaSyn'   Filling FILLING    Filling MetaSyn  MetaSyn'   Splitting SPLITTING    Splitting MetaSyn  MetaSyn'   Recursion RECURSION    Recursion MetaSyn  MetaSyn'   Qed QED    Qed MetaSyn  MetaSyn'   MetaPrint METAPRINT    MetaPrint MetaSyn  MetaSyn'   Names NAMES    Timers TIMERS     PROVER  struct (*! structure IntSyn = MetaSyn'.IntSyn !*)
exception module module module (* List of open states *)
let  in(* List of solved states *)
let  inlet rec errors raise (error s)(* reset () = ()

       Invariant:
       Resets the internal state of open states/solved states
    *)
let rec reset() (openStates := nil; solvedStates := nil)(* contains (L1, L2) = B'

       Invariant:
       B' holds iff L1 subset of L2 (modulo permutation)
    *)
let rec contains(nil,  , _) true contains(x :: l,  , l') (exists (fun x' -> x = x') l') && contains (l,  , l')(* equiv (L1, L2) = B'

       Invariant:
       B' holds iff L1 is equivalent to L2 (modulo permutation)
    *)
let rec equiv(l1,  , l2) contains (l1,  , l2) && contains (l2,  , l1)(* insertState S = ()

       Invariant:
       If S is successful prove state, S is stored in solvedStates
       else S is stored in openStates
    *)
let rec insertStates if subgoal s then solvedStates := s :: (! solvedStates) else openStates := s :: (! openStates)(* cLtoString L = s

       Invariant:
       If   L is a list of cid,
       then s is a string, listing their names
    *)
let rec cLToString(nil) "" cLToString(c :: nil) (conDecName (sgnLookup c)) cLToString(c :: l) (conDecName (sgnLookup c)) ^ ", " ^ (cLToString l)(* init (k, cL) = ()

       Invariant:
       If   k is the maximal search depth
       and  cL is a complete and consistent list of cids
       then init initializes the openStates/solvedStates
       else an Error exception is raised
    *)
let rec init(k,  , cL as (c :: _)) let let  inlet  inlet  in(* if no termination ordering given! *)
 in if equiv (cL,  , cL') then app (fun s -> insertState s) (init cL) else raise (error ("Theorem by simultaneous induction not correctly stated:" ^ "\n            expected: " ^ (cLToString cL')))(* auto () = ()

       Invariant:
       Solves as many States in openStates
       as possible.
    *)
let rec auto() let let  inlet  inlet  inlet  in in if (length (! openStates)) > 0 then raise (error ("A proof could not be found")) else ()(* makeConDec (name, (G, M), V) = e'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : type
       then e' = (name, |G|, {G}.V, Type) is a signature conDec
    *)
let rec makeConDec(state (name,  , prefix (g,  , m,  , b),  , v)) let let rec makeConDec'(null,  , v,  , k) conDec (name,  , nONE,  , k,  , normal,  , v,  , type) makeConDec'(decl (g,  , d),  , v,  , k) makeConDec' (g,  , pi ((d,  , maybe),  , v),  , k + 1) in (makeConDec' (g,  , v,  , 0))(* makeSignature (SL) = IS'

       Invariant:
       If   SL is a list of states,
       then IS' is the corresponding interface signaure
    *)
let rec makeSignature(nil) sgnEmpty makeSignature(s :: sL) conDec (makeConDec s,  , makeSignature sL)(* install () = ()

       Invariant:
       Installs solved states into the global signature.
    *)
let rec install(installConDec) let let rec install'sgnEmpty () install'(conDec (e,  , s)) (installConDec e; install' s)let  in in (install' iS; if ! chatter > 2 then (print "% ------------------\n"; print (sgnToString (iS)); print "% ------------------\n") else ())(* print () = ()

       Invariant:
       Prints the list of open States and the list of closed states.
    *)
let rec printState() let let rec print'nil () print'(s :: l) (print (stateToString s); print' l) in (print "Open problems:\n"; print "==============\n\n"; print' (! openStates); print "Solved problems:\n"; print "================\n\n"; print' (! solvedStates))let  inlet  inlet  inlet  in(* local *)
end