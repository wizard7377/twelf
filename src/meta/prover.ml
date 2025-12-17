MTProver  MTPGlobal MTPGLOBAL    StateSyn STATESYN    Order ORDER    MTPInit MTPINIT    MTPInit StateSyn  StateSyn   MTPStrategy MTPSTRATEGY    MTPStrategy StateSyn  StateSyn   RelFun RELFUN     PROVER  struct (*! structure IntSyn = IntSyn' !*)
exception module module module (* DISCLAIMER: This functor is temporary. Its purpose is to
       connect the new prover to Twelf  (see also functor below) *)
(* List of open states *)
let  in(* List of solved states *)
let  inlet rec transformOrder'(g,  , arg k) let let  inlet  in in arg ((root (bVar k',  , nil),  , id),  , (v,  , id)) transformOrder'(g,  , lex os) lex (map (fun o -> transformOrder' (g,  , o)) os) transformOrder'(g,  , simul os) simul (map (fun o -> transformOrder' (g,  , o)) os)let rec transformOrder(g,  , all (prim d,  , f),  , os) all (d,  , transformOrder (decl (g,  , d),  , f,  , os)) transformOrder(g,  , and (f1,  , f2),  , o :: os) and (transformOrder (g,  , f1,  , [o]),  , transformOrder (g,  , f2,  , os)) transformOrder(g,  , ex _,  , [o]) transformOrder' (g,  , o) transformOrder(g,  , true,  , [o]) transformOrder' (g,  , o)(* last case: no existentials---order must be trivial *)
let rec selectc (try  with )let rec errors raise (error s)(* reset () = ()

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
let rec insertStates openStates := s :: (! openStates)(* cLtoString L = s

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
let  inlet  in in if equiv (cL,  , cL') then app (fun s -> insertState s) (init (f,  , o)) else raise (error ("Theorem by simultaneous induction not correctly stated:" ^ "\n            expected: " ^ (cLToString cL')))(* auto () = ()

       Invariant:
       Solves as many States in openStates
       as possible.
    *)
let rec auto() let let  inlet  inlet  in in if (length (! openStates)) > 0 then raise (error ("A proof could not be found")) else ()let rec print() ()let rec install_ ()let  inlet  inlet  inlet  in(* local *)
end   CombiProver  MTPGlobal MTPGLOBAL    ProverOld PROVER    ProverNew PROVER     PROVER  struct (*! structure IntSyn = IntSyn' !*)
exception let rec hef try  with let rec initargs he (fun () -> match ! (prover) with new -> init args old -> init args)let rec autoargs he (fun () -> match ! (prover) with new -> auto args old -> auto args)let rec printargs he (fun () -> match ! (prover) with new -> print args old -> print args)let rec installargs he (fun () -> match ! (prover) with new -> install args old -> install args)let  inlet  inlet  inlet  in(* local *)
end