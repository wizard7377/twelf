IndexSkolem  Global GLOBAL    Queue QUEUE     INDEX  struct (*! structure IntSyn = IntSyn' !*)
module let rec cidFromHead(const c) c cidFromHead(def c) c(* Index array

       Invariant:
       For all type families  a
       indexArray (a) = c1,...,cn
       where c1,...,cn is a queue consisting of all constants with
       target family a
    *)
let  in(* reset () = ()
       Empties index array
    *)
let rec reset() modify (fun _ -> empty) indexArray(* update (a, c) = ()
       inserts c into the index queue for family a
       Invariant: a = target family of c
    *)
let rec update(a,  , c) update (indexArray,  , a,  , insert (c,  , sub (indexArray,  , a)))(* install (c) = ()
       installs c into the correct index queue
       presently ignores definitions
    *)
let rec installfromCS(h as const c) (match (fromCS,  , sgnLookup (c)) with (_,  , conDec (_,  , _,  , _,  , _,  , a,  , type)) -> update (cidFromHead (targetHead a),  , h) (clause,  , conDef (_,  , _,  , _,  , _,  , a,  , type,  , _)) -> update (cidFromHead (targetHead a),  , def (c)) _ -> ()) installfromCS(h as skonst c) (match sgnLookup (c) with skoDec (_,  , _,  , _,  , a,  , type) -> update (cidFromHead (targetHead a),  , h) _ -> ())let rec remove(a,  , cid) (match deleteEnd (sub (indexArray,  , a)) with nONE -> () sOME (const cid',  , queue') -> if cid = cid' then update (indexArray,  , a,  , queue') else () sOME (skonst cid',  , queue') -> if cid = cid' then update (indexArray,  , a,  , queue') else ())let rec uninstallcid (match sgnLookup cid with conDec (_,  , _,  , _,  , _,  , a,  , type) -> remove (cidFromHead (targetHead a),  , cid) skoDec (_,  , _,  , _,  , a,  , type) -> remove (cidFromHead (targetHead a),  , cid) _ -> ())let rec resetFrommark let let  inlet rec iteri if i < mark then () else (uninstall i; update (indexArray,  , i,  , empty)) in iter (limit - 1)(* lookup a = [c1,...,cn] *)
(*
       c1,...,cn are all constants with target family a
       in order of declaration, defined constants are omitted.

       A second lookup after the first without intermediate inserts will
       be in constant time.
    *)
let rec lookupa let let rec lk(l,  , nONE) l lk(l,  , sOME (q')) (update (indexArray,  , a,  , q'); l) in lk (toList (sub (indexArray,  , a)))let  inlet  inlet  inlet  in(* local *)
end