
module Rep =
struct

module I = IntSyn
module S = Syntax

let rec defSize x = (match x with 
   		       Sgn.DEF_TERM y -> S.size_term y
		     | Sgn.DEF_TYPE y -> S.size_tp y)

let rec cidSize cid = (match I.sgnLookup cid with 
   I.ConDec(_,_,_,_,_,I.Type) -> S.size_tp (S.typeOf (Sgn.classifier cid))
 | I.ConDec(_,_,_,_,_,I.Kind) -> S.size_knd (S.kindOf (Sgn.classifier cid))
 | I.ConDef(_,_,_,_,_,_,_) -> defSize(Sgn.def cid)
 | I.AbbrevDef(_,_,_,_,_,_) -> defSize(Sgn.def cid)
 | _ -> 0)

let rec o_cidSize cid = (match I.sgnLookup cid with 
   I.ConDec(_,_,_,_,_,I.Type) -> S.size_tp (S.typeOf (Sgn.o_classifier cid))
 | I.ConDec(_,_,_,_,_,I.Kind) -> S.size_knd (S.kindOf (Sgn.o_classifier cid))
 | I.ConDef(_,_,_,_,_,_,_) -> defSize(Sgn.o_def cid)
 | I.AbbrevDef(_,_,_,_,_,_) -> defSize(Sgn.o_def cid)
 | _ -> 0)


open SMLofNJ.Cont

(* let l : (Syntax.term * Syntax.tp) list ref = ref [] *)
let k : Reductio.eq_c option ref = ref NONE


exception Crap
let rec sanityCheck cid = ((match I.sgnLookup cid with 
   I.ConDec(_,_,_,_,_,I.Type) -> (Reductio.check_plusconst_type (Sgn.typeOf (Sgn.classifier cid)))
 | I.ConDec(_,_,_,_,_,I.Kind) -> (Reductio.check_kind ([], Sgn.kindOf (Sgn.classifier cid)))
 | I.ConDef(_,_,_,_,_,I.Type,_) -> let Sgn.DEF_TERM y = Sgn.def cid in
				     let Syntax.Tclass z = Sgn.classifier cid 
				 in
(*				     l := (y,z):: !l; *)
				     Reductio.check ([], y, z) 
				 end
 | I.ConDef(_,_,_,_,_,I.Kind,_) -> let Sgn.DEF_TYPE y = Sgn.def cid in
				     let Syntax.Kclass z = Sgn.classifier cid 
				 in
				     Reductio.check_type  Reductio.CON_LF (Syntax.explodeKind z, y) 
				 end
 | I.AbbrevDef(_,_,_,_,_,I.Type) -> let Sgn.DEF_TERM y = Sgn.def cid in
				     let Syntax.Tclass z = Sgn.classifier cid 
				 in
(*				     l := (y,z):: !l; *)
				     Reductio.check ([], y, z) 
				 end
 | I.AbbrevDef(_,_,_,_,_,I.Kind) -> let Sgn.DEF_TYPE y = Sgn.def cid in
				     let Syntax.Kclass z = Sgn.classifier cid 
				 in
				     Reductio.check_type Reductio.CON_LF (Syntax.explodeKind z, y) 
				 end
 | _ -> true (* we're not checking block declarations or anything else like that *))
handle Syntax.Syntax _ -> (print ("--> " ^ Int.toString cid); raise Match))



let rec gen_graph n autoCompress =
    let
	let _ = autoCompress n 
	fun sanity n = if n < 0 then true else 
		       (sanity (n-1) andalso (if sanityCheck n then true else (print ("insane: <" ^ (Int.toString n) ^ ">\n"); raise Crap)) )
	let _ = sanity n 
	let pairs = List.tabulate (n+1, (fun x -> ( o_cidSize x, cidSize x) ))
	let s = foldl op^ "" 
		      (map (fn (x,y) => 
			       Int.toString x ^ " " ^ Int.toString y ^ "\n" ) pairs) 
	let f = TextIO.openOut "/tmp/graph"
	let _ = TextIO.output(f,s)
	let _ = TextIO.closeOut(f)
    in
	()
    end
(* DEBUG  handle Reductio.Matching2 s => (print "doesn'tmatch"; k := SOME s); *)

(* fun gg n = (Compress.sgnReset(); gen_graph n
	    (fun n -> Compress.sgnAutoCompressUpTo n Compress.naiveModes)) *)

(* Syntax.size_term (Option.valOf(#o_def (Compress.sgnLookup n))) *)

open Reductio
end

(*
let rec autoCompress n modeFinder =
    let
(*	let rep = Twelf.Names.lookup "represents"
	let rep_z = Twelf.Names.lookup "represents_z"
	let rep_s = Twelf.Names.lookup "represents_s" *)
    in
	Compress.sgnReset();
	Compress.sgnAutoCompressUpTo(n)
    (* Syntax.size_term (Option.valOf(#o_def (Compress.sgnLookup n))) *)
    end
*)
