open Basis ;; 

module Rep = struct
  module I = IntSyn
  module S = Syntax

  let rec defSize x =
    match x with
    | Sgn.DEF_TERM y -> S.size_term y
    | Sgn.DEF_TYPE y -> S.size_tp y

  let rec cidSize cid =
    match I.sgnLookup cid with
    | I.ConDec (_, _, _, _, _, I.Type) ->
        S.size_tp (S.typeOf (Sgn.classifier cid))
    | I.ConDec (_, _, _, _, _, I.Kind) ->
        S.size_knd (S.kindOf (Sgn.classifier cid))
    | I.ConDef (_, _, _, _, _, _, _) -> defSize (Sgn.def cid)
    | I.AbbrevDef (_, _, _, _, _, _) -> defSize (Sgn.def cid)
    | _ -> 0

  let rec o_cidSize cid =
    match I.sgnLookup cid with
    | I.ConDec (_, _, _, _, _, I.Type) ->
        S.size_tp (S.typeOf (Sgn.o_classifier cid))
    | I.ConDec (_, _, _, _, _, I.Kind) ->
        S.size_knd (S.kindOf (Sgn.o_classifier cid))
    | I.ConDef (_, _, _, _, _, _, _) -> defSize (Sgn.o_def cid)
    | I.AbbrevDef (_, _, _, _, _, _) -> defSize (Sgn.o_def cid)
    | _ -> 0

  open SMLofNJCont
  (* val l : (Syntax.term * Syntax.tp) list ref = ref [] *)

  let k : Reductio.eq_c option ref = ref None

  exception Crap

  let rec sanityCheck cid =
    try
      match I.sgnLookup cid with
      | I.ConDec (_, _, _, _, _, I.Type) ->
          Reductio.check_plusconst_type (Sgn.typeOf (Sgn.classifier cid))
      | I.ConDec (_, _, _, _, _, I.Kind) ->
          Reductio.check_kind ([], Sgn.kindOf (Sgn.classifier cid))
      | I.ConDef (_, _, _, _, _, I.Type, _) ->
          let (Sgn.DEF_TERM y) = Sgn.def cid in
          let (Syntax.TClass z) = Sgn.classifier cid in
          (*				     l := (y,z):: !l; *)
          Reductio.check ([], y, z)
      | I.ConDef (_, _, _, _, _, I.Kind, _) ->
          let (Sgn.DEF_TYPE y) = Sgn.def cid in
          let (Syntax.KClass z) = Sgn.classifier cid in
          Reductio.check_type Reductio.CON_LF (Syntax.explodeKind z, y)
      | I.AbbrevDef (_, _, _, _, _, I.Type) ->
          let (Sgn.DEF_TERM y) = Sgn.def cid in
          let (Syntax.TClass z) = Sgn.classifier cid in
          (*				     l := (y,z):: !l; *)
          Reductio.check ([], y, z)
      | I.AbbrevDef (_, _, _, _, _, I.Kind) ->
          let (Sgn.DEF_TYPE y) = Sgn.def cid in
          let (Syntax.KClass z) = Sgn.classifier cid in
          Reductio.check_type Reductio.CON_LF (Syntax.explodeKind z, y)
      | _ -> true
      (* we're not checking block declarations or anything else like that *)
    with Syntax.Syntax _ ->
      print ("--> " ^ Int.toString cid);
      raise Match

  let rec gen_graph n autoCompress =
    let _ = autoCompress n in
    let rec sanity n =
      if n < 0 then true
      else
        sanity (n - 1)
        &&
        if sanityCheck n then true
        else (
          print ("insane: <" ^ Int.toString n ^ ">\n");
          raise Crap)
    in
    let _ = sanity n in
    let pairs = List.tabulate (n + 1, fun x -> (o_cidSize x, cidSize x)) in
    let s =
      foldl
      ^ ""
          (map
             (fun x y -> Int.toString x ^ " " ^ Int.toString y ^ "\n")
             pairs)
    in
    let f = TextIO.openOut "/tmp/graph" in
    let _ = TextIO.output (f, s) in
    let _ = TextIO.closeOut f in
    ()
  (* DEBUG  handle Reductio.Matching2 s => (print "doesn'tmatch"; k := SOME s); *)

  (* fun gg n = (Compress.sgnReset(); gen_graph n
	    (fn n => Compress.sgnAutoCompressUpTo n Compress.naiveModes)) *)

  (* Syntax.size_term (Option.valOf(#o_def (Compress.sgnLookup n))) *)

  open Reductio
end

(*
fun autoCompress n modeFinder =
    let
(*	val rep = Twelf.Names.lookup "represents"
	val rep_z = Twelf.Names.lookup "represents_z"
	val rep_s = Twelf.Names.lookup "represents_s" *)
    in
	Compress.sgnReset();
	Compress.sgnAutoCompressUpTo(n)
    (* Syntax.size_term (Option.valOf(#o_def (Compress.sgnLookup n))) *)
    end
*)
