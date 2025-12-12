(* GEN BEGIN SIGNATURE DECLARATION *) signature SGN =
sig
    type sigent
    datatype def = DEF_NONE
		 | DEF_TERM of Syntax.term
		 | DEF_TYPE of Syntax.tp

    val condec : string * Syntax.tp * Syntax.tp -> sigent
    val tycondec : string * Syntax.knd * Syntax.knd -> sigent
    val defn : string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term -> sigent
    val tydefn : string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp -> sigent
    val abbrev : string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term -> sigent
    val tyabbrev : string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp -> sigent
    val typeOfSigent : sigent -> Syntax.tp
    val classifier : int -> Syntax.class
    val o_classifier : int -> Syntax.class
    val def : int -> def
    val o_def : int -> def
    val update : int * sigent -> unit
    val sub : int -> sigent option
    val clear : unit -> unit
    val get_modes : int -> Syntax.mode list option
    val set_modes : int * Syntax.mode list -> unit
    val get_p : int -> bool option
    val set_p : int * bool -> unit
    val abbreviation : int -> bool
end (* GEN END SIGNATURE DECLARATION *)

structure Sgn =
struct
    open Syntax
    exception NoSuch of int

    datatype def = DEF_NONE
		 | DEF_TERM of term
		 | DEF_TYPE of tp

    (* o_ means "original", i.e. before compression *)
    type sigent = {name : string, 
		   classifier : class,
		   o_classifier : class,
		   def : def,
		   o_def : def,
		   abbreviation : bool}

    (* GEN BEGIN TAG INSIDE LET *) val sgn_size = 14000 (* GEN END TAG INSIDE LET *) (* XXX *)
    (* GEN BEGIN TAG INSIDE LET *) val sigma : sigent option Array.array = Array.array(sgn_size, NONE) (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val all_modes : mode list option Array.array = Array.array(sgn_size, NONE) (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val all_ps : bool option Array.array = Array.array(sgn_size, NONE) (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun  split (h::tl) 0 = ([], h, tl)
       | split (h::tl) n = let 
       	     val (pre, thing, post) = split tl (n-1)
       	 in
       	     (h::pre, thing, post)
       	 end
       | split [] n = split [NONE] n (* GEN END TAG INSIDE LET *) 

    (* GEN BEGIN TAG INSIDE LET *) fun clear () = let in
    		       Array.modify (fn _ => NONE) sigma;
    		       Array.modify (fn _ => NONE) all_modes;
    		       Array.modify (fn _ => NONE) all_ps
    		   end (* GEN END TAG INSIDE LET *)
		       
    (* GEN BEGIN TAG INSIDE LET *) fun condec (s, a, oa) = {name = s, classifier = tclass a, o_classifier = tclass oa,
    			     def = DEF_NONE, o_def = DEF_NONE, abbreviation = false} (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun tycondec (s, k, ok) = {name = s, classifier = kclass k, o_classifier = kclass ok,
    			       def = DEF_NONE, o_def = DEF_NONE, abbreviation = false} (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun defn (s, a, oa, m, om) = {name = s, classifier = tclass a, o_classifier = tclass oa,
    				  def = DEF_TERM m, o_def = DEF_TERM om, abbreviation = false} (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun tydefn (s, k, ok, a, oa) = {name = s, classifier = kclass k, o_classifier = kclass ok,
    				    def = DEF_TYPE a, o_def = DEF_TYPE oa, abbreviation = false} (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun abbrev (s, a, oa, m, om) = {name = s, classifier = tclass a, o_classifier = tclass oa,
    				    def = DEF_TERM m, o_def = DEF_TERM om, abbreviation = true} (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun tyabbrev (s, k, ok, a, oa) = {name = s, classifier = kclass k, o_classifier = kclass ok,
    				    def = DEF_TYPE a, o_def = DEF_TYPE oa, abbreviation = true} (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun typeOfSigent (e : sigent) = Syntax.typeOf (#classifier e) (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun setter table (n, x) = Array.update (table, n, SOME x) (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun getter table id = Array.sub (table, id) (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) val set_modes = setter all_modes (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val get_modes = getter all_modes (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val set_p = setter all_ps (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val get_p = getter all_ps (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val update = setter sigma (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) val sub = getter sigma (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun classifier id = (#classifier (Option.valOf(sub id)) handle Option => raise NoSuch id) (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun o_classifier id = (#o_classifier (Option.valOf(sub id)) handle Option => raise NoSuch id) (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun def id = (#def (Option.valOf(sub id)) handle Option => raise NoSuch id) (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun o_def id = (#o_def (Option.valOf(sub id)) handle Option => raise NoSuch id) (* GEN END TAG INSIDE LET *)
    (* GEN BEGIN TAG INSIDE LET *) fun abbreviation id = (#abbreviation (Option.valOf(sub id)) handle Option => raise NoSuch id) (* GEN END TAG INSIDE LET *)
end