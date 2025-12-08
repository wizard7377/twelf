module type SGN =
sig
    type sigent
    type def = DEF_NONE
		 | DEF_TERM of Syntax.term
		 | DEF_TYPE of Syntax.tp

    val condec : string * Syntax.tp * Syntax.tp -> sigent
    val tycondec : string * Syntax.knd * Syntax.knd -> sigent
    val defn : string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term -> sigent
    val tydefn : string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp -> sigent
    val abbrev : string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term -> sigent
    val tyabbrev : string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp -> sigent
    val typeOfSigent : sigent -> Syntax.tp
    val classifier : int -> Syntax.class_
    val o_classifier : int -> Syntax.class_
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
end

module Sgn =
struct
    open Syntax
    exception NoSuch of int

    type def = DEF_NONE
		 | DEF_TERM of term
		 | DEF_TYPE of tp

    (* o_ means "original", i.e. before compression *)
    type sigent = {name : string; 
		   classifier : class_;
		   o_classifier : class_;
		   def : def;
		   o_def : def;
		   abbreviation : bool}

    let sgn_size = 14000 (* XXX *)
    let sigma : sigent option Array.array = Array.array(sgn_size, NONE)
    let all_modes : mode list option Array.array = Array.array(sgn_size, NONE)
    let all_ps : bool option Array.array = Array.array(sgn_size, NONE)

    let rec split (h::tl) 0 = ([], h, tl)
       | split (h::tl) n = let 
	     (pre, thing, post) = split tl (n-1)
	 in
	     (h::pre, thing, post)
	 end
       | split [] n = split [NONE] n 

    let clear () = begin
		       Array.modify (fun _ -> NONE) sigma;
		       Array.modify (fun _ -> NONE) all_modes;
		       Array.modify (fun _ -> NONE) all_ps
		   end
		       
    let condec (s, a, oa) = {name = s; classifier = Tclass a; o_classifier = Tclass oa;
			     def = DEF_NONE; o_def = DEF_NONE; abbreviation = false}
    let tycondec (s, k, ok) = {name = s; classifier = Kclass k; o_classifier = Kclass ok;
			       def = DEF_NONE; o_def = DEF_NONE; abbreviation = false}
    let defn (s, a, oa, m, om) = {name = s; classifier = Tclass a; o_classifier = Tclass oa;
				  def = DEF_TERM m; o_def = DEF_TERM om; abbreviation = false}
    let tydefn (s, k, ok, a, oa) = {name = s; classifier = Kclass k; o_classifier = Kclass ok;
				    def = DEF_TYPE a; o_def = DEF_TYPE oa; abbreviation = false}
    let abbrev (s, a, oa, m, om) = {name = s; classifier = Tclass a; o_classifier = Tclass oa;
				    def = DEF_TERM m; o_def = DEF_TERM om; abbreviation = true}
    let tyabbrev (s, k, ok, a, oa) = {name = s; classifier = Kclass k; o_classifier = Kclass ok;
				    def = DEF_TYPE a; o_def = DEF_TYPE oa; abbreviation = true}
    let typeOfSigent (e : sigent) = Syntax.typeOf (#classifier e)

    let setter table (n, x) = Array.update (table, n, SOME x)
    let getter table id = Array.sub (table, id)

    let set_modes = setter all_modes
    let get_modes = getter all_modes
    let set_p = setter all_ps
    let get_p = getter all_ps
    let update = setter sigma
    let sub = getter sigma

    let classifier id = (#classifier (Option.valOf(sub id)) handle Option -> raise NoSuch id)
    let o_classifier id = (#o_classifier (Option.valOf(sub id)) handle Option -> raise NoSuch id)
    let def id = (#def (Option.valOf(sub id)) handle Option -> raise NoSuch id)
    let o_def id = (#o_def (Option.valOf(sub id)) handle Option -> raise NoSuch id)
    let abbreviation id = (#abbreviation (Option.valOf(sub id)) handle Option -> raise NoSuch id)
end