module type SGN =
sig
    type sigent
    type def = DEF_NONE
		 | DEF_TERM of Syntax.term
		 | DEF_TYPE of Syntax.tp

    let condec : string * Syntax.tp * Syntax.tp -> sigent
    let tycondec : string * Syntax.knd * Syntax.knd -> sigent
    let defn : string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term -> sigent
    let tydefn : string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp -> sigent
    let abbrev : string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term -> sigent
    let tyabbrev : string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp -> sigent
    let typeOfSigent : sigent -> Syntax.tp
    let classifier : int -> Syntax.tClass
    let o_classifier : int -> Syntax.tClass
    let def : int -> def
    let o_def : int -> def
    let update : int * sigent -> unit
    let sub : int -> sigent option
    let clear : unit -> unit
    let get_modes : int -> Syntax.mode list option
    let set_modes : int * Syntax.mode list -> unit
    let get_p : int -> bool option
    let set_p : int * bool -> unit
    let abbreviation : int -> bool
end

module Sgn =
struct
    open Syntax
    exception NoSuch of int

    type def = DEF_NONE
		 | DEF_TERM of term
		 | DEF_TYPE of tp

    (* o_ means "original", i.e. before compression *)
    type sigent = {name : string, 
		   classifier : tClass,
		   o_classifier : tClass,
		   def : def,
		   o_def : def,
		   abbreviation : bool}

    let sgn_size = 14000 (* XXX *)
    let sigma : sigent option Array.array = Array.array(sgn_size, NONE)
    let all_modes : mode list option Array.array = Array.array(sgn_size, NONE)
    let all_ps : bool option Array.array = Array.array(sgn_size, NONE)

    fun  split (h::tl) 0 = ([], h, tl)
       | split (h::tl) n = let 
	     let (pre, thing, post) = split tl (n-1)
	 in
	     (h::pre, thing, post)
	 end
       | split [] n = split [NONE] n 

    fun clear () = let in
		       Array.modify (fun _ -> NONE) sigma;
		       Array.modify (fun _ -> NONE) all_modes;
		       Array.modify (fun _ -> NONE) all_ps
		   end
		       
    fun condec (s, a, oa) = {name = s, classifier = tclass a, o_classifier = tclass oa,
			     def = DEF_NONE, o_def = DEF_NONE, abbreviation = false}
    fun tycondec (s, k, ok) = {name = s, classifier = kclass k, o_classifier = kclass ok,
			       def = DEF_NONE, o_def = DEF_NONE, abbreviation = false}
    fun defn (s, a, oa, m, om) = {name = s, classifier = tclass a, o_classifier = tclass oa,
				  def = DEF_TERM m, o_def = DEF_TERM om, abbreviation = false}
    fun tydefn (s, k, ok, a, oa) = {name = s, classifier = kclass k, o_classifier = kclass ok,
				    def = DEF_TYPE a, o_def = DEF_TYPE oa, abbreviation = false}
    fun abbrev (s, a, oa, m, om) = {name = s, classifier = tclass a, o_classifier = tclass oa,
				    def = DEF_TERM m, o_def = DEF_TERM om, abbreviation = true}
    fun tyabbrev (s, k, ok, a, oa) = {name = s, classifier = kclass k, o_classifier = kclass ok,
				    def = DEF_TYPE a, o_def = DEF_TYPE oa, abbreviation = true}
    fun typeOfSigent (e : sigent) = Syntax.typeOf (#classifier e)

    fun setter table (n, x) = Array.update (table, n, SOME x)
    fun getter table id = Array.sub (table, id)

    let set_modes = setter all_modes
    let get_modes = getter all_modes
    let set_p = setter all_ps
    let get_p = getter all_ps
    let update = setter sigma
    let sub = getter sigma

    fun classifier id = (#classifier (Option.valOf(sub id)) handle Option => raise NoSuch id)
    fun o_classifier id = (#o_classifier (Option.valOf(sub id)) handle Option => raise NoSuch id)
    fun def id = (#def (Option.valOf(sub id)) handle Option => raise NoSuch id)
    fun o_def id = (#o_def (Option.valOf(sub id)) handle Option => raise NoSuch id)
    fun abbreviation id = (#abbreviation (Option.valOf(sub id)) handle Option => raise NoSuch id)
end