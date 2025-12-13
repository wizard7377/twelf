structure Reductio =
struct
	exception Unimp
	exception Error of string
	exception Matching of string
	exception NonPattern
	exception NotFound of string

        open Syntax

	datatype kinding_constraint = 
		 CON_LF (* Pi- only *)
	       | CON_PLUS (* Pi-, Pi+, [Pi] matched by strict occ in later args
                             not necessarily in return type *)
	       | CON_MINUS (* All Pis, and [Pi] can use strict occs in later args
                              and in return type. *)

        (* left side is open, (with respect to outer pi bindings)
           and right side is closed *)
	datatype eq_c = EltC of spinelt * spinelt
		      | SpineC of spine * spine
		      | TypeC of tp * tp
	type tp_c = term * tp

        (* equality checking *)
	fun (* GEN BEGIN FUN FIRST *) tp_eq (TRoot (n, sp), TRoot(n', sp')) = type_const_head_eq(n, n', sp, sp') (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) tp_eq (TPi(m,a,b),TPi(m',a',b')) = m = m' andalso tp_eq (a,a') andalso tp_eq (b,b') (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) tp_eq _ = false (* GEN END FUN BRANCH *)
	and (* GEN BEGIN FUN FIRST *) sp_eq ([],[]) = true (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) sp_eq (e::sp, e'::sp') = elt_eq (e,e') andalso sp_eq (sp, sp') (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) sp_eq _ = false (* GEN END FUN BRANCH *)
	and elt_eq (t, t') = elt_eq' (elt_eroot_elim t, elt_eroot_elim t')
	and (* GEN BEGIN FUN FIRST *) elt_eq' (Elt t, Elt t') = tm_eq (t, t') (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) elt_eq' (AElt t, AElt t') = atm_eq (t, t') (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) elt_eq' (Ascribe (t, a), Ascribe (t', a')) = ntm_eq (t,t') andalso tp_eq (a,a') (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) elt_eq' (Omit, Omit) = true (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) elt_eq' _ = false (* GEN END FUN BRANCH *)
	and (* GEN BEGIN FUN FIRST *) tm_eq (NTerm t, NTerm t') = ntm_eq (t, t') (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) tm_eq (ATerm t, ATerm t') = atm_eq (t, t') (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) tm_eq _ = false (* GEN END FUN BRANCH *)
	and (* GEN BEGIN FUN FIRST *) atm_eq (tm as ARoot(Const n,sp), tm' as ARoot(Const n',sp')) = const_head_eq(n, n', sp, sp', ATerm tm, ATerm tm') (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) atm_eq (ARoot(Var n,sp),ARoot(Var n',sp')) = n = n' andalso sp_eq (sp, sp') (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) atm_eq _ = false (* GEN END FUN BRANCH *) (* ERoots are taken care of at the spine element level *)
	and ntm_eq (t, t') = ntm_eq' (ntm_eroot_elim t, ntm_eroot_elim t')
	and (* GEN BEGIN FUN FIRST *) ntm_eq' (tm as NRoot(Const n,sp), tm' as NRoot(Const n',sp')) = const_head_eq(n, n', sp, sp', NTerm tm, NTerm tm') (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) ntm_eq' (Lam t, Lam t') = tm_eq (t, t') (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) ntm_eq' _ = false (* GEN END FUN BRANCH *)
        (* determine whether two roots are equal. n and n' are the cids of the heads, whether the
           roots happen to be nroots or aroots. sp and sp' are the spines, and tm and tm' are the
           entire roots. *)
	and const_head_eq (n, n', sp, sp', tm, tm') =
 	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val def = Sgn.def n (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val def' = Sgn.def n' (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val eq_and_strict = (n = n' andalso (def = Sgn.DEF_NONE orelse not (Sgn.abbreviation n))) (* GEN END TAG OUTSIDE LET *)
 		fun redux t n sp = reduce(srTerm(t, typeOf(Sgn.classifier n)), sp) 
	    in
		    case (eq_and_strict, def, def') of 
			(true, _, _) => sp_eq(sp, sp')
		      | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) => false
		      | (_, Sgn.DEF_TERM t, Sgn.DEF_TERM t') => tm_eq(redux t n sp, redux t' n' sp')
		      | (_, Sgn.DEF_TERM t, Sgn.DEF_NONE) => tm_eq(redux t n sp, tm')
		      | (_, Sgn.DEF_NONE, Sgn.DEF_TERM t') => tm_eq(tm, redux t' n' sp')
		      | _ => raise Syntax "invariant violation"
	    end
         (* similar thing for atomic types. Here we need not include redundant arguments for the entire
            TRoot since there is only one kind of TRoot (not both ARoot and NRoot in the case of terms)
            so we just build it back up from scratch *)
	and type_const_head_eq (n, n', sp, sp') =
 	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val def = Sgn.def n (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val def' = Sgn.def n' (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val eq_and_strict = n = n' andalso (def = Sgn.DEF_NONE orelse not (Sgn.abbreviation n)) (* GEN END TAG OUTSIDE LET *)
		fun redux a n sp = tp_reduce(a, kindOf(Sgn.classifier n), sp)
	    in
		    case (eq_and_strict, def, def') of 
			(true, _, _) => sp_eq(sp, sp')
		      | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) => false
		      | (_, Sgn.DEF_TYPE a, Sgn.DEF_TYPE a') => tp_eq(redux a n sp, redux a' n' sp')
		      | (_, Sgn.DEF_TYPE a, Sgn.DEF_NONE) => tp_eq(redux a n sp, TRoot(n',sp'))
		      | (_, Sgn.DEF_NONE, Sgn.DEF_TYPE a') => tp_eq(TRoot(n,sp), redux a' n' sp')
		      | _ => raise Syntax "invariant violation"
	    end

        (* is an equality constraint satisfied? *)
	fun (* GEN BEGIN FUN FIRST *) eq_c_true (EltC(e,e')) = elt_eq(e, e') (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) eq_c_true (SpineC(s,s')) = sp_eq(s, s') (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) eq_c_true (TypeC(a,a')) = tp_eq(a, a') (* GEN END FUN BRANCH *)

        (* The type ppsubst is a compact way of representing a
           class of substitutions that contains all of the pattern
           substitutions. These are the "prepattern" substitutions,
           the ones that are of the form 
           i1.i2. ... in . shift^m
           where all the i1...in are variables. *)
        (* ([i1, i2, ... , in], m) represents i1.i2. ... in . shift^m *)
	type ppsubst = int list * int

	(* pp_shift pps m: compute pps o shift^m *)
	fun pp_shift (vs,shift) m = 
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val len = length vs (* GEN END TAG OUTSIDE LET *)
	    in
		if m < len
		then (List.drop(vs, m),shift)
		else ([], m - len + shift)
	    end

        (* pp_nth: extract the result of applying a ppsubst to the nth variable *)
	fun pp_nth (vs,shift) n = 
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val len = length vs (* GEN END TAG OUTSIDE LET *)
	    in
		if n < len 
		then List.nth(vs, n) 
		else n - len + shift
	    end

        (* pp_o: compose two ppsubsts *)
	fun pp_o (pps, (vs, shift)) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val (vs', shift') =  pp_shift pps shift (* GEN END TAG OUTSIDE LET *)
	    in
		((map (pp_nth pps) vs) @ vs', shift')
	    end

        (* pp_comp: compose a list of ppsubsts *)
	fun pp_comp ppsl = foldr pp_o ([],0) ppsl

        (* pp_normalize s
           if a substitution s is equal to a 'prepattern'
           i1.i2. ... in . shift^m (no restriction on the i's being distinct)
           returns ([i1, i2, ... , in], m).
           Otherwise raises Domain. *)
	fun pp_normalize s = pp_normalize' s
	and (* GEN BEGIN FUN FIRST *) pp_normalize' Id = ([], 0) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) pp_normalize' (TermDot(t, a, s)) =
	    let 
                 (* if the term being consed on is not an eta-expansion of
                    a variable, forget about it *)
		 (* GEN BEGIN TAG OUTSIDE LET *) val v = Strict.eta_contract_var (Elt t) handle Strict.EtaContract => raise Domain (* GEN END TAG OUTSIDE LET *)
		 (* GEN BEGIN TAG OUTSIDE LET *) val (vs, shift) = pp_normalize' s (* GEN END TAG OUTSIDE LET *)
	     in
		 (v::vs, shift)
	     end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) pp_normalize' (ZeroDotShift s) = 
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val (vs, shift) = pp_normalize' s (* GEN END TAG OUTSIDE LET *)
	    in
		(0 :: (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => x + 1 (* GEN END FUNCTION EXPRESSION *)) vs), shift + 1)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) pp_normalize' (Shift (n, m)) = 
	    (* using the fact that Shift (n+1) m = ZeroDotShift (Shift n m) *)
	    (List.tabulate (n, ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => x (* GEN END FUNCTION EXPRESSION *))), n + m) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) pp_normalize' (EVarDot _) = raise Domain (* GEN END FUN BRANCH *) (* XXX: Correct??? *)
	  | (* GEN BEGIN FUN BRANCH *) pp_normalize' (VarOptDot (no, s)) = 
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val (vs, shift) = pp_normalize' s (* GEN END TAG OUTSIDE LET *)
	    in
		case no of 
		    SOME n => (n :: vs, shift)
		  | NONE => raise Error "??? I'm not sure this is really wrong"
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) pp_normalize' (Compose sl) = prepattern (substs_comp sl) (* GEN END FUN BRANCH *)

	(* prepattern: convert a subst into a ppsubst *)
        (* raises Domain if it is not a prepattern *)
	and prepattern (s : subst) = pp_normalize s

	(* pp_ispat: is this ppsubst a pattern substitution? *)
	fun (* GEN BEGIN FUN FIRST *) pp_ispat ([],shift) = true (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) pp_ispat (n::s,shift) = let fun isn x = (x = n)
				     fun hasn s = List.exists isn s
				 in
				     n < shift andalso
				     not (hasn s) andalso
				     pp_ispat (s,shift)
				 end (* GEN END FUN BRANCH *)

        (* take a list of int options and a shift value and
        produce an actual substitution. This is morally a one-sided
        inverse to pp_normalize *)
	fun (* GEN BEGIN FUN FIRST *) makesubst ([],0) = Id (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) makesubst ([],shift) = Shift (0, shift) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) makesubst (v::vs,shift) = VarOptDot (v, makesubst (vs,shift)) (* GEN END FUN BRANCH *)

        (* take in a ppsubst and return a substitution (which may involve VarOptDots) that is its inverse. *)
	fun pp_invert (vs,shift) =
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val inds = List.tabulate(shift, ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => x (* GEN END FUNCTION EXPRESSION *))) (* GEN END TAG OUTSIDE LET *)
		fun (* GEN BEGIN FUN FIRST *) search n [] (x : int) = NONE (* GEN END FUN FIRST *)
		  | (* GEN BEGIN FUN BRANCH *) search n (h::tl) x = 
		    if x = h 
		    then SOME n
		    else search (n+1) tl x (* GEN END FUN BRANCH *)
	    in
		makesubst (map (search 0 vs) inds, length vs)
	    end 

        (* Here begins all the matching code.
           flex_left takes an uninstantiated evar, a substitution, and a right-hand-side of an equation.
           The equation is
           E[sl] = RHS
           If it can successfully instantiate E with RHS[sl^-1], then it does so
           imperatively and returns ().

           If sl is not pattern it raises NonPattern.
           If RHS is not in the range of sl, then MissingVar is raised by substitution *)
	fun (* GEN BEGIN FUN FIRST *) flex_left ((r as ref NONE,a), s : subst, rhs) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val pps = prepattern s handle Domain => raise NonPattern (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = if pp_ispat pps then () else raise NonPattern (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val ppsi = pp_invert pps (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val rhs' = subst_term ppsi (termof rhs) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = r := SOME rhs' (* GEN END TAG OUTSIDE LET *)
	    in
		()
	    end (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) flex_left _ = raise Error "evar invariant violated" (* GEN END FUN BRANCH *)

        (* match_one' takes an equation (which by invariant does not
           have an instantiated evar on the left, and is ground on the
           right) and returns a list of smaller equations that are
           equivalent to it, or else throws NonPattern in the event
           that it finds a flex-rigid equation where the flex side is
           not pattern. *)

	(* XXX this just_one stuff is here for debugging: replace with match_one *)
	fun just_one c = [c]
	and just_one' c = [c]
	and (* GEN BEGIN FUN FIRST *) match_one' (EltC(Elt(NTerm(Lam t)),Elt(NTerm(Lam t')))) =
	    just_one (EltC(Elt t, Elt t')) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (EltC(elt as Elt(NTerm(NRoot(Const n,s))), elt' as Elt(NTerm(NRoot(Const n',s'))))) =
	    match_const_head(n,n',s,s',elt,elt',"c- head mismatch") (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (EltC(elt as Elt(ATerm(ARoot(Const n,s))), elt' as Elt(ATerm(ARoot(Const n',s'))))) =
	    match_const_head(n,n',s,s',elt,elt',"c+ head mismatch") (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (EltC(Elt(ATerm(ARoot(Var n,s))),Elt(ATerm(ARoot(Var n',s'))))) =
	    if n = n' 
	    then just_one' (SpineC(s, s'))
	    else raise Matching "var head mismatch" (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (EltC(AElt t,AElt t')) =
	    just_one' (EltC(Elt(ATerm t), Elt(ATerm t'))) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (EltC(Ascribe(m,a),Ascribe(m',a'))) =
	    match_two (EltC(Elt(NTerm m), Elt(NTerm m'))) (TypeC(a, a')) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (EltC(Omit,Omit)) = [] (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (TypeC(TPi(m,a,b),TPi(m',a',b'))) = 
	    if m = MINUS andalso m' = MINUS
	    then match_two (TypeC(a, a')) (TypeC(b, b'))
	    else raise Matching "mode mismatch" (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (TypeC(TRoot(n,s), TRoot(n',s'))) = match_type_const_head (n, n', s, s', "type family mismatch") (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (SpineC([],[])) = [] (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (SpineC(h::s,h'::s')) = match_two (EltC(h, h'))  (SpineC(s, s')) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' (EltC(Elt(ATerm(ERoot(ev,s : subst))), elt)) = (flex_left (ev, s, elt); []) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) match_one' x = raise Matching "doesn't match" (* GEN END FUN BRANCH *)

	(* PERF: this second elt_eroot_elim on elt' seems like it ought to be unnecessary if
	     I eliminate all eroots at synth time *)
	and (* GEN BEGIN FUN FIRST *) match_one (EltC(elt,elt')) = match_one' (EltC(elt_eroot_elim elt, elt_eroot_elim elt')) (* GEN END FUN FIRST *) 
	  | (* GEN BEGIN FUN BRANCH *) match_one e = match_one' e (* GEN END FUN BRANCH *)
	and match_two e1 e2 = [e1, e2] 
	and match_const_head (n, n', s, s', elt, elt', err) =
 	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val def = Sgn.def n (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val def' = Sgn.def n' (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val eq_and_strict = n = n' andalso (def = Sgn.DEF_NONE orelse not (Sgn.abbreviation n)) (* GEN END TAG OUTSIDE LET *)
		fun redux t n sp = reduce(srTerm(t, typeOf(Sgn.classifier n)), sp)
		(* GEN BEGIN TAG OUTSIDE LET *) val eq = 	
		    case (eq_and_strict, def, def') of 
			(true, _, _) => SpineC(s, s')
		      | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) => raise Matching err
		      | (_, Sgn.DEF_TERM t, Sgn.DEF_TERM t') => EltC(Elt(redux t n s), Elt(redux t' n' s'))
		      | (_, Sgn.DEF_TERM t, Sgn.DEF_NONE) => EltC(Elt(redux t n s), elt')
		      | (_, Sgn.DEF_NONE, Sgn.DEF_TERM t') => EltC(elt, Elt(redux t' n' s'))
		      | _ => raise Matching "invariant violation" (* GEN END TAG OUTSIDE LET *)
	    in
		just_one' eq
	    end 
	and match_type_const_head (n, n', s, s', err) =
 	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val def = Sgn.def n (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val def' = Sgn.def n' (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val eq_and_strict = n = n' andalso (def = Sgn.DEF_NONE orelse not (Sgn.abbreviation n)) (* GEN END TAG OUTSIDE LET *)
		fun redux a n sp = tp_reduce(a, kindOf(Sgn.classifier n), sp)
		(* GEN BEGIN TAG OUTSIDE LET *) val eq = 	
		    case (eq_and_strict, def, def') of 
			(true, _, _) => SpineC(s, s')
		      | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) => raise Matching err
		      | (_, Sgn.DEF_TYPE a, Sgn.DEF_TYPE a') => TypeC(redux a n s, redux a' n' s')
		      | (_, Sgn.DEF_TYPE a, Sgn.DEF_NONE) => TypeC(redux a n s, TRoot(n', s'))
		      | (_, Sgn.DEF_NONE, Sgn.DEF_TYPE a') => TypeC(TRoot(n, s), redux a' n' s')
		      | _ => raise Matching "invariant violation" (* GEN END TAG OUTSIDE LET *)
	    in
		just_one' eq
	    end

	fun matching (p) =  let
	    fun (* GEN BEGIN FUN FIRST *) matching' (c::p,p') =
		(let (* GEN BEGIN TAG OUTSIDE LET *) val eqs = match_one c (* GEN END TAG OUTSIDE LET *) in matching'(eqs @ p, p') end
		 handle NonPattern => matching'(p, c::p')) (* GEN END FUN FIRST *)
	      | (* GEN BEGIN FUN BRANCH *) matching' ([], p') = p' (* GEN END FUN BRANCH *)
	in
	    matching' (p,[]) 
	end


(*	fun ctxcons (a, G) = map (shift_tp 0) (a::G) *)
	fun ctxcons (a, G) = a::G

	datatype cg_mode = CG_SYNTH
			 | CG_CHECK of tp

(* 	val constraint_gen : tp list -> spine * tp * cg_mode -> eq_c list * tp_c list
        fun constraint_gen G (s, z, c) = (p, q, aopt) *)
	(* invariants: 
	   s is ground
	   if c is CG_CHECK c', then c' is ground 
           right-hand sides of p,q are ground
           left-hand sides of p,q and z may involve evars
           
           the returned aopt...
           ... is SOME of a type if c was CG_SYNTH
           ... is NONE           if c was CG_CHECK of something *)

	fun constraint_gen G (s, z, c) = constraint_gen' G (s, z, c)
	and (* GEN BEGIN FUN FIRST *) constraint_gen' G ([], a as TRoot _, CG_CHECK(a' as TRoot _)) = 
	    ([TypeC(a,a')], [], NONE) (* GEN END FUN FIRST *) (* PERF: we might be able to reject this faster if we knew a and a'
                                         were not defined types and were different *)
	  | (* GEN BEGIN FUN BRANCH *) constraint_gen' G ([], TRoot(n,s), CG_SYNTH) = 
	     ([], [], SOME(TRoot(n, s))) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) constraint_gen' G (Omit::s, TPi(OMIT, a, z), c) =
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val ev : evar = (ref NONE, a) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val z' = subst_tp (EVarDotId ev) z (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (p,q,aa) = constraint_gen' G (s, z', c) (* GEN END TAG OUTSIDE LET *)
	    in
		(p, q, aa)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) constraint_gen' G ((Elt m)::s, TPi(MINUS, a, z), c) =
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val z' = subst_tp (TermDot (m, a, Id)) z (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (p,q,aa) = constraint_gen' G (s, z', c) (* GEN END TAG OUTSIDE LET *)
	    in
		(p, (m,a)::q, aa)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) constraint_gen' G ((AElt m)::s, TPi(PLUS, a, z), c) =
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val a' = synth(G, m) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val z' = subst_tp (TermDot (ATerm m, a, Id)) z (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (p,q,aa) = constraint_gen' G (s, z', c) (* GEN END TAG OUTSIDE LET *)
	    in
                (* Same PERF comment here as above *)
		((TypeC(a,a'))::p, q, aa)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) constraint_gen' G ((Ascribe(m,a'))::s, TPi(PLUS, a, z), c) =
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val z' = subst_tp (TermDot (NTerm m, a, Id)) z (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (p,q,aa) = constraint_gen' G (s, z', c) (* GEN END TAG OUTSIDE LET *)
	    in
                (* As well as here *)
		((TypeC(a,a'))::p, q, aa)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) constraint_gen' _ _ = raise Error "spine doesn't match type" (* GEN END FUN BRANCH *)

        (* similar to above but we just have a putative type and its kind, and return nothing but constraints *)
	and (* GEN BEGIN FUN FIRST *) tp_constraint_gen G ([], Type) =  ([], []) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) tp_constraint_gen G (Omit::s, KPi(OMIT, a, z)) =
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val ev : evar = (ref NONE, a) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val z' = subst_knd (EVarDotId ev) z (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (p,q) = tp_constraint_gen G (s, z') (* GEN END TAG OUTSIDE LET *)
	    in
		(p, q)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) tp_constraint_gen G ((Elt m)::s, KPi(MINUS, a, z)) =
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val z' = subst_knd (TermDot (m, a, Id)) z (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (p,q) = tp_constraint_gen G (s, z') (* GEN END TAG OUTSIDE LET *)
	    in
		(p, (m,a)::q)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) tp_constraint_gen G ((AElt m)::s, KPi(PLUS, a, z)) =
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val a' = synth(G, m) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val z' = subst_knd (TermDot (ATerm m, a, Id)) z (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (p,q) = tp_constraint_gen G (s, z') (* GEN END TAG OUTSIDE LET *)
	    in
		((TypeC(a,a'))::p, q)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) tp_constraint_gen G ((Ascribe(m,a'))::s, KPi(PLUS, a, z)) =
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val z' = subst_knd (TermDot (NTerm m, a, Id)) z (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (p,q) = tp_constraint_gen G (s, z') (* GEN END TAG OUTSIDE LET *)
	    in
		((TypeC(a,a'))::p, q)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) tp_constraint_gen _ _ = raise Error "spine doesn't match type" (* GEN END FUN BRANCH *)

	and check_equality_constraints p = List.all eq_c_true p

	and check_typing_constraints G q = List.all ((* GEN BEGIN FUNCTION EXPRESSION *) fn (m,a) => check(G, m, a) (* GEN END FUNCTION EXPRESSION *)) q

        (* returns true on success or raises Matching on failure *)
	and matching_succeeds G (p,q) =
	    let
 		(* GEN BEGIN TAG OUTSIDE LET *) val p' = matching p (* GEN END TAG OUTSIDE LET *) (* evar side-effects affect q, raises Matching if matching fails *)
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = if check_equality_constraints p' then () else raise Matching "residual equality constraints failed" (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = if check_typing_constraints G q then () else raise Matching "residual typing constraints failed" (* GEN END TAG OUTSIDE LET *)
	    in
		true
	    end

	and (* GEN BEGIN FUN FIRST *) check_spinelt (G, Elt t, a) = check(G, t, a) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) check_spinelt (G, AElt t, a) = check(G, ATerm t, a) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) check_spinelt (G, Ascribe(t,a), a') = (tp_eq(a, a') andalso check(G, NTerm t, a)) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) check_spinelt (G, Omit, _) = raise Error "cannot check omitted arguments" (* GEN END FUN BRANCH *)

	and (* GEN BEGIN FUN FIRST *) check (G, NTerm(Lam(t)), TPi(_,a,b)) = check(ctxcons (a, G), t, b) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) check (G, ATerm(t), a) = (tp_eq(synth(G, t), a) handle Error s =>  false) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) check (G, NTerm(NRoot(Const n, s)), a) = 
	    let
		 (* GEN BEGIN TAG OUTSIDE LET *) val b = case Sgn.classifier n of 
			     tclass b => b
			   | _ => raise Error "signature invariant violated!" (* GEN END TAG OUTSIDE LET *)
		 (* GEN BEGIN TAG OUTSIDE LET *) val (p, q, _) = constraint_gen G  (s, b, CG_CHECK a) (* GEN END TAG OUTSIDE LET *) (* creates ref cells for evars *)
	     in
		 matching_succeeds G (p, q)
	     end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) check _ = false (* GEN END FUN BRANCH *)
	and (* GEN BEGIN FUN FIRST *) check_kind (G, Type) = true (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) check_kind (G, KPi(OMIT,a,k)) = check_type CON_LF (G,a) andalso 
					    check_kind(ctxcons (a, G), k) andalso
					    Strict.check_strict_kind(k) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) check_kind (G, KPi(_,a,k)) = check_type CON_LF (G,a) andalso
					 check_kind(ctxcons (a, G), k) (* GEN END FUN BRANCH *)

	and (* GEN BEGIN FUN FIRST *) check_type _ (G, TRoot(n, s)) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val k = case Sgn.classifier n of 
			    kclass k => k
			  | _ => raise Error "signature invariant violated!" (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (p, q) = tp_constraint_gen G  (s, k) (* GEN END TAG OUTSIDE LET *) (* creates ref cells for evars *)
	    in
		matching_succeeds G (p, q)
	    end (* GEN END FUN FIRST *)

	  | (* GEN BEGIN FUN BRANCH *) check_type con (G, TPi(OMIT,a,b)) = 
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val plusconst = case con of
		 CON_LF => raise Error "TPi(OMIT) where a pure LF function type expected"
	       | CON_PLUS => true
	       | CON_MINUS => false (* GEN END TAG OUTSIDE LET *)
	    in
		check_type CON_LF (G,a) andalso
			     check_type con (ctxcons (a, G), b) andalso
			     Strict.check_strict_type plusconst b 
	    end (* GEN END FUN BRANCH *)
 
	  | (* GEN BEGIN FUN BRANCH *) check_type con (G, TPi(m,a,b)) = 
	    (case (con,m) of
		 (CON_LF, PLUS) => raise Error "TPi(PLUS) where a pure LF function type expected"
	       | _ => check_type CON_LF (G,a) andalso 
		      check_type con (ctxcons (a, G), b)) (* GEN END FUN BRANCH *)
(* check a type spine *)
	and (* GEN BEGIN FUN FIRST *) check_type' (G, Type, []) = true (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) check_type' (G, KPi(_,a,k), m::s) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = if check_spinelt(G, m, a) then () else raise Error "argument type mismatch" (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val k' = subst_knd (TermDot(termof m,a,Id)) k (* GEN END TAG OUTSIDE LET *)
	    in
		check_type'(G,k',s)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) check_type' _ = false (* GEN END FUN BRANCH *)
	and (* GEN BEGIN FUN FIRST *) synth (G, ARoot(Var n, s)) = synth'(G, ctxLookup(G, n), s) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) synth (G, ARoot(Const n, s)) = 
	    let
		 (* GEN BEGIN TAG OUTSIDE LET *) val b = case Sgn.classifier n of 
			     tclass b => b
			   | _ => raise Error "signature invariant violated!" (* GEN END TAG OUTSIDE LET *)
		 (* GEN BEGIN TAG OUTSIDE LET *) val (p, q, aopt) = constraint_gen G  (s, b, CG_SYNTH) (* GEN END TAG OUTSIDE LET *) (* creates ref cells for evars *)
(* DEBUG		 val _ = l3 := (p, q, aopt)::(!l3) *)
		 (* GEN BEGIN TAG OUTSIDE LET *) val _ = matching_succeeds G (p,q) (* GEN END TAG OUTSIDE LET *) (* raises Matching if not *)
	     in
		 Option.valOf aopt (* by invariant, aopt must be SOME *)
	     end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) synth (G, t as ERoot _) = elt_synth (G, eroot_elim_plus t) (* GEN END FUN BRANCH *)
	and (* GEN BEGIN FUN FIRST *) synth' (G, a as TRoot(_,_), []) = a (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) synth' (G, TPi(_,a,b), m::s) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = if check_spinelt(G, m, a) then () else raise Error "argument type mismatch" (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val b' = subst_tp (TermDot(termof m,a,Id)) b (* GEN END TAG OUTSIDE LET *)
	    in
		synth' (G, b', s)
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) synth' _ = raise Error "applying nonfunction to argument" (* GEN END FUN BRANCH *)
	and (* GEN BEGIN FUN FIRST *) elt_synth (G, AElt t) = synth (G, t) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) elt_synth (G, Ascribe(t,a)) = if check(G,NTerm t,a) then a else raise Error "ascription doesn't check" (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) elt_synth (G, Elt _) = raise Error "trying to synthesize a merely checkable element" (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) elt_synth (G, Omit) = raise Error "trying to synthesize an omitted argument" (* GEN END FUN BRANCH *)

	fun check_plusconst_type t = check_type CON_PLUS ([], t)
	fun check_minusconst_type t = check_type CON_MINUS ([], t)

(* check_strictness_type : bool -> tp -> bool

   For a type B = Pi x1 : A1 . Pi x2 : A2 ... a . S (where the Pis
   may be omit or plus or minus) 
   and plus_const : bool
   the call
   check_strictness_type plus_const B
   returns true iff for every i, the following holds:
     the variable xi has either a strict occurrence in Aj for
     some j > i where xj is bound by a plus-Pi, or else 
     plus_const = false and xi has a strict occurrence in a . S.

  This function does *not* check to make sure types such as A1
  do not contain omit-Pis and plus-Pis. This test is carried
  out in check_type. check_strictness_type is useful mainly when
  we are simply deciding, by trial and error, which of the arguments
  to B we should omit and which to force to be synthesizing.
 *)
	fun (* GEN BEGIN FUN FIRST *) check_strictness_type _ (TRoot(n, s)) = true (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) check_strictness_type plusconst (TPi(OMIT,_,b)) = 
	    check_strictness_type plusconst b andalso Strict.check_strict_type plusconst b (* GEN END FUN BRANCH *) 
	  | (* GEN BEGIN FUN BRANCH *) check_strictness_type plusconst (TPi(_,_,b)) = check_strictness_type plusconst b (* GEN END FUN BRANCH *)
							
	(* GEN BEGIN TAG OUTSIDE LET *) val check_plusconst_strictness = check_strictness_type true (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val check_minusconst_strictness = check_strictness_type false (* GEN END TAG OUTSIDE LET *)
end

