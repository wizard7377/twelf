
structure Syntax =
struct
        exception Syntax of string
	exception MissingVar


	datatype mode = MINUS
		      | PLUS
		      | OMIT

	datatype nterm =
	         Lam of term
	       | NRoot of head * spine (* c^- *)
	     and aterm =
	        ARoot of head * spine (* c^+, x *)
	      | ERoot of evar * subst (* X[s] lowered to base type *)
	     and head =
		 Var of int
	       | Const of int
	     and tp =
		 TRoot of int * spine
	       | TPi of mode * tp * tp
	     and knd =
		 Type
	       | KPi of mode * tp * knd
	     and spinelt =
		 Elt of term           (*   M    *)
	       | AElt of aterm         (*  (R:)  *)
	       | Ascribe of nterm * tp (*  (N:A) *)
	       | Omit                  (*   *    *)
	     and term =
		 NTerm of nterm
	       | ATerm of aterm
	     and subst = 
		 Id
	       | Shift of int * int (* Shift n m = 0.1.2. ... .n-1.n+m.n+m+1.n+m+2. ... *)
	       | ZeroDotShift of subst
	       | TermDot of term * tp * subst
	       | EVarDot of evar * subst list * subst (* X[sl] . s *)
	       | VarOptDot of int option * subst
	       | Compose of subst list
	withtype spine = spinelt list
	and evar = (term option ref) * tp

        (* special hack for type functions used only in tp_reduce *)
	datatype tpfn = tpfnType of tp
		      | tpfnLam of tpfn

	fun EVarDotId ev = EVarDot (ev, [], Id)

(*	type decl = string * Parse.term *)
(*	type ctx = decl list *)

	datatype class = kclass of knd
			| tclass of tp

        (* termof elm
        returns the term part of the spine element elm *)
	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) termof (Elt t) = t (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) termof (AElt t) = ATerm t (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) termof (Ascribe(t, a)) = NTerm t (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) termof (Omit) = raise Syntax "invariant violated: arguments to variables cannot be omitted" (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)



	datatype subst_result = srVar of int 
			      | srTerm of term * tp
			      | srEVar of evar * subst list

	exception Debugs of subst_result * spinelt list

	fun curryfoldr sf sl x = foldr ((* GEN BEGIN FUNCTION EXPRESSION *) (* GEN BEGIN FUNCTION EXPRESSION *) fn (s,x') => sf s x' (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) x sl


	(* lower (a, sp)
           supposing we have an evar of (potentially higher-order)
           type a, applied to a spine sp, return the lowered type of
           that evar and a substitution to apply it to *)
        (* XXX: so we're not carrying out substitutions over the type
                as we recurse down: is this right? I think it is. *)
	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) lower acc (a as TRoot _, []) = (a, acc) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) lower acc (TPi(m,a,b), elt::sp) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val newacc = TermDot(termof elt, subst_tp acc a, acc) (* GEN END TAG OUTSIDE LET *)
	    in
		lower newacc (b, sp)
	    end (* GEN END CASE BRANCH *)
(*
	  | lower base (TPi(m,a,b), elt::sp) = 
	    let
		val (aa,subst) = lower base (b, sp)
	    in
		(aa, TermDot(termof elt, a, subst))
	    end *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) lower _ _ = raise Syntax "type mismatch in lowering" (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
			      
        (* substNth (subst, n)
        returns the result of applying the substitution subst
        to the index n *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) substNth (Id,n) = srVar n (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) substNth (ZeroDotShift s, n) = if n = 0 then srVar 0 else
					  (case substNth(s, n - 1)
					    of
					      srTerm(t, a) => srTerm(shift t, shift_tp 0 a)
					    | srVar n => srVar (n+1)
					    | srEVar (ev, sl) => srEVar(ev, (Shift (0,1))::sl)) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) substNth (TermDot(m, a, s), n) = if n = 0 then srTerm(m, a) else substNth(s, n-1) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) substNth (EVarDot (ev,sl,s), n) = if n = 0 then srEVar (ev, sl) else substNth(s, n-1) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) substNth (Shift (n, m), n') = if n' >= n then srVar (n' + m) else srVar n' (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) substNth (VarOptDot (no, s), n') = if n' = 0 
					       then case no of
							SOME n => srVar n
						      | NONE => raise MissingVar
					       else substNth(s, n'-1) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) substNth (Compose [], n) = srVar n (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) substNth (Compose (h::tl), n) = subst_sr h (substNth(Compose tl, n)) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_sr s (srTerm(t,a)) = srTerm(subst_term s t, subst_tp s a) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) subst_sr s (srVar n) = substNth (s, n) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_sr s (srEVar (ev, sl)) = srEVar(ev, s::sl) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *) (* the type of the evar is understood to be
							        affected by the subst as well *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_spinelt Id x = x (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) subst_spinelt s (Elt t) = Elt(subst_term s t) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_spinelt s (AElt t) = subst_aterm_plus s t (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_spinelt s (Ascribe(t, a)) = Ascribe(subst_nterm s t, subst_tp s a) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_spinelt s Omit = Omit (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and subst_spine s sp = map (subst_spinelt s) sp
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_term s (ATerm t) = subst_aterm s t (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_term s (NTerm t) = NTerm(subst_nterm s t) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_nterm s (Lam t) = Lam(subst_term (ZeroDotShift s) t) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_nterm s (NRoot(h,sp)) = NRoot(h, subst_spine s sp) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_aterm s (ARoot(Const n,sp)) = ATerm(ARoot(Const n, subst_spine s sp)) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) subst_aterm s (ARoot(Var n,sp)) = reduce (substNth(s,n),subst_spine s sp) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_aterm s (ERoot(ev as (ref NONE,_),sl)) = ATerm(ERoot(ev,subst_compose(s,sl))) (* GEN END CASE BRANCH *) (* XXX right??? *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_aterm s (t as ERoot _) = subst_term s (eroot_elim t) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_aterm_plus s (ARoot(Const n,sp)) = AElt(ARoot(Const n, subst_spine s sp)) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) subst_aterm_plus s (ARoot(Var n,sp)) = reduce_plus (substNth(s,n),subst_spine s sp) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_aterm_plus s (ERoot(ev as (ref NONE,_),sl)) = AElt(ERoot(ev,subst_compose(s,sl))) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_aterm_plus s (t as ERoot _) = subst_spinelt s (eroot_elim_plus t) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)  (* XXX right??? *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_tp s (TRoot(h,sp)) = TRoot(h, subst_spine s sp) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_tp s (TPi(m,b,b')) = TPi(m,subst_tp s b, subst_tp (ZeroDotShift s) b') (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_knd s (Type) = Type (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_knd s (KPi(m,b,k)) = KPi(m,subst_tp s b, subst_knd (ZeroDotShift s) k) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) reduce (srVar n, sp) = ATerm(ARoot(Var n, sp)) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) reduce (srTerm(NTerm(Lam n), TPi(_,a,b)), h::sp) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val s = TermDot(termof h,a,Id) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val n' = subst_term s n (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val b' = subst_tp s b (* GEN END TAG OUTSIDE LET *)
	    in
		reduce (srTerm(n', b'), sp)
	    end (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce (srTerm(t as NTerm(NRoot(h,sp)), a), []) = t (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce (srTerm(t as ATerm(ARoot(h,sp)), a), []) = t (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce (srTerm(ATerm(t as ERoot ((ref (SOME _), _), _)), a), []) = reduce(srTerm(eroot_elim t, a), []) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce (srTerm(ATerm(t as ERoot ((ref NONE, _), _)), a), []) = ATerm t (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce (srEVar ((x, a), sl), sp) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val (a',subst) = lower (substs_comp sl) (a, sp) (* GEN END TAG OUTSIDE LET *)
	    in
		ATerm(ERoot((x,a'),subst))
	    end (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) reduce _ = raise Syntax "simplified-type mismatch in reduction" (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) reduce_plus (srVar n, sp) = AElt(ARoot(Var n, sp)) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) reduce_plus (srTerm(NTerm(Lam n), TPi(_,a,b)), h::sp) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val s = TermDot(termof h,a,Id) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val n' = subst_term s n (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val b' = subst_tp s b (* GEN END TAG OUTSIDE LET *)
	    in
		reduce_plus (srTerm(n', b'), sp)
	    end (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce_plus (srTerm(NTerm(t as NRoot(h,sp)), a), []) = Ascribe(t, a) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce_plus (srTerm(ATerm(t as ARoot(h,sp)), a), []) = AElt t (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce_plus (srTerm(ATerm(t as ERoot ((ref (SOME _), _), _)), a), []) = reduce_plus(srTerm(eroot_elim t, a), []) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce_plus (srTerm(ATerm(t as ERoot ((ref NONE, _), _)), a), []) = AElt t (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) reduce_plus (srEVar ((x, a), sl), sp) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val (a',subst) = lower (substs_comp sl) (a, sp) (* GEN END TAG OUTSIDE LET *)
	    in
		AElt(ERoot((x,a'),subst))
	    end (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) reduce_plus (x,y) = (raise Debugs (x,y); raise Syntax "simplified-type mismatch in reduction") (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

        (* val tp_reduce : tp * knd * spine -> tp
           tp_reduce (a, k, sp) computes the result
           of reducing (.\ .\ ... .\ a) . sp
           assuming (.\ .\ ... .\ a) : k
           (where the number of lambdas is the number
            of pis found in k) 
        *) 

	and tp_reduce (a, k, sp) =
	    let 
		fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_tpfn s (tpfnLam a) = tpfnLam(subst_tpfn (ZeroDotShift s) a) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
		  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_tpfn s (tpfnType a) = tpfnType(subst_tp s a) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
		fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) tp_reduce'(tpfnLam(a), KPi(_,b,k), h::sp) = 
		    let
			val s = TermDot(termof h, b, Id)
			val a' = subst_tpfn s a
			val k' = subst_knd s k
		    in
			tp_reduce' (a', k', sp)
		    end (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
		  | (* GEN BEGIN CASE BRANCH *) tp_reduce' (tpfnType a, Type, []) = a (* GEN END CASE BRANCH *)
		  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) tp_reduce' _ = raise Syntax "simplified-kind mismatch in type reduction" (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *) 
		fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) wrap (a, KPi(_,b,k)) = tpfnLam (wrap(a,k)) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
		  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) wrap (a, Type) = tpfnType a (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
		(* GEN BEGIN TAG OUTSIDE LET *) val aw = wrap (a, k) (* GEN END TAG OUTSIDE LET *)
	    in 
		tp_reduce' (aw, k, sp)
	    end

        (* elt_eroot_elim e
        returns a spine element equal to e but makes sure that it's not
        an instatiated ERoot. That is, it carries out the instantiation
        and substitutions involved therein. *)

	(* probably not the right way to do things considering I have Compose *)
	and substs_term x = curryfoldr subst_term x
	and substs_tp x = curryfoldr subst_tp x

	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) eroot_elim (ERoot((ref (SOME t), a), subst)) = subst_term subst t (* GEN END CASE FIRST *) (* GEN END CASE FIRST *) 
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) eroot_elim x = ATerm x (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) eroot_elim_plus (ERoot((ref (SOME t), a), subst)) = 
	    let
		val newt =  subst_term subst t 
	    in
		case newt of
		    ATerm t => AElt t
		  | NTerm t => Ascribe(t,  subst_tp subst a)
	    end (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) eroot_elim_plus x = AElt x (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

        (* YYY: the following doesn't avoid incurring polyequal. why??? 

	datatype foo =
	        Foo of baralias
	     and bar =
	        Bar of foo 
	withtype baralias = bar;

        - fn (x : foo, y : foo) => x = y;
        stdIn:376.28 Warning: calling polyEqual
        val it = fn : foo * foo -> bool

        doesn't really matter anymore to this code, (it used to)
        but I'm still curious.
        *)

        (* compute [s]n . (s o s') *)
	and composeNth (s, n, s') =
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val s'' = subst_compose (s, s') (* GEN END TAG OUTSIDE LET *)
	    in
		case substNth (s,n) of 
		    srVar n' => VarOptDot(SOME n', s'')
		  | srTerm (t,a) => TermDot(t, a, s'')
		  | srEVar (ev,sl) => EVarDot(ev, sl, s'')
	    end
	(* val subst_compose : subst * subst -> subst *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subst_compose (Id, s) = s (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (s, Id) = s (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (s, Shift(_,0)) = s (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (Shift(_,0), s) = s (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (s, Compose []) = s (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (Compose [], s) = s (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (s, Compose (h::tl)) =  subst_compose(subst_compose(s,h), Compose tl) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (Compose (h::tl), s) = subst_compose(h, subst_compose(Compose tl, s)) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (ZeroDotShift s, Shift (0, m)) = subst_compose (subst_compose (Shift (0,1), s), Shift (0, m-1)) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (TermDot (_,_,s), Shift (0, m)) = subst_compose (s, Shift (0, m-1)) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (EVarDot (_,_,s), Shift (0, m)) = subst_compose (s, Shift (0, m-1)) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (VarOptDot (_,s), Shift (0, m)) = subst_compose (s, Shift (0, m-1)) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (Shift(0,m), Shift (0, m')) = Shift (0,m+m') (* GEN END CASE BRANCH *)
          (* ZeroDotShift (Shift (n-1,m)) = Shift(n,m) but the former is 'smaller' *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (Shift(n,m'), t as Shift (0, m)) = subst_compose (ZeroDotShift (Shift (n-1,m')), t) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (s, Shift (n, m)) = subst_compose (s, ZeroDotShift (Shift (n-1,m))) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (s, ZeroDotShift s') = 
	    composeNth (s, 0, subst_compose (Shift (0, 1), s')) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (s, TermDot (t,a,s')) = TermDot (subst_term s t, 
							   subst_tp s a,
							   subst_compose(s,  s')) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subst_compose (s, EVarDot (ev,sl,s')) = EVarDot (ev,s::sl,subst_compose(s,s')) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subst_compose (s, VarOptDot (no, s')) = (case no of
							NONE => VarOptDot(NONE, subst_compose(s,s'))
						      | SOME n => composeNth(s, n, s')) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
        (* shift_[...] n t
        shifts all deBruijn indices in the object t by one, as long
        as they refer to positions in the current context 
        greater than or equal to n. *)
	and shift t = shift_term 0 t
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) shift_nterm n (Lam t) = Lam(shift_term (n+1) t) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) shift_nterm n (NRoot(h,sp)) = NRoot(h, shift_spine n sp) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) shift_aterm n (ARoot(Const n',sp)) = ARoot(Const n', shift_spine n sp) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) shift_aterm n (ERoot(ev,sl)) = ERoot(ev,subst_compose(Shift (n, 1), sl)) (* GEN END CASE BRANCH *) 
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) shift_aterm n (ARoot(Var n',sp)) = 
	    let 
		val sp' = shift_spine n sp
	    in 
		if n' >= n 
		then ARoot(Var (n' + 1), sp')
		else ARoot(Var n', sp')
	    end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) shift_spinelt n (Elt(ATerm t)) = Elt(ATerm(shift_aterm n t)) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) shift_spinelt n (Elt(NTerm t)) = Elt(NTerm(shift_nterm n t)) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) shift_spinelt n (AElt t) = AElt(shift_aterm n t) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) shift_spinelt n (Ascribe(t,a)) = Ascribe(shift_nterm n t, shift_tp n a) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) shift_spinelt n Omit = Omit (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and shift_spine n = map (shift_spinelt n)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) shift_tp n (TPi(m,a,b)) = TPi(m,shift_tp n a, shift_tp (n+1) b) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) shift_tp n (TRoot(h,sp)) = TRoot(h, shift_spine n sp) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) shift_term n (NTerm t) = NTerm(shift_nterm n t) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) shift_term n (ATerm t) = ATerm(shift_aterm n t) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and substs_comp sl = foldr subst_compose Id sl

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) elt_eroot_elim (AElt(t)) = eroot_elim_plus t (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) elt_eroot_elim (Elt(ATerm(t))) = Elt(eroot_elim t) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) elt_eroot_elim x = x (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) ntm_eroot_elim (Lam(ATerm(t))) = Lam(eroot_elim t) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) ntm_eroot_elim x = x (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)



	fun ctxLookup (G, n) = subst_tp (Shift (0, n + 1)) (List.nth (G, n))

	fun typeOf (tclass a) = a
	fun kindOf (kclass k) = k

	(* GEN BEGIN TAG OUTSIDE LET *) val sum = foldl op+ 0 (* GEN END TAG OUTSIDE LET *)
	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) size_term (NTerm (Lam t)) = 1 + (size_term t) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) size_term (NTerm (NRoot (_, s))) = 1 + size_spine s (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) size_term (ATerm (ARoot (_, s))) = 1 + size_spine s (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) size_term (ATerm (ERoot _)) = 1 (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and size_spine s = sum (map size_spinelt s)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) size_spinelt (Elt t) = size_term t (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) size_spinelt (AElt t) = size_term (ATerm t) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) size_spinelt (Ascribe (t, a)) = size_term (NTerm t) + size_tp a (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) size_spinelt Omit = 0 (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) size_tp (TRoot (_, s)) = 1 + size_spine s (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) size_tp (TPi(_,a,b)) = 1 + size_tp a + size_tp b (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) size_knd (Type) = 1 (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) size_knd (KPi(_,a,b)) = 1 + size_tp a + size_knd b (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

     (* convert a kind to a context of all the pi-bound variables in it *) 
	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) explodeKind (Type) = [] (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) explodeKind (KPi(_,a,k)) = (explodeKind k) @ [a] (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
 
end