structure Convert =
struct
        open Syntax

        exception Convert of string
	exception NotFound of string

	(* GEN BEGIN TAG OUTSIDE LET *) val sigma : string list ref = ref [] (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val sigmat : class list ref = ref [] (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val sigmap : bool list ref = ref [] (* GEN END TAG OUTSIDE LET *)

	fun clear () = let in
			   sigma := [];
			   sigmat := [];
			   sigmap := []
		       end

	fun (* GEN BEGIN FUN FIRST *) findn [] (v : string) = raise NotFound v (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) findn (v::tl) v' = if v = v' then 0 else 1 + findn tl v' (* GEN END FUN BRANCH *)
	fun findid ctx v = (Var(findn ctx v) handle NotFound _ =>
							Const(findn (!sigma) v))
	fun (* GEN BEGIN FUN FIRST *) modeconvert Parse.mMINUS = MINUS (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) modeconvert Parse.mPLUS = PLUS (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) modeconvert Parse.mOMIT = OMIT (* GEN END FUN BRANCH *)

	fun (* GEN BEGIN FUN FIRST *) modesofclass (kclass(Type)) = [] (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) modesofclass (kclass(KPi(m,_,k))) = m :: modesofclass(kclass k) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) modesofclass (tclass(TRoot _)) = [] (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) modesofclass (tclass(TPi(m,_,a))) = m :: modesofclass(tclass a) (* GEN END FUN BRANCH *)

(* given a context and an external expression, returns the internal 'spine form' as a 4-tuple
   (h, mopt, p, s)
   where h is the head (Var n or Const n)
         mopt is a list of modes for the arguments (MINUS, PLUS, OMIT)
         p is true iff the head is a synthesizing constant or a variable
         s is the list of arugments
*)
	fun (* GEN BEGIN FUN FIRST *) spine_form (G, Parse.Id s) = 
	    (case findid G s of
		 Var n => (Var n, NONE, true, [])
	       | Const n => (Const n,
			     SOME (modesofclass (List.nth (!sigmat, n))),
			     List.nth (!sigmap, n),
			     [])) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) spine_form (G, Parse.App (t, u)) = let (* GEN BEGIN TAG OUTSIDE LET *) val (h, mopt, p, s) = spine_form (G, t) (* GEN END TAG OUTSIDE LET *) in (h, mopt, p, s @ [u]) end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) spine_form (G, Parse.Lam _) = raise Convert "illegal redex" (* GEN END FUN BRANCH *) 
	  | (* GEN BEGIN FUN BRANCH *) spine_form (G, _) = raise Convert "level mismatch" (* GEN END FUN BRANCH *) 

(* similar to spine_form for a type family applied to a list of arguments *)
	fun (* GEN BEGIN FUN FIRST *) type_spine_form (G, Parse.Id s) = 
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val n = findn (!sigma) s (* GEN END TAG OUTSIDE LET *)
	    in
	        (n, modesofclass (List.nth (!sigmat, n)), [])
	    end (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) type_spine_form (G, Parse.App (t, u)) = let (* GEN BEGIN TAG OUTSIDE LET *) val (n, m, s) = type_spine_form (G, t) (* GEN END TAG OUTSIDE LET *)
					       in (n, m, s @ [u]) end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) type_spine_form (G, _) = raise Convert "level mismatch" (* GEN END FUN BRANCH *) 

	fun safezip (l1, l2) = if length l1 = length l2 
			       then ListPair.zip (l1,l2)
			       else raise Convert "wrong spine length"

(* given a context and an external expression and a mode, return a spine element or raise an exception*)
	fun (* GEN BEGIN FUN FIRST *) eltconvert G (t, MINUS) = Elt (convert (G, t)) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) eltconvert G (Parse.Ascribe(t, a), PLUS) = Ascribe(nconvert (G, t), typeconvert (G, a)) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) eltconvert G (t, PLUS) = AElt (aconvert(G, t)) (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) eltconvert G (Parse.Omit, OMIT) = Omit (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) eltconvert G (_, OMIT) = raise Convert "found term expected to be omitted" (* GEN END FUN BRANCH *)
		
(* given a context and an external expression, return an atomic term or raise an exception*)
	and aconvert (G, t) = 
	    (case convert (G, t) of
		 ATerm t' => t'
	       | NTerm _ => raise Convert "required atomic, found normal")

(* given a context and an external expression, return a normal term or raise an exception*)
	and nconvert (G, t) = 
	    (case convert (G, t) of
		 NTerm t' => t'
	       | ATerm _ => raise Convert "required normal, found atomic")

(* given a context and an external expression, return a term or raise an exception *)
	and (* GEN BEGIN FUN FIRST *) convert (G, Parse.Lam ((v,_), t)) = NTerm(Lam(convert(v::G, t))) (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) convert (G, t) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val (h, mopt, p, s) = spine_form (G, t) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val s' = map (eltconvert G) (case mopt of
						 NONE => map ((* GEN BEGIN FUNCTION EXPRESSION *) fn elt => (elt, MINUS) (* GEN END FUNCTION EXPRESSION *)) s
					       | SOME m =>  (safezip (s, m))) (* GEN END TAG OUTSIDE LET *)
	    in
		if p 
		then ATerm(ARoot(h, s'))
		else NTerm(NRoot(h, s'))
	    end (* GEN END FUN BRANCH *)
(* given a context and an external expression, return a type or raise an exception *)
	and (* GEN BEGIN FUN FIRST *) typeconvert (G, Parse.Pi (m, (v,SOME t),t')) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val ct = typeconvert(G, t) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val ct' = typeconvert(v::G, t') (* GEN END TAG OUTSIDE LET *)
	    in
		TPi(modeconvert m, ct, ct')
	    end (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) typeconvert (G, Parse.Pi (m, (_,NONE),_)) = raise Convert "can't handle implicit pi" (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) typeconvert (G, Parse.Arrow (t, t')) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val ct = typeconvert(G, t) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val ct' = typeconvert(""::G, t') (* GEN END TAG OUTSIDE LET *)
	    in
		TPi(MINUS, ct, ct')
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) typeconvert (G, Parse.PlusArrow (t, t')) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val ct = typeconvert(G, t) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val ct' = typeconvert(""::G, t') (* GEN END TAG OUTSIDE LET *)
	    in
		TPi(PLUS, ct, ct')
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) typeconvert (G, a) = 
	    let 
		(* GEN BEGIN TAG OUTSIDE LET *) val (n, m, s) = type_spine_form (G, a) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val s' = map (eltconvert G) (safezip (s,m)) (* GEN END TAG OUTSIDE LET *)
	    in
		TRoot(n, s')
	    end (* GEN END FUN BRANCH *)
(* given a context and an external expression, return a kind or raise an exception *)
	and (* GEN BEGIN FUN FIRST *) kindconvert (G, Parse.Pi (m, (v,SOME t),t')) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val ct = typeconvert(G, t) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val ct' = kindconvert(v::G, t') (* GEN END TAG OUTSIDE LET *)
	    in
		KPi(modeconvert m, ct, ct')
	    end (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) kindconvert (G, Parse.Arrow (t, t')) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val ct = typeconvert(G, t) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val ct' = kindconvert(""::G, t') (* GEN END TAG OUTSIDE LET *)
	    in
		KPi(MINUS, ct, ct')
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) kindconvert (G, Parse.PlusArrow (t, t')) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val ct = typeconvert(G, t) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val ct' = kindconvert(""::G, t') (* GEN END TAG OUTSIDE LET *)
	    in
		KPi(PLUS, ct, ct')
	    end (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) kindconvert (G, Parse.Pi (m, (_,NONE),_)) = raise Convert "can't handle implicit pi" (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) kindconvert (G, Parse.Type) = Type (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) kindconvert _ = raise Convert "level mismatch" (* GEN END FUN BRANCH *)

end
