structure Convert =
struct
        open Syntax

        exception Convert of string
	exception NotFound of string

	(* GEN BEGIN TAG INSIDE LET *) val sigma : string list ref = ref [] (* GEN END TAG INSIDE LET *)
	(* GEN BEGIN TAG INSIDE LET *) val sigmat : class list ref = ref [] (* GEN END TAG INSIDE LET *)
	(* GEN BEGIN TAG INSIDE LET *) val sigmap : bool list ref = ref [] (* GEN END TAG INSIDE LET *)

	(* GEN BEGIN TAG INSIDE LET *) fun clear () = let in
			   sigma := [];
			   sigmat := [];
			   sigmap := []
		       end (* GEN END TAG INSIDE LET *)

	(* GEN BEGIN TAG INSIDE LET *) fun findn [] (v : string) = raise NotFound v
	  | findn (v::tl) v' = if v = v' then 0 else 1 + findn tl v' (* GEN END TAG INSIDE LET *)
	(* GEN BEGIN TAG INSIDE LET *) fun findid ctx v = (Var(findn ctx v) handle NotFound _ =>
							Const(findn (!sigma) v)) (* GEN END TAG INSIDE LET *)
	(* GEN BEGIN TAG INSIDE LET *) fun modeconvert Parse.mMINUS = MINUS
	  | modeconvert Parse.mPLUS = PLUS
	  | modeconvert Parse.mOMIT = OMIT (* GEN END TAG INSIDE LET *)

	(* GEN BEGIN TAG INSIDE LET *) fun modesofclass (kclass(Type)) = []
	  | modesofclass (kclass(KPi(m,_,k))) = m :: modesofclass(kclass k)
	  | modesofclass (tclass(TRoot _)) = []
	  | modesofclass (tclass(TPi(m,_,a))) = m :: modesofclass(tclass a) (* GEN END TAG INSIDE LET *)

(* given a context and an external expression, returns the internal 'spine form' as a 4-tuple
   (h, mopt, p, s)
   where h is the head (Var n or Const n)
         mopt is a list of modes for the arguments (MINUS, PLUS, OMIT)
         p is true iff the head is a synthesizing constant or a variable
         s is the list of arugments
*)
	(* GEN BEGIN TAG INSIDE LET *) fun spine_form (G, Parse.Id s) = 
	    (case findid G s of
		 Var n => (Var n, NONE, true, [])
	       | Const n => (Const n,
			     SOME (modesofclass (List.nth (!sigmat, n))),
			     List.nth (!sigmap, n),
			     []))
	  | spine_form (G, Parse.App (t, u)) = let val (h, mopt, p, s) = spine_form (G, t) in (h, mopt, p, s @ [u]) end
	  | spine_form (G, Parse.Lam _) = raise Convert "illegal redex" 
	  | spine_form (G, _) = raise Convert "level mismatch" (* GEN END TAG INSIDE LET *) 

(* similar to spine_form for a type family applied to a list of arguments *)
	(* GEN BEGIN TAG INSIDE LET *) fun type_spine_form (G, Parse.Id s) = 
	    let 
		val n = findn (!sigma) s
	    in
	        (n, modesofclass (List.nth (!sigmat, n)), [])
	    end
	  | type_spine_form (G, Parse.App (t, u)) = let val (n, m, s) = type_spine_form (G, t)
					       in (n, m, s @ [u]) end
	  | type_spine_form (G, _) = raise Convert "level mismatch" (* GEN END TAG INSIDE LET *) 

	(* GEN BEGIN TAG INSIDE LET *) fun safezip (l1, l2) = if length l1 = length l2 
			       then ListPair.zip (l1,l2)
			       else raise Convert "wrong spine length" (* GEN END TAG INSIDE LET *)

(* given a context and an external expression and a mode, return a spine element or raise an exception*)
	(* GEN BEGIN TAG INSIDE LET *) fun eltconvert G (t, MINUS) = Elt (convert (G, t))
	  | eltconvert G (Parse.Ascribe(t, a), PLUS) = Ascribe(nconvert (G, t), typeconvert (G, a))
	  | eltconvert G (t, PLUS) = AElt (aconvert(G, t))
	  | eltconvert G (Parse.Omit, OMIT) = Omit
	  | eltconvert G (_, OMIT) = raise Convert "found term expected to be omitted"
		
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
	and convert (G, Parse.Lam ((v,_), t)) = NTerm(Lam(convert(v::G, t)))
	  | convert (G, t) = 
	    let
		val (h, mopt, p, s) = spine_form (G, t)
		val s' = map (eltconvert G) (case mopt of
						 NONE => map (fn elt => (elt, MINUS)) s
					       | SOME m =>  (safezip (s, m)))
	    in
		if p 
		then ATerm(ARoot(h, s'))
		else NTerm(NRoot(h, s'))
	    end
(* given a context and an external expression, return a type or raise an exception *)
	and typeconvert (G, Parse.Pi (m, (v,SOME t),t')) = 
	    let
		val ct = typeconvert(G, t)
		val ct' = typeconvert(v::G, t')
	    in
		TPi(modeconvert m, ct, ct')
	    end
	  | typeconvert (G, Parse.Pi (m, (_,NONE),_)) = raise Convert "can't handle implicit pi"
	  | typeconvert (G, Parse.Arrow (t, t')) = 
	    let
		val ct = typeconvert(G, t)
		val ct' = typeconvert(""::G, t')
	    in
		TPi(MINUS, ct, ct')
	    end
	  | typeconvert (G, Parse.PlusArrow (t, t')) = 
	    let
		val ct = typeconvert(G, t)
		val ct' = typeconvert(""::G, t')
	    in
		TPi(PLUS, ct, ct')
	    end
	  | typeconvert (G, a) = 
	    let 
		val (n, m, s) = type_spine_form (G, a)
		val s' = map (eltconvert G) (safezip (s,m))
	    in
		TRoot(n, s')
	    end
(* given a context and an external expression, return a kind or raise an exception *)
	and kindconvert (G, Parse.Pi (m, (v,SOME t),t')) = 
	    let
		val ct = typeconvert(G, t)
		val ct' = kindconvert(v::G, t')
	    in
		KPi(modeconvert m, ct, ct')
	    end
	  | kindconvert (G, Parse.Arrow (t, t')) = 
	    let
		val ct = typeconvert(G, t)
		val ct' = kindconvert(""::G, t')
	    in
		KPi(MINUS, ct, ct')
	    end
	  | kindconvert (G, Parse.PlusArrow (t, t')) = 
	    let
		val ct = typeconvert(G, t)
		val ct' = kindconvert(""::G, t')
	    in
		KPi(PLUS, ct, ct')
	    end
	  | kindconvert (G, Parse.Pi (m, (_,NONE),_)) = raise Convert "can't handle implicit pi"
	  | kindconvert (G, Parse.Type) = Type
	  | kindconvert _ = raise Convert "level mismatch" (* GEN END TAG INSIDE LET *)

end
