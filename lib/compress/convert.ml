module Convert =
struct
        open Syntax

        exception Convert of string
	exception NotFound of string

	let sigma : string list ref = ref []
	let sigmat : class_ list ref = ref []
	let sigmap : bool list ref = ref []

	let clear () = begin
			   sigma := [];
			   sigmat := [];
			   sigmap := []
		       end

	let rec findn ctx (v : string) = match ctx with
	    [] -> raise NotFound v
	  | (v'::tl) -> if v' = v then 0 else 1 + findn tl v
	let findid ctx v = try Var(findn ctx v) with NotFound _ ->
							Const(findn (!sigma) v)
	let modeconvert = function
	    Parse.MMINUS -> MINUS
	  | Parse.MPLUS -> PLUS
	  | Parse.MOMIT -> OMIT

	let rec modesofclass = function
	    (Kclass(Type)) -> []
	  | (Kclass(KPi(m,_,k))) -> m :: modesofclass(Kclass k)
	  | (Tclass(TRoot _)) -> []
	  | (Tclass(TPi(m,_,a))) -> m :: modesofclass(Tclass a)

(* given a context and an external expression, returns the internal 'spine form' as a 4-tuple
   (h, mopt, p, s)
   where h is the head (Var n or Const n)
         mopt is a list of modes for the arguments (MINUS, PLUS, OMIT)
         p is true iff the head is a synthesizing constant or a variable
         s is the list of arugments
*)
	let rec spine_form = function
	    (G, Parse.Id s) -> 
	    (match findid G s with
		 Var n -> (Var n, NONE, true, [])
	       | Const n -> (Const n,
			     SOME (modesofclass (List.nth (!sigmat, n))),
			     List.nth (!sigmap, n),
			     []))
	  | (G, Parse.App (t, u)) -> let let (h, mopt, p, s) = spine_form (G, t) in (h, mopt, p, s @ [u]) end
	  | (G, Parse.Lam _) -> raise Convert "illegal redex" 
	  | (G, _) -> raise Convert "level mismatch" 

(* similar to spine_form for a type family applied to a list of arguments *)
	and type_spine_form = function
	    (G, Parse.Id s) -> 
	    let 
		let n = findn (!sigma) s
	    in
	        (n, modesofclass (List.nth (!sigmat, n)), [])
	    end
	  | (G, Parse.App (t, u)) -> let let (n, m, s) = type_spine_form (G, t)
					       in (n, m, s @ [u]) end
	  | (G, _) -> raise Convert "level mismatch" 

	let safezip (l1, l2) = if length l1 = length l2 
			       then ListPair.zip (l1,l2)
			       else raise Convert "wrong spine length"

(* given a context and an external expression and a mode, return a spine element or raise an exception*)
	let rec eltconvert G = function
	    (t, MINUS) -> Elt (convert (G, t))
	  | (Parse.Ascribe(t, a), PLUS) -> Ascribe(nconvert (G, t), typeconvert (G, a))
	  | (t, PLUS) -> AElt (aconvert(G, t))
	  | (Parse.Omit, OMIT) -> Omit
	  | (_, OMIT) -> raise Convert "found term expected to be omitted"
		
(* given a context and an external expression, return an atomic term or raise an exception*)
	and aconvert (G, t) = 
	    (match convert (G, t) with
		 ATerm t' -> t'
	       | NTerm _ -> raise Convert "required atomic, found normal")

(* given a context and an external expression, return a normal term or raise an exception*)
	and nconvert (G, t) = 
	    (match convert (G, t) with
		 NTerm t' -> t'
	       | ATerm _ -> raise Convert "required normal, found atomic")

(* given a context and an external expression, return a term or raise an exception *)
	and convert = function
	    (G, Parse.Lam ((v,_), t)) -> NTerm(Lam(convert(v::G, t)))
	  | (G, t) -> 
	    let
		let (h, mopt, p, s) = spine_form (G, t)
		let s' = map (eltconvert G) (match mopt with
						 NONE -> map (fun elt -> (elt, MINUS)) s
					       | SOME m ->  (safezip (s, m)))
	    in
		if p 
		then ATerm(ARoot(h, s'))
		else NTerm(NRoot(h, s'))
	    end
(* given a context and an external expression, return a type or raise an exception *)
	and typeconvert = function
	    (G, Parse.Pi (m, (v,SOME t),t')) -> 
	    let
		let ct = typeconvert(G, t)
		let ct' = typeconvert(v::G, t')
	    in
		TPi(modeconvert m, ct, ct')
	    end
	  | (G, Parse.Pi (m, (_,NONE),_)) -> raise Convert "can't handle implicit pi"
	  | (G, Parse.Arrow (t, t')) -> 
	    let
		let ct = typeconvert(G, t)
		let ct' = typeconvert(""::G, t')
	    in
		TPi(MINUS, ct, ct')
	    end
	  | (G, Parse.PlusArrow (t, t')) -> 
	    let
		let ct = typeconvert(G, t)
		let ct' = typeconvert(""::G, t')
	    in
		TPi(PLUS, ct, ct')
	    end
	  | (G, a) -> 
	    let 
		let (n, m, s) = type_spine_form (G, a)
		let s' = map (eltconvert G) (safezip (s,m))
	    in
		TRoot(n, s')
	    end
(* given a context and an external expression, return a kind or raise an exception *)
	and kindconvert = function
	    (G, Parse.Pi (m, (v,SOME t),t')) -> 
	    let
		let ct = typeconvert(G, t)
		let ct' = kindconvert(v::G, t')
	    in
		KPi(modeconvert m, ct, ct')
	    end
	  | (G, Parse.Arrow (t, t')) -> 
	    let
		let ct = typeconvert(G, t)
		let ct' = kindconvert(""::G, t')
	    in
		KPi(MINUS, ct, ct')
	    end
	  | (G, Parse.PlusArrow (t, t')) -> 
	    let
		let ct = typeconvert(G, t)
		let ct' = kindconvert(""::G, t')
	    in
		KPi(PLUS, ct, ct')
	    end
	  | (G, Parse.Pi (m, (_,NONE),_)) -> raise Convert "can't handle implicit pi"
	  | (G, Parse.Type) -> Type
	  | _ -> raise Convert "level mismatch"

end
