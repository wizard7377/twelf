structure Strict =
struct

    open Syntax
    exception EtaContract

    (* val eta_contract_var : spineelt -> int
      if the spine element given is an ordinary spine element (i.e. an Elt)
      that is an eta-expansion of the deBruijn index n,
      then returns n. Otherwise raises EtaContract.
    *)
    fun (* GEN BEGIN FUN FIRST *) eta_contract_var (Elt t) = eta_contract_var' 0 t (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) eta_contract_var _ = raise EtaContract (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) eta_contract_var' n (ATerm(ARoot(Var n', s))) = 
    	let
    	    (* GEN BEGIN TAG OUTSIDE LET *) val s' = map eta_contract_var s (* GEN END TAG OUTSIDE LET *)
    	    fun (* GEN BEGIN FUN FIRST *) decreasing_list 0 [] = true (* GEN END FUN FIRST *)
    	      | (* GEN BEGIN FUN BRANCH *) decreasing_list n (h::tl) = (n - 1 = h) andalso decreasing_list (n-1) tl (* GEN END FUN BRANCH *)
    	      | (* GEN BEGIN FUN BRANCH *) decreasing_list _ _ = false (* GEN END FUN BRANCH *)
    	in
    	    if decreasing_list n s' then n' - n else raise EtaContract
    	end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) eta_contract_var' n (NTerm(Lam t)) = eta_contract_var' (n+1) t (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) eta_contract_var' _ _ = raise EtaContract (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) pattern_spine' (D, []) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) pattern_spine' (D, n::s) = let fun isn x = (x = n)
      				      fun hasn s = List.exists isn s
      				  in
      				      hasn D andalso 
      				      not (hasn s) andalso
      				      pattern_spine' (D, s) 
      				  end (* GEN END FUN BRANCH *)
    fun pattern_spine (D, s) = 
    	((pattern_spine' (D, map eta_contract_var s))
    	 handle EtaContract => false)


    fun (* GEN BEGIN FUN FIRST *) spine_occ n (D, nil) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) spine_occ n (D, (Elt t)::s) = term_occ n (D, t) orelse
      				      spine_occ n (D, s) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) spine_occ n (D, (AElt t)::s) = aterm_occ n (D, t) orelse
      				       spine_occ n (D, s) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) spine_occ n (D, (Ascribe (t,a))::s) = nterm_occ n (D, t) orelse
      					      type_occ n (D, a) orelse
      					      spine_occ n (D, s) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) spine_occ n (D, Omit::s) = false (* GEN END FUN BRANCH *) (* Omit invalidates all strict
					    occurrences to the right *)

    and (* GEN BEGIN FUN FIRST *) term_occ n (D, NTerm t) = nterm_occ n (D, t) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) term_occ n (D, ATerm t) = aterm_occ n (D, t) (* GEN END FUN BRANCH *)

    (* PERF: suspend these context shifts, do them at the end *)
    and (* GEN BEGIN FUN FIRST *) nterm_occ n (D, Lam t) = term_occ (n+1) (0 :: (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => x+1 (* GEN END FUNCTION EXPRESSION *)) D), t) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nterm_occ n (D, NRoot (h,s)) = root_occ n (D, h, s) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) aterm_occ n (D, ARoot (h,s)) = root_occ n (D, h, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) aterm_occ n (D, ERoot _) = false (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) root_occ n (D, Var n', s) = if n = n' (* n = n' precludes n in D, right? *)
    				    then pattern_spine (D, s)
    				    else List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => x = n' (* GEN END FUNCTION EXPRESSION *)) D andalso
     					 spine_occ  n (D, s) (* GEN END FUN FIRST *) 

      | (* GEN BEGIN FUN BRANCH *) root_occ n (D, Const n', s) = spine_occ n (D, s) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) type_occ n (D, TRoot (_,s)) = spine_occ n (D, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) type_occ n (D, TPi (_, a, b)) = type_occ n (D, a) orelse
          (* PERF: suspend these context shifts, do them at the end *)
      					type_occ (n+1) (0 :: (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => x+1 (* GEN END FUNCTION EXPRESSION *)) D), b) (* GEN END FUN BRANCH *)

    (* toplevel strictness judgments *)
    fun (* GEN BEGIN FUN FIRST *) check_strict_type' n p (TRoot(n', s)) = if p then false else spine_occ n ([], s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) check_strict_type' n p (TPi(PLUS,a,b)) = type_occ n ([],a) orelse
      					       check_strict_type' (n+1) p b (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) check_strict_type' n p (TPi(_,a,b)) = check_strict_type' (n+1) p b (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) check_strict_kind' n Type = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) check_strict_kind' n (KPi(PLUS,a,k)) = type_occ n ([],a) orelse
      					       check_strict_kind' (n+1) k (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) check_strict_kind' n (KPi(_,a,k)) = check_strict_kind' (n+1) k (* GEN END FUN BRANCH *)


(* p is whether we should imagine we are checking a c+ (rather than c-) constant *)
    fun check_strict_type p b = check_strict_type' 0 p b
    fun check_strict_kind k = check_strict_kind' 0 k
end