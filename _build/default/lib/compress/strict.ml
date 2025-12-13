structure Strict =
struct

    open Syntax
    exception EtaContract

    (* val eta_contract_var : spineelt -> int
      if the spine element given is an ordinary spine element (i.e. an Elt)
      that is an eta-expansion of the deBruijn index n,
      then returns n. Otherwise raises EtaContract.
    *)
    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) eta_contract_var (Elt t) = eta_contract_var' 0 t (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) eta_contract_var _ = raise EtaContract (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) eta_contract_var' n (ATerm(ARoot(Var n', s))) = 
    	let
    	    val s' = map eta_contract_var s
    	    fun decreasing_list 0 [] = true
    	      | decreasing_list n (h::tl) = (n - 1 = h) andalso decreasing_list (n-1) tl
    	      | decreasing_list _ _ = false
    	in
    	    if decreasing_list n s' then n' - n else raise EtaContract
    	end (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) eta_contract_var' n (NTerm(Lam t)) = eta_contract_var' (n+1) t (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) eta_contract_var' _ _ = raise EtaContract (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) pattern_spine' (D, []) = true (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) pattern_spine' (D, n::s) = let fun isn x = (x = n)
      				      fun hasn s = List.exists isn s
      				  in
      				      hasn D andalso 
      				      not (hasn s) andalso
      				      pattern_spine' (D, s) 
      				  end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    fun pattern_spine (D, s) = 
    	((pattern_spine' (D, map eta_contract_var s))
    	 handle EtaContract => false)


    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) spine_occ n (D, nil) = false (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) spine_occ n (D, (Elt t)::s) = term_occ n (D, t) orelse
      				      spine_occ n (D, s) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) spine_occ n (D, (AElt t)::s) = aterm_occ n (D, t) orelse
      				       spine_occ n (D, s) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) spine_occ n (D, (Ascribe (t,a))::s) = nterm_occ n (D, t) orelse
      					      type_occ n (D, a) orelse
      					      spine_occ n (D, s) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) spine_occ n (D, Omit::s) = false (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *) (* Omit invalidates all strict
					    occurrences to the right *)

    and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) term_occ n (D, NTerm t) = nterm_occ n (D, t) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) term_occ n (D, ATerm t) = aterm_occ n (D, t) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    (* PERF: suspend these context shifts, do them at the end *)
    and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) nterm_occ n (D, Lam t) = term_occ (n+1) (0 :: (map (fn x => x+1) D), t) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) nterm_occ n (D, NRoot (h,s)) = root_occ n (D, h, s) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) aterm_occ n (D, ARoot (h,s)) = root_occ n (D, h, s) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) aterm_occ n (D, ERoot _) = false (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) root_occ n (D, Var n', s) = if n = n' (* n = n' precludes n in D, right? *)
    				    then pattern_spine (D, s)
    				    else List.exists (fn x => x = n') D andalso
     					 spine_occ  n (D, s) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *) 

      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) root_occ n (D, Const n', s) = spine_occ n (D, s) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) type_occ n (D, TRoot (_,s)) = spine_occ n (D, s) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) type_occ n (D, TPi (_, a, b)) = type_occ n (D, a) orelse
          (* PERF: suspend these context shifts, do them at the end *)
      					type_occ (n+1) (0 :: (map (fn x => x+1) D), b) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    (* toplevel strictness judgments *)
    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) check_strict_type' n p (TRoot(n', s)) = if p then false else spine_occ n ([], s) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) check_strict_type' n p (TPi(PLUS,a,b)) = type_occ n ([],a) orelse
      					       check_strict_type' (n+1) p b (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) check_strict_type' n p (TPi(_,a,b)) = check_strict_type' (n+1) p b (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) check_strict_kind' n Type = false (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) check_strict_kind' n (KPi(PLUS,a,k)) = type_occ n ([],a) orelse
      					       check_strict_kind' (n+1) k (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) check_strict_kind' n (KPi(_,a,k)) = check_strict_kind' (n+1) k (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)


(* p is whether we should imagine we are checking a c+ (rather than c-) constant *)
    fun check_strict_type p b = check_strict_type' 0 p b
    fun check_strict_kind k = check_strict_kind' 0 k
end