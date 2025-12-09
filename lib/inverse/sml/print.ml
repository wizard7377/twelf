
  (* -------------------------------------------------------------------------- *)
  (*  Printing                                                                  *)
  (* -------------------------------------------------------------------------- *)

  local   
    nonfix $ % & %%
    let rec op$ x = Layout.str x
    let rec op% x = Layout.mayAlign x
    let rec op%% x = Layout.align x
    let rec op& x = Layout.seq x
    let rec paren x = &[$"(",x,$")"]
    let rec bracket x = &[$"[",x,$"]"]
    let rec squiggle x = &[$"{",x,$"}"]
    let rec indent x = Layout.indent x
    let rec uni_to_layout = function Type -> $"type"
      | Kind -> $"kind"

    let rec const_to_string sgn c = name(Sig.lookup sgn c)

    let rec spine_to_list = function Nil -> []
      | (App(E,S)) -> E::spine_to_list S

    let rec head_to_layout = function sgn (Const c) -> $(const_to_string sgn c)
      | sgn (BVar n) -> $(Int.toString n)

    let rec needs_parens_in_arg_pos = function (Uni _) -> false 
      | (Root(_,Nil)) -> false
      | _ -> true

    let rec needs_sparens_in_arg_pos = function Nil -> false 
      | (App(E,Nil)) -> needs_parens_in_arg_pos E
      | _ -> true

    let rec maybe_paren E l = if needs_parens_in_arg_pos E then paren l else l

    let rec maybe_sparen S l = if needs_sparens_in_arg_pos S then paren l else l

    let rec spine_to_layout sgn S = %%(map (exp_to_layout sgn) (spine_to_list S))
        
    and exp_to_layout sgn (Uni lev) = uni_to_layout lev
      | exp_to_layout sgn (Pi pi) = 
        &[$"PI ",%%[(&[maybe_paren (#arg pi) (exp_to_layout sgn (#arg pi)),$". "]),exp_to_layout sgn (#body pi)]]
      | exp_to_layout sgn (Lam lam) = &[$"LAM. ",exp_to_layout sgn (#body lam)]
      | exp_to_layout sgn (Root(H,Nil)) = head_to_layout sgn H
      | exp_to_layout sgn (Root(H,S)) = &[head_to_layout sgn H,$" ^ ",maybe_sparen S (spine_to_layout sgn S)]

    type subelem = SubShift of int | SubExp of exp

    let rec sub_to_list = function (sub as Shift n) -> [SubShift n]
      | (Dot(M,sub)) -> SubExp M::sub_to_list sub
      | (Comp(s1,s2)) -> sub_to_list s1 @ sub_to_list s2

    let rec sub_to_layout sgn sub = 
        let
          let sub' = sub_to_list sub 
          let rec mapfn = function (SubShift n) -> $("^" ^ Int.toString n)
            | (SubExp exp) -> exp_to_layout sgn exp
          let sub'' = map mapfn sub'
        in
          Layout.list sub''
        end        

  in    
    let rec exp_to_string sgn exp = Layout.tostring (exp_to_layout sgn exp) 
    let rec spine_to_string sgn sp = Layout.tostring (spine_to_layout sgn sp) 
    let rec sub_to_string sgn sub = Layout.tostring (sub_to_layout sgn sub) 
    let rec print_exp sgn exp = print ("\n" ^ exp_to_string sgn exp ^ "\n")
    let rec print_spine sgn sp = print ("\n" ^ spine_to_string sgn sp ^ "\n")
    let rec print_sub sgn sub = print ("\n" ^ sub_to_string sgn sub ^ "\n")
  end
