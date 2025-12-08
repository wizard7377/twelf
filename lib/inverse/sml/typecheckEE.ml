
(TypecheckEE : TYPECHEC)K =
struct 

  module L = Lib
  module S = Syntax
  module Sig = S.Signat
  module C = Context
  module D = Debug

  open S

  type ret = RetExp of exp | RetVar of int

  (** check a term (type)  against a type (kind) *)
  let rec check_exp = function (ctx,Uni Type,Uni Kind) -> ()
    | (ctx,Lam {body -> M,...}, Pi {var,arg=U,body=V,...}) =
      check_exp (C.push (ctx, (var, U)), M, V)
    | (ctx,Root(Const con,S), V) -> 
      let 
        (* pull some common code out of the following case *)
        fun foc exp =
           let
             let U = focus (ctx,S,exp)
           in
             if equiv_exp(U,V) then ()
             else raise Fail "check_exp: exps not equivalent"
           end
      in
        case Sig.lookup con of
           Decl decl => foc (#exp decl) 
         | Def def => foc (#exp def)
         (* why does this fail?*)
         | Abbrev abbrev => raise Fail "check_exp: abbrev"
      end
    | (ctx, Root(BVar i,S), V) -> 
      (case C.lookup (ctx, i-1) (* DeBruijn indices start at 1 *) of
         SOME (_,A) =>
         let
           let U = focus (ctx,S, apply_exp (Shift i, A)) 
         in
           if equiv_exp (U,V) then ()
           else raise Fail_exp2("check_exp: Root,BVar",U,V)
         end
       | NONE => raise Fail ("focus: var out of bounds"))
    | (ctx, Pi {var,arg -> A1,body=A2,...}, uni as Uni _) = 
      (check_exp (ctx, A1, expType);
       check_exp (C.push (ctx, (var, A1)), A2, uni))
    | _ -> raise Fail "check: bad case"

  and focus (ctx, Nil, ty as Uni Type) = ty
    | focus (ctx, Nil, hd as Root (Const _,_)) = hd
    | focus (ctx ,App(M,S), Pi {arg=A1,body=A2,...}) =
      (check_exp (ctx, M, A1);
       focus (ctx, S, apply_exp (Dot(M,id_sub), A2)))
    | focus (_,S,E) = raise Fail_spine_exp("focus: bad case",S,E)

  and check E1 E2 = (Timers.time Timers.checking check_exp) (C.empty,E1,E2)
 
  (* -------------------------------------------------------------------------- *)
  (*  Substitutions                                                             *)
  (* -------------------------------------------------------------------------- *)

  and apply_exp (_, uni as Uni _) = uni
    | apply_exp (sub, Pi {var,arg=U,depend,body=V}) =
      Pi {var = var,
          arg = apply_exp(sub, U),
          depend = depend,
          body = apply_exp (push_sub sub, V)}
    | apply_exp (sub, Lam {var,body=U}) =
      Lam {var=var,
           body=apply_exp (push_sub sub, U)}
    | apply_exp (sub, exp as Root(H,S)) =
      let
        let S' = apply_spine (sub, S)
      in
        case H of
          Const _ => Root(H,S')
        | BVar i =>
          case apply_var (sub, i) of
            RetVar j => Root(BVar j,S')
          | RetExp M => reduce (M, S')
      end

  and apply_spine (_, Nil) = Nil
    | apply_spine (sub, App(M,S)) = App(apply_exp (sub, M),apply_spine (sub, S))

  and apply_var (Dot(M,sub), i) =
      if i = 1 
      then 
        case M of 
          Root(BVar j,Nil) => RetVar j
        | _ => RetExp M
      else apply_var (sub, i-1)
    | apply_var (Shift n, i) = RetVar (i+n)

  and compose (Dot(M,sigma),sigma') = Dot(apply_exp (sigma', M),compose(sigma,sigma'))
    | compose (Shift n,Shift m) = Shift (n + m)
    | compose (Shift 0,sigma) = sigma
    | compose (Shift n,Dot(M,sigma)) = compose (Shift (n-1),sigma)

  and push_sub s = Dot(one,compose(s,shift))

  (* -------------------------------------------------------------------------- *)
  (*  Beta                                                                      *)
  (* -------------------------------------------------------------------------- *)

  and reduce (exp as Root(_,_), Nil) = exp
    | reduce (Lam {body=M,...}, App(M',S)) =
      reduce (apply_exp (Dot(M',id_sub), M), S)
    | reduce (E, S) = raise Fail_exp_spine ("reduce: bad case: head: ",E,S)

  (* -------------------------------------------------------------------------- *)
  (*  Equivalence wrt Definitions                                               *)
  (* -------------------------------------------------------------------------- *)

  and equiv_exp (Uni u1, Uni u2) = u1 = u2
    | equiv_exp (Pi {arg=U1,body=V1,...}, Pi {arg=U2,body=V2,...}) =
      equiv_exp (U1, U2) andalso equiv_exp (V1, V2)
    | equiv_exp (Lam {body=U,...}, Lam {body=U',...}) =
      equiv_exp (U, U')
    | equiv_exp (Root(BVar i,S1), Root(BVar i',S2)) =
      i = i' andalso equiv_spine (S1, S2)
    | equiv_exp (exp as Root(Const c,S), exp' as Root(Const c',S')) =
      if c = c' then equiv_spine (S, S') else
      (case (Sig.lookup c,Sig.lookup c') of
         (Decl decl,Def def) =>
         if #root def <> #id decl then false
         else equiv_exp (exp, reduce (#def def, S'))
       | (Def def,Decl decl) =>
         if #root def <> #id decl then false
         else equiv_exp (reduce (#def def, S), exp')
       | (Abbrev {def,...},_) => equiv_exp (reduce (def, S), exp')
       | (_,Abbrev {def,...}) => equiv_exp (exp, reduce (def, S'))
       | (Def {def=def,height=h,root=rc,...},
          Def {def=def',height=h',root=rc',...}) =>
         if rc <> rc' then false else
         if h = h' then equiv_exp (reduce (def, S),reduce (def', S'))
         else if h > h' then equiv_exp (reduce (def, S), exp')
         else equiv_exp (exp, reduce (def', S'))
       | (_,_) => raise Fail "equiv_exp: bad case")
    | equiv_exp _ = false

  and equiv_spine (S.Nil, Nil) = true
    | equiv_spine (S.App(E,S), S.App(E',S')) =
      equiv_exp (E ,E') andalso equiv_spine (S, S')
    | equiv_spine _ = false

  (* -------------------------------------------------------------------------- *)
  (*  Signatures                                                                *)
  (* -------------------------------------------------------------------------- *)

  let rec check_dec = function (c,Decl {id,name,exp,uni}) -> 
      let
        let uni' = Uni uni
        let exp' = eta_expand(exp,uni')
      in
        check exp' uni';
        Sig.insert (id,Decl {id=id,name=name,exp=exp',uni=uni})
      end
    | (c,Def {id,name,exp,def,height,root,uni}) -> 
      let
        let uni' = Uni uni
        let exp' = eta_expand(exp,uni')
        let def' = eta_expand(def,exp')
      in
        check exp' uni';
        check def' exp';
        Sig.insert (id,Def {id=id,name=name,exp=exp',def=def',
                            height=height,root=root,uni=uni})
      end
    | (c,Abbrev {id,name,exp,def,uni}) -> 
      let
        let uni' = Uni uni
(*         let exp' = eta_expand(exp,uni') *)
(*         let def' = eta_expand(def,exp') *)
        let exp' = exp
        let def' = def
      in
        check exp' uni';
        check def' exp';
        Sig.insert (id,Abbrev{id=id,name=name,exp=exp',
                              def=def',uni=uni})
      end

  fun check_signat' decs = 
      List.app (fn (decl as (c,dec)) => 
                   ((* L.printl ("checking: " ^ name dec ); *)
                    check_dec decl)) decs

  fun check_signat decs = (Timers.time Timers.checking check_signat') decs

  fun check_signat_clear decs = 
      (Sig.reset();
       check_signat decs)

end

