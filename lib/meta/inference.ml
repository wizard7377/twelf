(* Inference:  Version 1.3*)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Inference (structure MTPGlobal : MTPGLOBAL
                   (*! structure IntSyn : INTSYN !*)
                   (*! structure FunSyn' : FUNSYN !*)
                   (*! sharing FunSyn'.IntSyn = IntSyn !*)
                   structure StateSyn' : STATESYN
                   (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                   structure Abstract : ABSTRACT
                   (*! sharing Abstract.IntSyn = IntSyn !*)
                   structure TypeCheck : TYPECHECK
                   (*! sharing TypeCheck.IntSyn = IntSyn !*)
                   structure FunTypeCheck : FUNTYPECHECK
                   (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                     sharing FunTypeCheck.StateSyn = StateSyn'
                   structure UniqueSearch  : UNIQUESEARCH
                   (*! sharing UniqueSearch.IntSyn = IntSyn !*)
                   (*! sharing UniqueSearch.FunSyn = FunSyn' !*)
                     sharing UniqueSearch.StateSyn = StateSyn'
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = IntSyn !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn !*)
                     )
  : INFERENCE =
struct
  (*! structure FunSyn = FunSyn' !*)
  structure StateSyn = StateSyn'

  exception Error of string

  type operator = (unit -> StateSyn'.state)

  local
    structure S = StateSyn
    structure F = FunSyn
    structure I = IntSyn

    exception Success

    (* createEVars (G, (F, V, s)) = (Xs', (F', V', s'))

       Invariant:
       If   |- G ctx
       and  G0 |- F = {{x1:A1}} .. {{xn::An}} F1 formula
       and  G0 |- V = { x1:A1}  .. {xn:An} V1 : type
       and  G |- s : G0
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G |- s: G'
       and  G0 |- F' = F1 for
       and  G0 |- V' = V1 : type
    *)
    fun (* GEN BEGIN FUN FIRST *) createEVars (G, (I.Pi ((I.Dec (_, V), I.Meta), V'), s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V, s)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X' = Whnf.lowerEVar X (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Xs, FVs') = createEVars (G, (V', I.Dot (I.Exp X, s))) (* GEN END TAG OUTSIDE LET *)
        in
          (X' :: Xs, FVs')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createEVars (G, FVs as (_, s)) = (nil, FVs) (* GEN END FUN BRANCH *)



    (* forward (G, B, (V, F)) = (V', F')  (or none)

       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  G |- V type
       and  G; . |- F : formula
       then G |- V' type
       and  G; . |- F' : formula

    *)
    fun (* GEN BEGIN FUN FIRST *) forward (G, B, V as I.Pi ((_, I.Meta), _)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.doubleCheck
                    then TypeCheck.typeCheck (G, (V, I.Uni I.Type))
                    else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Xs, (V', s')) = createEVars (G, (V, I.id)) (* GEN END TAG OUTSIDE LET *)
        in
          (case  UniqueSearch.searchEx (2, Xs, (* GEN BEGIN FUNCTION EXPRESSION *) fn nil => [(Whnf.normalize (V', s'))]
                                                | _ => raise UniqueSearch.Error "Too many solutions" (* GEN END FUNCTION EXPRESSION *))
             of [VF''] => SOME VF''
    
              | [] => NONE) handle UniqueSearch.Error _ => NONE
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) forward (G, B, V) = NONE (* GEN END FUN BRANCH *)



    (* expand' ((G, B), n) = ((Gnew, Bnew), sc)

       Invariant:
       If   |- G0 ctx    G0 |- B0 tags
       and  |- G ctx     G |- B tags
       and  G prefix of G0 , and B prefix of B0
       and  n + |G| = |G0|
       then sc is a continutation which maps
            |- G' ctx
            and G' |- B' tags
            and G', B' |- w' : G0, B0
            to  |- G'' ctx
            and G'' |- B'' tags
            and G'', B'' extends G, B
       and |- Gnew = G ctx
       and Gnew |- Bnew tags
       where Bnew stems from B where all used lemmas (S.RL) are now tagged with (S.RLdone)
    *)

    fun (* GEN BEGIN FUN FIRST *) expand' ((G0, B0), (I.Null, I.Null), n) =
        ((I.Null, I.Null), (* GEN BEGIN FUNCTION EXPRESSION *) fn ((G', B'), w') => ((G', B'), w') (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) expand' ((G0, B0), (I.Decl (G, D as I.Dec (_, V)), I.Decl (B, T as S.Lemma (S.RL))), n) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((G0', B0'), sc') = expand' ((G0, B0), (G, B), n+1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val s = I.Shift (n+1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Vs = Whnf.normalize (V, s) (* GEN END TAG OUTSIDE LET *)
        in
          case (forward (G0, B0, (Vs)))
            of NONE => ((I.Decl (G0', D), I.Decl (B0', T)), sc')
             | SOME (V') =>
                 ((I.Decl (G0', D), I.Decl (B0', S.Lemma (S.RLdone))),
                  (* GEN BEGIN FUNCTION EXPRESSION *) fn ((G', B'), w') =>
                  let
                        
                        
                    (* GEN BEGIN TAG OUTSIDE LET *) val V'' = Whnf.normalize (V', w') (* GEN END TAG OUTSIDE LET *)
                                        (* G' |- V'' : type *)
                  in
                    sc' ((I.Decl (G', I.Dec (NONE, V'')),
                          I.Decl (B', S.Lemma (S.Splits (!MTPGlobal.maxSplit)))), I.comp (w', I.shift))
                  end (* GEN END FUNCTION EXPRESSION *))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) expand' (GB0, (I.Decl (G, D), I.Decl (B, T)), n) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((G0', B0'), sc') = expand' (GB0, (G, B), n+1) (* GEN END TAG OUTSIDE LET *)
        in
          ((I.Decl (G0', D), I.Decl (B0', T)), sc')
        end (* GEN END FUN BRANCH *)


    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (G) else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((Gnew, Bnew), sc) = expand' ((G, B), (G, B), 0) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (Gnew) else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((G', B'), w') = sc ((Gnew, Bnew), I.id) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheckCtx G' (* GEN END TAG OUTSIDE LET *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val S' = S.State (n, (G', B'), (IH, OH), d, S.orderSub (O, w'),
                   map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (i, F') => (i, F.forSub (F', w')) (* GEN END FUNCTION EXPRESSION *)) H, F.forSub (F, w')) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.doubleCheck
                  then FunTypeCheck.isState S'
                  else () (* GEN END TAG OUTSIDE LET *)
        in
          (* GEN BEGIN FUNCTION EXPRESSION *) fn () => S' (* GEN END FUNCTION EXPRESSION *)
        end


    (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
    fun apply f = f ()

    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    fun menu _ =  "Inference"

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val expand = expand (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val apply = apply (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val menu = menu (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor Filling *)
