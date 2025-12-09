(* Inference:  Version 1.3*)
(* Author: Carsten Schuermann *)

module Inference (MTPGlobal : MTPGLOBAL)
                   (*! (IntSyn : INTSYN) !*)
                   (*! module FunSyn' : FUNSYN !*)
                   (*! sharing FunSyn'.IntSyn = IntSyn !*)
                   module StateSyn' : STATESYN
                   (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                   (Abstract : ABSTRACT)
                   (*! sharing Abstract.IntSyn = IntSyn !*)
                   (TypeCheck : TYPECHECK)
                   (*! sharing TypeCheck.IntSyn = IntSyn !*)
                   (FunTypeCheck : FUNTYPECHECK)
                   (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                     sharing FunTypeCheck.StateSyn = StateSyn'
                   module UniqueSearch  : UNIQUESEARCH
                   (*! sharing UniqueSearch.IntSyn = IntSyn !*)
                   (*! sharing UniqueSearch.FunSyn = FunSyn' !*)
                     sharing UniqueSearch.StateSyn = StateSyn'
                   (Print : PRINT)
                   (*! sharing Print.IntSyn = IntSyn !*)
                   (Whnf : WHNF): INFERENCE =
                   (*! sharing Whnf.IntSyn = IntSyn !*)
struct
  (*! module FunSyn = FunSyn' !*)
  module StateSyn = StateSyn'

  exception Error of string

  type operator = (unit -> StateSyn'.State)

  local
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn

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
    let rec createEVars = function (G, (I.Pi ((I.Dec (_, V), I.Meta), V'), s)) -> 
        let
          let X = I.newEVar (G, I.EClo (V, s))
          let X' = Whnf.lowerEVar X
          let (Xs, FVs') = createEVars (G, (V', I.Dot (I.Exp X, s)))
        in
          (X' :: Xs, FVs')
        end
      | (G, FVs as (_, s)) -> (nil, FVs)



    (* forward (G, B, (V, F)) = (V', F')  (or none)

       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  G |- V type
       and  G; . |- F : formula
       then G |- V' type
       and  G; . |- F' : formula

    *)
    let rec forward = function (G, B, V as I.Pi ((_, I.Meta), _)) -> 
        let
          let _ = if !Global.doubleCheck
                    then TypeCheck.typeCheck (G, (V, I.Uni I.Type))
                    else ()
          let (Xs, (V', s')) = createEVars (G, (V, I.id))
        in
          (case  UniqueSearch.searchEx (2, Xs, fun nil -> [(Whnf.normalize (V', s'))]
                                                | _ => raise UniqueSearch.Error "Too many solutions")
             of [VF''] => SOME VF''

              | [] => NONE) handle UniqueSearch.Error _ => NONE
        end
      | (G, B, V) -> NONE



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

    let rec expand' = function ((G0, B0), (I.Null, I.Null), n) -> 
        ((I.Null, I.Null), fn ((G', B'), w') => ((G', B'), w'))
      | ((G0, B0), (I.Decl (G, D as I.Dec (_, V)), I.Decl (B, T as S.Lemma (S.RL))), n) -> 
        let
          let ((G0', B0'), sc') = expand' ((G0, B0), (G, B), n+1)
          let s = I.Shift (n+1)
          let Vs = Whnf.normalize (V, s)
        in
          case (forward (G0, B0, (Vs)))
            of NONE => ((I.Decl (G0', D), I.Decl (B0', T)), sc')
             | SOME (V') =>
                 ((I.Decl (G0', D), I.Decl (B0', S.Lemma (S.RLdone))),
                  fn ((G', B'), w') =>
                  let


                    let V'' = Whnf.normalize (V', w')
                                        (* G' |- V'' : type *)
                  in
                    sc' ((I.Decl (G', I.Dec (NONE, V'')),
                          I.Decl (B', S.Lemma (S.Splits (!MTPGlobal.maxSplit)))), I.comp (w', I.shift))
                  end)
        end
      | (GB0, (I.Decl (G, D), I.Decl (B, T)), n) -> 
        let
          let ((G0', B0'), sc') = expand' (GB0, (G, B), n+1)
        in
          ((I.Decl (G0', D), I.Decl (B0', T)), sc')
        end


    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
        let
          let _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (G) else ()
          let ((Gnew, Bnew), sc) = expand' ((G, B), (G, B), 0)
          let _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (Gnew) else ()
          let ((G', B'), w') = sc ((Gnew, Bnew), I.id)
          let _ = TypeCheck.typeCheckCtx G'

          let S' = S.State (n, (G', B'), (IH, OH), d, S.orderSub (O, w'),
                   map (fn (i, F') => (i, F.forSub (F', w'))) H, F.forSub (F, w'))
          let _ = if !Global.doubleCheck
                  then FunTypeCheck.isState S'
                  else ()
        in
          fn () => S'
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
    let expand = expand
    let apply = apply
    let menu = menu
  end (* local *)
end;; (* functor Filling *)
