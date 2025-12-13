(* Filling  Version 1.3*)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) MTPFilling (structure MTPGlobal : MTPGLOBAL
                    (*! structure IntSyn : INTSYN !*)
                    (*! structure FunSyn' : FUNSYN !*)
                    (*! sharing FunSyn'.IntSyn = IntSyn !*)
                    structure StateSyn' : STATESYN
                    (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                    structure Abstract : ABSTRACT
                    (*! sharing Abstract.IntSyn = IntSyn !*)
                    structure TypeCheck : TYPECHECK
                    (*! sharing TypeCheck.IntSyn = IntSyn !*)
                    structure MTPData : MTPDATA
                    structure Search   : MTPSEARCH
                      sharing Search.StateSyn = StateSyn'
                    structure Whnf : WHNF
                    (*! sharing Whnf.IntSyn = IntSyn !*)
                      )
  : MTPFILLING =
struct
  (*! structure FunSyn = FunSyn' !*)
  structure StateSyn = StateSyn'

  exception Error of string
  exception TimeOut

  type operator = (unit -> int * FunSyn.pro)

  local
    structure S = StateSyn
    structure F = FunSyn
    structure I = IntSyn

    exception Success of int

    (* Checking for constraints: Used to be in abstract, now must be done explicitly! --cs*)

    (* createEVars (G, F) = (Xs', P')

       Invariant:
       If   |- G ctx
       and  G |- F = [[x1:A1]] .. [[xn::An]] formula
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G; D |- P' = <X1', <.... <Xn', <>> ..> in F     for some D
    *)
    fun (* GEN BEGIN FUN FIRST *) createEVars (G, (F.True, s)) = (nil, F.Unit) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createEVars (G, (F.Ex (I.Dec (_, V), F), s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V, s)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X' = Whnf.lowerEVar X (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Xs, P) = createEVars (G, (F, I.Dot (I.Exp X, s))) (* GEN END TAG OUTSIDE LET *)
        in
          (X' :: Xs, F.Inx (X, P))
        end (* GEN END FUN BRANCH *)


(*    fun checkConstraints nil = raise Success
      | checkConstraints (X :: L) =
        if Abstract.closedExp (I.Null, (Whnf.normalize (X, I.id), I.id)) then checkConstraints L
        else ()
*)

    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (G) else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Xs, P) = createEVars (G, (F, I.id)) (* GEN END TAG OUTSIDE LET *)
        in
          (* GEN BEGIN FUNCTION EXPRESSION *) fn () => ((Search.searchEx (!MTPGlobal.maxFill, Xs, (* GEN BEGIN FUNCTION EXPRESSION *) fn max => (if (!Global.doubleCheck) then
                                                       map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (X as I.EVar (_, G', V, _)) =>
                                                            TypeCheck.typeCheck (G', (X, V)) (* GEN END FUNCTION EXPRESSION *)) Xs
                                                     else []; raise Success max) (* GEN END FUNCTION EXPRESSION *));
                     raise Error "Filling unsuccessful")
                    handle Success max => (MTPData.maxFill := Int.max (!MTPData.maxFill, max);
                                           (max, P))) (* GEN END FUNCTION EXPRESSION *)
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
    fun menu _ =  "Filling   (tries to close this subgoal)"

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val expand = expand (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val apply = apply (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val menu = menu (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor Filling *)
