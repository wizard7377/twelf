(* Filling  Version 1.3*)
(* Author: Carsten Schuermann *)

module MTPFilling (MTPGlobal : MTPGLOBAL)
                    (*! (IntSyn : INTSYN) !*)
                    (*! module FunSyn' : FUNSYN !*)
                    (*! sharing FunSyn'.IntSyn = IntSyn !*)
                    module StateSyn' : STATESYN
                    (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                    (Abstract : ABSTRACT)
                    (*! sharing Abstract.IntSyn = IntSyn !*)
                    (TypeCheck : TYPECHECK)
                    (*! sharing TypeCheck.IntSyn = IntSyn !*)
                    (MTPData : MTPDATA)
                    module Search   : MTPSEARCH
                      sharing Search.StateSyn = StateSyn'
                    (Whnf : WHNF): MTPFILLING =
                    (*! sharing Whnf.IntSyn = IntSyn !*)
struct
  (*! module FunSyn = FunSyn' !*)
  module StateSyn = StateSyn'

  exception Error of string
  exception TimeOut

  type operator = (unit -> int * FunSyn.Pro)

  local
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn

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
    fun createEVars (G, (F.True, s)) = (nil, F.Unit)
      | createEVars (G, (F.Ex (I.Dec (_, V), F), s)) =
        let
          let X = I.newEVar (G, I.EClo (V, s))
          let X' = Whnf.lowerEVar X
          let (Xs, P) = createEVars (G, (F, I.Dot (I.Exp X, s)))
        in
          (X' :: Xs, F.Inx (X, P))
        end


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
          let _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (G) else ()
          let (Xs, P) = createEVars (G, (F, I.id))
        in
          fn () => ((Search.searchEx (!MTPGlobal.maxFill, Xs, fun max -> (if (!Global.doubleCheck) then
                                                       map (fn (X as I.EVar (_, G', V, _)) =>
                                                            TypeCheck.typeCheck (G', (X, V))) Xs
                                                     else []; raise Success max));
                     raise Error "Filling unsuccessful")
                    handle Success max => (MTPData.maxFill := Int.max (!MTPData.maxFill, max);
                                           (max, P)))
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
    let expand = expand
    let apply = apply
    let menu = menu
  end (* local *)
end;; (* functor Filling *)
