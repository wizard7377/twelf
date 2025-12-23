(* Filling: Version 1.3 *)

(* Author: Carsten Schuermann *)

module type MTPFILLING = sig
  (*! structure FunSyn : Funsyn.FUNSYN !*)
  module StateSyn : Statesyn.State.STATESYN

  exception Error of string
  exception TimeOut

  type operator

  val expand : StateSyn.state -> operator
  val apply : operator -> int * FunSyn.pro
  val menu : operator -> string
end

(* signature MTPFILLING *)
(* Filling  Version 1.3*)

(* Author: Carsten Schuermann *)

module MTPFilling
    (MTPGlobal : Global.MTPGLOBAL)
    (StateSyn' : Statesyn.State.STATESYN)
    (Abstract : Abstract.ABSTRACT)
    (TypeCheck : Typecheck.TYPECHECK)
    (MTPData : Data.MTPDATA)
    (Search : Search.MTPSEARCH)
    (Whnf : Whnf.WHNF) : MTPFILLING = struct
  (*! structure FunSyn = FunSyn' !*)

  module StateSyn = StateSyn'

  exception Error of string
  exception TimeOut

  type operator = unit -> int * FunSyn.pro

  module S = StateSyn
  module F = FunSyn
  module I = IntSyn

  exception Success of int
  (* Checking for_sml constraints: Used to be in abstract, now must be done explicitly! --cs*)

  (* createEVars (G, F) = (Xs', P')

       Invariant:
       If   |- G ctx
       and  G |- F = [[x1:A1]] .. [[xn::An]] formula
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for_sml all i <= n
       and  G; D |- P' = <X1', <.... <Xn', <>> ..> in F     for_sml some D
    *)

  let rec createEVars = function
    | G, (F.True, s) -> ([], F.Unit)
    | G, (F.Ex (I.Dec (_, V), F), s) ->
        let X = I.newEVar (G, I.EClo (V, s)) in
        let X' = Whnf.lowerEVar X in
        let Xs, P = createEVars (G, (F, I.Dot (I.Exp X, s))) in
        (X' :: Xs, F.Inx (X, P))
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

  let rec expand S =
    let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx G else () in
    let Xs, P = createEVars (G, (F, I.id)) in
    fun () ->
      try
        Search.searchEx
          ( !MTPGlobal.maxFill,
            Xs,
            fun max ->
              if !Global.doubleCheck then
                map (fun X -> TypeCheck.typeCheck (G', (X, V))) Xs
              else [];
              raise (Success max) );
        raise (Error "Filling unsuccessful")
      with Success max ->
        MTPData.maxFill := Int.max (!MTPData.maxFill, max);
        (max, P)
  (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)

  let rec apply f = f ()
  (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)

  let rec menu _ = "Filling   (tries to close this subgoal)"
  let expand = expand
  let apply = apply
  let menu = menu
  (* local *)
end

(* functor Filling *)
