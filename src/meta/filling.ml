MTPFilling  MTPGlobal MTPGLOBAL    StateSyn' STATESYN    Abstract ABSTRACT    TypeCheck TYPECHECK    MTPData MTPDATA    Search MTPSEARCH    Search StateSyn  StateSyn'   Whnf WHNF     MTPFILLING  struct (*! structure FunSyn = FunSyn' !*)
module exception exception type Operatormodule module module exception (* Checking for constraints: Used to be in abstract, now must be done explicitly! --cs*)
(* createEVars (G, F) = (Xs', P')

       Invariant:
       If   |- G ctx
       and  G |- F = [[x1:A1]] .. [[xn::An]] formula
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G; D |- P' = <X1', <.... <Xn', <>> ..> in F     for some D
    *)
let rec createEVars(g,  , (true,  , s)) (nil,  , unit) createEVars(g,  , (ex (dec (_,  , v),  , f),  , s)) let let  inlet  inlet  in in (x' :: xs,  , inx (x,  , p))(*    fun checkConstraints nil = raise Success
      | checkConstraints (X :: L) =
        if Abstract.closedExp (I.Null, (Whnf.normalize (X, I.id), I.id)) then checkConstraints L
        else ()
*)
(* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
let rec expand(s as state (n,  , (g,  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f)) let let  inlet  in in fun () -> (try  with )(* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
let rec applyf f ()(* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
let rec menu_ "Filling   (tries to close this subgoal)"let  inlet  inlet  in(* local *)
end