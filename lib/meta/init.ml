(* Initialization *)

(* Author: Carsten Schuermann *)

module MTPInit
    (MTPGlobal : MTPGLOBAL)
    (MTPData : MTPDATA)
    (Names : NAMES)
    (StateSyn' : STATESYN)
    (Formatter : FORMATTER)
    (Whnf : WHNF)
    (Print : PRINT)
    (FunPrint : FUNPRINT) : MTPINIT = struct
  (*! structure FunSyn = FunSyn' !*)

  module StateSyn = StateSyn'

  exception Error of string

  module I = IntSyn
  module F = FunSyn
  module S = StateSyn
  module Fmt = Formatter
  (* init (F, OF) = Ss'

       Invariant:
       If   . |- F formula    and   F in nf
       and  . |- OF order
       then Ss' is a list of initial states for_sml the theorem prover
    *)

  let rec init (F, OF) =
    (* added in case there are no existentials -fp *)
    let rec init' = function
      | (G, B), S.All (_, O), F.All (F.Prim D, F'), Ss ->
          let D' = Names.decName (G, D) in
          init'
            ( ( I.Decl (G, D'),
                I.Decl (B, S.Lemma (S.Splits !MTPGlobal.maxSplit)) ),
              O,
              F',
              Ss )
      | GB, S.And (O1, O2), F.And (F1, F2), Ss ->
          init' (GB, O1, F1, init' (GB, O2, F2, Ss))
      | GB, O, F', Ss ->
          S.State (List.length Ss + 1, GB, (F, OF), 1, O, [], F') :: Ss
      | GB, O, F', Ss ->
          S.State (List.length Ss + 1, GB, (F, OF), 1, O, [], F') :: Ss
    in
    Names.varReset I.Null;
    MTPData.maxFill := 0;
    init' ((I.Null, I.Null), OF, F, [])

  let init = init
  (* local *)
end

(* functor Init *)
