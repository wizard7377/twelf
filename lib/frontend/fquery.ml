(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)

module Fquery
  (Global : GLOBAL)
   (Names : NAMES)
   (ReconQuery : RECON_QUERY)
   (Timers : TIMERS)
   (Print : PRINT)
 : FQUERY =
struct
  module ExtQuery = ReconQuery

  exception AbortQuery of string


  module I = IntSyn
  module T = Tomega
  module W = WorldSyn
  module P = Paths

  (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
  fun evarInstToString (Xs) =
      if !Global.chatter >= 3
        then Print.evarInstToString (Xs)
      else ""

  (* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
  fun expToString GU =
      if !Global.chatter >= 3
        then Print.expToString GU
      else ""


  fun lower (0, G, V) = (G, V)
    | lower (n, G, I.Pi ((D, _), V)) = lower (n-1, I.Decl (G, D), V)

  fun run (quy, Paths.Loc (fileName, r)) =
      let
        (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
        let (V, optName, Xs) = ReconQuery.queryToQuery(quy, Paths.Loc (fileName, r))
                                        (* times itself *)
        let _ = if !Global.chatter >= 3
                  then print ("%fquery")
                else ()
        let _ = if !Global.chatter >= 3
                  then print (" ")
                else ()
        let _ = if !Global.chatter >= 3
                  then print ((Timers.time Timers.printing expToString)
                              (IntSyn.Null, V) ^ ".\n")
                else ()

        let (k, V1)  = Abstract.abstractDecImp V
        let (G, V2) = lower (k, I.Null, V1)
                                        (* G |- V'' : type *)
        let a = I.targetFam V2
        let W = W.lookup a
        let V3 = Worldify.worldifyGoal (G, V2)
        let _ = TypeCheck.typeCheck (G, (V3, I.Uni I.Type))
        let P = Converter.convertGoal (T.embedCtx G, V3)
        let V = (Timers.time Timers.delphin Opsem.evalPrg) P
      in
        print ("Delphin: " ^ TomegaPrint.prgToString (I.Null, V) ^ "\n")
      end

end;; (* functor Solve *)
