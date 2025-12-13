(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Fquery
  (structure Global : GLOBAL
   structure Names : NAMES
   structure ReconQuery : RECON_QUERY
   structure Timers : TIMERS
   structure Print : PRINT)
 : FQUERY =
struct
  structure ExtQuery = ReconQuery

  exception AbortQuery of string


  structure I = IntSyn
  structure T = Tomega
  structure W = WorldSyn
  structure P = Paths

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


  fun (* GEN BEGIN FUN FIRST *) lower (0, G, V) = (G, V) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) lower (n, G, I.Pi ((D, _), V)) = lower (n-1, I.Decl (G, D), V) (* GEN END FUN BRANCH *)

  fun run (quy, Paths.Loc (fileName, r)) =
      let
        (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (V, optName, Xs) = ReconQuery.queryToQuery(quy, Paths.Loc (fileName, r)) (* GEN END TAG OUTSIDE LET *)
                                        (* times itself *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 3
                  then print ("%fquery")
                else () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 3
                  then print (" ")
                else () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 3
                  then print ((Timers.time Timers.printing expToString)
                              (IntSyn.Null, V) ^ ".\n")
                else () (* GEN END TAG OUTSIDE LET *)
  
        (* GEN BEGIN TAG OUTSIDE LET *) val (k, V1)  = Abstract.abstractDecImp V (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (G, V2) = lower (k, I.Null, V1) (* GEN END TAG OUTSIDE LET *)
                                        (* G |- V'' : type *)
        (* GEN BEGIN TAG OUTSIDE LET *) val a = I.targetFam V2 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val W = W.lookup a (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val V3 = Worldify.worldifyGoal (G, V2) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheck (G, (V3, I.Uni I.Type)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val P = Converter.convertGoal (T.embedCtx G, V3) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val V = (Timers.time Timers.delphin Opsem.evalPrg) P (* GEN END TAG OUTSIDE LET *)
      in
        print ("Delphin: " ^ TomegaPrint.prgToString (I.Null, V) ^ "\n")
      end

end (* GEN END FUNCTOR DECL *); (* functor Solve *)
