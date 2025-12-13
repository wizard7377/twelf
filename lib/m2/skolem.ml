(* Skolem constant administration *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Skolem (structure Global : GLOBAL
                (*! structure IntSyn' : INTSYN !*)
                structure Whnf : WHNF
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                structure Abstract : ABSTRACT
                (*! sharing Abstract.IntSyn = IntSyn' !*)
                structure IndexSkolem : INDEX
                (*! sharing IndexSkolem.IntSyn = IntSyn' !*)
                structure ModeTable : MODETABLE
                (*! sharing ModeSyn.IntSyn = IntSyn' !*)
                structure Print : PRINT
                (*! sharing Print.IntSyn = IntSyn' !*)
                structure Compile : COMPILE
                (*! sharing Compile.IntSyn = IntSyn' !*)
                structure Timers : TIMERS
                structure Names : NAMES
                (*! sharing Names.IntSyn = IntSyn' !*)
                  )
  : SKOLEM =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn
    (*! structure CompSyn = Compile.CompSyn !*)

    (* installSkolem (name, k, (V, mS), L) =

       Invariant:
            name is the name of a theorem
       and  imp is the number of implicit arguments
       and  V is its term together with the mode assignment mS
       and  L is the level of the declaration

       Effects: New Skolem constants are generated, named, and indexed
    *)
    fun installSkolem (name, imp, (V, mS), L) =
      let
        (* spine n = S'
    
           Invariant:
           S' = n; n-1; ... 1; Nil
        *)
        fun (* GEN BEGIN FUN FIRST *) spine 0 = I.Nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) spine n = I.App (I.Root (I.BVar n, I.Nil),  spine (n-1)) (* GEN END FUN BRANCH *)
    
        (* installSkolem' ((V, mS), s, k) = ()
    
           Invariant:
                G |- V : type
           and  G' |- s : G
           and  |G'| = d
           and  k is a continuation, mapping a type G' |- V' type
                to . |- {{G'}} V'
    
           Effects: New Skolem constants are generated, named, and indexed
        *)
    
        fun (* GEN BEGIN FUN FIRST *) installSkolem' (d, (I.Pi ((D, DP), V), mS), s, k) =
            (case mS
               of M.Mapp (M.Marg (M.Plus, _), mS') =>
                    installSkolem' (d+1, (V, mS'), I.dot1 s,
                                    (* GEN BEGIN FUNCTION EXPRESSION *) fn V => k (Abstract.piDepend ((Whnf.normalizeDec (D, s), I.Meta), V)) (* GEN END FUNCTION EXPRESSION *))
            (*                                  fn V => k (I.Pi ((Whnf.normalizeDec (D, s), DP), V))) *)
                | M.Mapp (M.Marg (M.Minus, _), mS') =>
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V') = D (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val V'' = k (Whnf.normalize (V', s)) (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val name' = Names.skonstName (name ^ "#") (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val SD = I.SkoDec (name', NONE, imp, V'', L) (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val sk = I.sgnAdd SD (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val H = I.Skonst sk (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val _ = IndexSkolem.install I.Ordinary H (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.installConstName sk (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val _ = (Timers.time Timers.compiling Compile.install) I.Ordinary sk (* GEN END TAG OUTSIDE LET *)
            (*                  val CompSyn.SClause r = CompSyn.sProgLookup sk *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val S = spine d (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 3
                              then TextIO.print (Print.conDecToString SD ^ "\n")
                            else () (* GEN END TAG OUTSIDE LET *)
                  in
                    installSkolem' (d, (V, mS'), I.Dot (I.Exp (I.Root (H, S)), s), k)
                  end) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) installSkolem' (_, (I.Uni _, M.Mnil), _, _) = () (* GEN END FUN BRANCH *)
    
    
      in
        installSkolem' (0, (V, mS), I.id, (* GEN BEGIN FUNCTION EXPRESSION *) fn V => V (* GEN END FUNCTION EXPRESSION *))
      end

    (* install L = ()

       Invariant:
           L is a list of a's (mututal inductive theorems)
           which have an associated mode declaration

       Effect: Skolem constants for all theorems are generated, named, and indexed
    *)
    fun (* GEN BEGIN FUN FIRST *) install nil = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) install (a :: aL) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val I.ConDec (name, _, imp, _, V, L) = I.sgnLookup a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val SOME mS = ModeTable.modeLookup a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = installSkolem (name, imp, (V, mS), I.Type) (* GEN END TAG OUTSIDE LET *)
        in
          install aL
        end (* GEN END FUN BRANCH *)


  in
    (* GEN BEGIN TAG OUTSIDE LET *) val install = install (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *) (* functor Skolem *)
