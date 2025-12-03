(* Skolem constant administration *)
(* Author: Carsten Schuermann *)

let recctor Skolem (module Global : GLOBAL
                (*! module IntSyn' : INTSYN !*)
                module Whnf : WHNF
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                module Abstract : ABSTRACT
                (*! sharing Abstract.IntSyn = IntSyn' !*)
                module IndexSkolem : INDEX
                (*! sharing IndexSkolem.IntSyn = IntSyn' !*)
                module ModeTable : MODETABLE
                (*! sharing ModeSyn.IntSyn = IntSyn' !*)
                module Print : PRINT
                (*! sharing Print.IntSyn = IntSyn' !*)
                module Compile : COMPILE
                (*! sharing Compile.IntSyn = IntSyn' !*)
                module Timers : TIMERS
                module Names : NAMES
                (*! sharing Names.IntSyn = IntSyn' !*)
                  )
  : SKOLEM =
struct
  (*! module IntSyn = IntSyn' !*)

  exception Error of string

  local
    module I = IntSyn
    module M = ModeSyn
    (*! module CompSyn = Compile.CompSyn !*)

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
        fun spine 0 = I.Nil
          | spine n = I.App (I.Root (I.BVar n, I.Nil),  spine (n-1))

        (* installSkolem' ((V, mS), s, k) = ()

           Invariant:
                G |- V : type
           and  G' |- s : G
           and  |G'| = d
           and  k is a continuation, mapping a type G' |- V' type
                to . |- {{G'}} V'

           Effects: New Skolem constants are generated, named, and indexed
        *)

        fun installSkolem' (d, (I.Pi ((D, DP), V), mS), s, k) =
            (case mS
               of M.Mapp (M.Marg (M.Plus, _), mS') =>
                    installSkolem' (d+1, (V, mS'), I.dot1 s,
                                    fun V -> k (Abstract.piDepend ((Whnf.normalizeDec (D, s), I.Meta), V)))
(*                                  fun V -> k (I.Pi ((Whnf.normalizeDec (D, s), DP), V))) *)
                | M.Mapp (M.Marg (M.Minus, _), mS') =>
                  let
                    let I.Dec (_, V') = D
                    let V'' = k (Whnf.normalize (V', s))
                    let name' = Names.skonstName (name ^ "#")
                    let SD = I.SkoDec (name', NONE, imp, V'', L)
                    let sk = I.sgnAdd SD
                    let H = I.Skonst sk
                    let _ = IndexSkolem.install I.Ordinary H
                    let _ = Names.installConstName sk
                    let _ = (Timers.time Timers.compiling Compile.install) I.Ordinary sk
(*                  let CompSyn.SClause r = CompSyn.sProgLookup sk *)
                    let S = spine d
                    let _ = if !Global.chatter >= 3
                              then TextIO.print (Print.conDecToString SD ^ "\n")
                            else ()
                  in
                    installSkolem' (d, (V, mS'), I.Dot (I.Exp (I.Root (H, S)), s), k)
                  end)
          | installSkolem' (_, (I.Uni _, M.Mnil), _, _) = ()


      in
        installSkolem' (0, (V, mS), I.id, fun V -> V)
      end

    (* install L = ()

       Invariant:
           L is a list of a's (mututal inductive theorems)
           which have an associated mode declaration

       Effect: Skolem constants for all theorems are generated, named, and indexed
    *)
    fun install nil = ()
      | install (a :: aL) =
        let
          let I.ConDec (name, _, imp, _, V, L) = I.sgnLookup a
          let SOME mS = ModeTable.modeLookup a
          let _ = installSkolem (name, imp, (V, mS), I.Type)
        in
          install aL
        end


  in
    let install = install
  end (* local *)
end (* functor Skolem *)
