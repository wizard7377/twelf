(* Skolem constant administration *)

(* Author: Carsten Schuermann *)

module Skolem
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (IndexSkolem : INDEX)
    (ModeTable : MODETABLE)
    (Print : PRINT)
    (Compile : COMPILE)
    (Timers : TIMERS)
    (Names : NAMES) : SKOLEM = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  module I = IntSyn
  module M = ModeSyn
  (*! structure CompSyn = Compile.CompSyn !*)

  (* installSkolem (name, k, (V, mS), L) =

       Invariant:
            name is the name of a theorem
       and  imp is the number of implicit arguments
       and  V is its term together with the mode assignment mS
       and  L is the level of the declaration

       Effects: New Skolem constants are generated, named, and indexed
    *)

  let rec installSkolem (name, imp, (V, mS), L) =
    (* spine n = S'

           Invariant:
           S' = n; n-1; ... 1; Nil
        *)
    (* installSkolem' ((V, mS), s, k) = ()

           Invariant:
                G |- V : type
           and  G' |- s : G
           and  |G'| = d
           and  k is a continuation, mapping a type G' |- V' type
                to . |- {{G'}} V'

           Effects: New Skolem constants are generated, named, and indexed
        *)
    let rec spine = function
      | 0 -> I.Nil
      | n -> I.App (I.Root (I.BVar n, I.Nil), spine (n - 1))
    in
    let rec installSkolem' = function
      | d, (I.Pi ((D, DP), V), mS), s, k -> (
          match mS with
          | M.Mapp (M.Marg (M.Plus, _), mS') ->
              installSkolem'
                ( d + 1,
                  (V, mS'),
                  I.dot1 s,
                  fun V ->
                    k
                      (Abstract.piDepend
                         ((Whnf.normalizeDec (D, s), I.Meta), V)) )
              (*                                  fn V => k (I.Pi ((Whnf.normalizeDec (D, s), DP), V))) *)
          | M.Mapp (M.Marg (M.Minus, _), mS') ->
              (*                  val CompSyn.SClause r = CompSyn.sProgLookup sk *)
              let (I.Dec (_, V')) = D in
              let V'' = k (Whnf.normalize (V', s)) in
              let name' = Names.skonstName (name ^ "#") in
              let SD = I.SkoDec (name', None, imp, V'', L) in
              let sk = I.sgnAdd SD in
              let H = I.Skonst sk in
              let _ = IndexSkolem.install I.Ordinary H in
              let _ = Names.installConstName sk in
              let _ =
                (Timers.time Timers.compiling Compile.install) I.Ordinary sk
              in
              let S = spine d in
              let _ =
                if !Global.chatter >= 3 then
                  TextIO.print (Print.conDecToString SD ^ "\n")
                else ()
              in
              installSkolem' (d, (V, mS'), I.Dot (I.Exp (I.Root (H, S)), s), k))
      | _, (I.Uni _, M.Mnil), _, _ -> ()
    in
    installSkolem' (0, (V, mS), I.id, fun V -> V)
  (* install L = ()

       Invariant:
           L is a list of a's (mututal inductive theorems)
           which have an associated mode declaration

       Effect: Skolem constants for_sml all theorems are generated, named, and indexed
    *)

  let rec install = function
    | [] -> ()
    | a :: aL ->
        let (I.ConDec (name, _, imp, _, V, L)) = I.sgnLookup a in
        let (Some mS) = ModeTable.modeLookup a in
        let _ = installSkolem (name, imp, (V, mS), I.Type) in
        install aL

  let install = install
  (* local *)
end

(* functor Skolem *)
