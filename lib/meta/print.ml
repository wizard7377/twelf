(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

module MTPrint (Global : GLOBAL)
                 (*! (IntSyn : INTSYN) !*)
                 (*! (FunSyn : FUNSYN) !*)
                 (*! sharing FunSyn.IntSyn = IntSyn !*)
                 (Names : NAMES)
                 (*! sharing Names.IntSyn = IntSyn !*)
                 module StateSyn' : STATESYN
                 (*! sharing StateSyn'.FunSyn = FunSyn !*)
                   (*! sharing StateSyn'.IntSyn = IntSyn !*)
                 module Formatter' : FORMATTER
                 (Print : PRINT)
                   sharing Print.Formatter = Formatter'
                   (*! sharing Print.IntSyn = IntSyn !*)
                 (FunPrint : FUNPRINT)
                 (*! sharing FunPrint.FunSyn = FunSyn !*)
                   sharing FunPrint.Formatter = Formatter')
  : MTPRINT =
struct
  module Formatter = Formatter'
  module StateSyn = StateSyn'

  exception Error of string

  local
    module I = IntSyn
    module N = Names
    module S = StateSyn
    module Fmt = Formatter


    (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
    fun nameState (S.State (n, (G, B), (IH, OH), d, O, H, F)) =
        let
          let _ = Names.varReset I.Null
          let G' = Names.ctxName G
        in
          S.State (n, (G', B), (IH, OH), d, O, H, F)
        end


    fun formatOrder (G, S.Arg (Us, Vs)) =
          [Print.formatExp (G, I.EClo Us), Fmt.String ":",
           Print.formatExp (G, I.EClo Vs)]
      | formatOrder (G, S.Lex Os) =
          [Fmt.String "{", Fmt.HVbox0 1 0 1 (formatOrders (G, Os)), Fmt.String "}"]
      | formatOrder (G, S.Simul Os) =
          [Fmt.String "[", Fmt.HVbox0 1 0 1 (formatOrders (G, Os)), Fmt.String "]"]

    and formatOrders (G, nil) = nil
      | formatOrders (G, O :: nil) = formatOrder (G, O)
      | formatOrders (G, O :: Os) = formatOrder (G, O) @
          [Fmt.String ",", Fmt.Break]  @ formatOrders (G, Os)

    (* format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    *)
    fun formatTag (G, S.Parameter l) = [Fmt.String "<p>"]
      | formatTag (G, S.Lemma (S.Splits k)) = [Fmt.String "<i",
                                                 Fmt.String (Int.toString k),
                                                 Fmt.String ">"]
      | formatTag (G, S.Lemma (S.RL)) = [Fmt.String "<i >"]
      | formatTag (G, S.Lemma (S.RLdone)) = [Fmt.String "<i*>"]
(*      | formatTag (G, S.Assumption k) = [Fmt.String "<a",
                                         Fmt.String (Int.toString k),
                                         Fmt.String ">"] *)


    (* formatCtx (G, B) = fmt'

       Invariant:
       If   |- G ctx       and G is already named
       and  |- B : G tags
       then fmt' is a format describing the context (G, B)
    *)
    fun formatCtx (I.Null, B) = []
      | formatCtx (I.Decl (I.Null, D), I.Decl (I.Null, T)) =
        if !Global.chatter >= 4 then
          [Fmt.HVbox (formatTag (I.Null, T) @ [Fmt.Break, Print.formatDec (I.Null, D)])]
        else
          [Print.formatDec (I.Null, D)]
      | formatCtx (I.Decl (G, D), I.Decl (B, T)) =
        if !Global.chatter >= 4 then
          formatCtx (G, B) @ [Fmt.String ",", Fmt.Break, Fmt.Break] @
          [Fmt.HVbox (formatTag (G, T) @ [Fmt.Break, Print.formatDec (G, D)])]
        else
          formatCtx (G, B) @ [Fmt.String ",",  Fmt.Break] @
         [Fmt.Break, Print.formatDec (G, D)]


    (* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)
    fun formatState (S.State (n, (G, B), (IH, OH), d, O, H, F)) =
          Fmt.Vbox0 0 1
          [Fmt.HVbox0 1 0 1 (formatOrder (G, O)), Fmt.Break,
           Fmt.String "========================", Fmt.Break,
           Fmt.HVbox0 1 0 1 (formatCtx (G, B)), Fmt.Break,
           Fmt.String "------------------------", Fmt.Break,
           FunPrint.formatForBare (G, F)]


    (* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *)
    fun stateToString S =
      (Fmt.makestring_fmt (formatState S))


  in
    let nameState = nameState
    let formatState = formatState
    let stateToString = stateToString
  end (* local *)
end (* functor MTPrint *)