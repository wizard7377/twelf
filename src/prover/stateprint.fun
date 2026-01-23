(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

functor StatePrint
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State'  : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Formatter' : FORMATTER
   structure Print : PRINT
     sharing Print.Formatter = Formatter'
     (*! sharing Print.IntSyn = IntSyn' !*)
   structure TomegaPrint : TOMEGAPRINT
   (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
   (*! sharing TomegaPrint.Tomega = Tomega' !*)
     sharing TomegaPrint.Formatter = Formatter')
     : STATEPRINT =
struct
  structure Formatter = Formatter'
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'


  exception Error of string

  local
    structure I = IntSyn
    structure T = Tomega
    structure S = State'
    structure N = Names
    structure Fmt = Formatter


(*
    fun nameCtx I.Null = I.Null
      | nameCtx (I.Decl (Psi, T.UDec D)) =
          I.Decl (nameCtx Psi,
                  T.UDec (Names.decName (T.coerceCtx Psi, D)))
      | nameCtx (I.Decl (Psi, T.PDec (_, F, TC))) =
          I.Decl (nameCtx Psi,
                  T.PDec (SOME "s", F, TC))   (* to be fixed! --cs *)

*)

      fun nameCtx Psi = Psi


    (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
    fun nameState (S) = S

(*
    fun formatOrder (G, S.Arg (Us, Vs)) =
          [Print.formatExp (G, I.EClo Us), Fmt.string ":",
           Print.formatExp (G, I.EClo Vs)]
      | formatOrder (G, S.Lex Os) =
          [Fmt.string "{", Fmt.hvbox0 1 0 1 (formatOrders (G, Os)), Fmt.string "}"]
      | formatOrder (G, S.Simul Os) =
          [Fmt.string "[", Fmt.hvbox0 1 0 1 (formatOrders (G, Os)), Fmt.string "]"]

    and formatOrders (G, nil) = nil
      | formatOrders (G, O :: nil) = formatOrder (G, O)
      | formatOrders (G, O :: Os) = formatOrder (G, O) @
          [Fmt.string ",", Fmt.break]  @ formatOrders (G, Os)

    (* format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    *)
    fun formatTag (G, S.Parameter l) = [Fmt.string "<p>"]
      | formatTag (G, S.Lemma (S.Splits k)) = [Fmt.string "<i",
                                                 Fmt.string (Int.toString k),
                                                 Fmt.string ">"]
      | formatTag (G, S.Lemma (S.RL)) = [Fmt.string "<i >"]
      | formatTag (G, S.Lemma (S.RLdone)) = [Fmt.string "<i*>"]
(*      | formatTag (G, S.Assumption k) = [Fmt.string "<a",
                                         Fmt.string (Int.toString k),
                                         Fmt.string ">"] *)

*)
    (* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)
    fun formatCtx (I.Null) = []
      | formatCtx (I.Decl (I.Null, T.UDec D)) =
        if !Global.chatter >= 4 then
          [Fmt.hvbox ([Fmt.break, Print.formatDec (I.Null, D)])]
        else
          [Print.formatDec (I.Null, D)]
      | formatCtx (I.Decl (I.Null, T.PDec (SOME s, F, _))) =
        if !Global.chatter >= 4 then
          [Fmt.hvbox ([Fmt.break, Fmt.string s, Fmt.space,
                       Fmt.string "::", Fmt.space, TomegaPrint.formatFor (I.Null, F)])]
        else
          [Fmt.string s, Fmt.space, Fmt.string "::", Fmt.space,
           TomegaPrint.formatFor (I.Null, F)]
      | formatCtx (I.Decl (Psi, T.UDec D)) =
        let
          val G = T.coerceCtx Psi
        in
          if !Global.chatter >= 4 then
            formatCtx Psi @ [Fmt.string ",", Fmt.break, Fmt.break] @
            [Fmt.hvbox ([Fmt.break, Print.formatDec (G, D)])]
          else
            formatCtx Psi @ [Fmt.string ",",  Fmt.break] @
            [Fmt.break, Print.formatDec (G, D)]
        end
      | formatCtx (I.Decl (Psi, T.PDec (SOME s, F, _))) =
        if !Global.chatter >= 4 then
          formatCtx Psi @ [Fmt.string ",", Fmt.break, Fmt.break] @
          [Fmt.hvbox ([Fmt.break, Fmt.string s, Fmt.space, Fmt.string "::", Fmt.space, TomegaPrint.formatFor (Psi, F)])]
        else
          formatCtx Psi @ [Fmt.string ",",  Fmt.break] @
          [Fmt.break, Fmt.string s, Fmt.space, Fmt.string "::", Fmt.space,
           TomegaPrint.formatFor (Psi, F)]

    (* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)
    fun formatState (S.State (W, Psi, P, F, _)) =
          Fmt.vbox0 0 1
          [Fmt.string "------------------------", Fmt.break,
           Fmt.string "------------------------", Fmt.break,
           TomegaPrint.formatPrg (Psi, P)]

    (* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *)
    fun stateToString S =
      (Fmt.makestring_fmt (formatState S))


  in
    val nameState = nameState
    val formatState = formatState
    val stateToString = stateToString
  end (* local *)
end (* functor MTPrint *)