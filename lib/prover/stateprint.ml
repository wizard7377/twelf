open Basis ;; 
(* Meta Printer Version 1.3 *)

(* Author: Carsten Schuermann *)

module type STATEPRINT = sig
  module Formatter : Formatter.FORMATTER

  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure Tomega : Tomega.TOMEGA !*)
  module State : State.STATE

  exception Error of string

  val nameState : State.state -> State.state
  val formatState : State.state -> Formatter.format
  val stateToString : State.state -> string
end

(* signature State.STATEPRINT *)
(* Meta Printer Version 1.3 *)

(* Author: Carsten Schuermann *)

module StatePrint
    (Global : Global.GLOBAL)
    (State' : State.STATE)
    (Names : Names.NAMES)
    (Formatter' : Formatter.FORMATTER)
    (Print : Print.PRINT)
    (TomegaPrint : Tomega.Tomegaprint.TOMEGAPRINT) : State.STATEPRINT = struct
  module Formatter = Formatter'
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  module State = State'

  exception Error of string

  module I = IntSyn
  module T = Tomega
  module S = State'
  module N = Names
  module Fmt = Formatter
  (*
    fun nameCtx I.Null = I.Null
      | nameCtx (I.Decl (Psi, T.UDec D)) =
          I.Decl (nameCtx Psi,
                  T.UDec (Names.decName (T.coerceCtx Psi, D)))
      | nameCtx (I.Decl (Psi, T.PDec (_, F, TC))) =
          I.Decl (nameCtx Psi,
                  T.PDec (SOME "s", F, TC))   (* to be fixed! --cs *)

*)

  let rec nameCtx Psi = Psi
  (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)

  let rec nameState S = S
  (*
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

*)

  (* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)

  let rec formatCtx = function
    | I.Null -> []
    | I.Decl (I.Null, T.UDec D) ->
        if !Global.chatter >= 4 then
          [ Fmt.HVbox [ Fmt.Break; Print.formatDec (I.Null, D) ] ]
        else [ Print.formatDec (I.Null, D) ]
    | I.Decl (I.Null, T.PDec (Some s, F, _)) ->
        if !Global.chatter >= 4 then
          [
            Fmt.HVbox
              [
                Fmt.Break;
                Fmt.String s;
                Fmt.Space;
                Fmt.String "::";
                Fmt.Space;
                TomegaPrint.formatFor (I.Null, F);
              ];
          ]
        else
          [
            Fmt.String s;
            Fmt.Space;
            Fmt.String "::";
            Fmt.Space;
            TomegaPrint.formatFor (I.Null, F);
          ]
    | I.Decl (Psi, T.UDec D) ->
        let G = T.coerceCtx Psi in
        if !Global.chatter >= 4 then
          formatCtx Psi
          @ [ Fmt.String ","; Fmt.Break; Fmt.Break ]
          @ [ Fmt.HVbox [ Fmt.Break; Print.formatDec (G, D) ] ]
        else
          formatCtx Psi
          @ [ Fmt.String ","; Fmt.Break ]
          @ [ Fmt.Break; Print.formatDec (G, D) ]
    | I.Decl (Psi, T.PDec (Some s, F, _)) ->
        if !Global.chatter >= 4 then
          formatCtx Psi
          @ [ Fmt.String ","; Fmt.Break; Fmt.Break ]
          @ [
              Fmt.HVbox
                [
                  Fmt.Break;
                  Fmt.String s;
                  Fmt.Space;
                  Fmt.String "::";
                  Fmt.Space;
                  TomegaPrint.formatFor (Psi, F);
                ];
            ]
        else
          formatCtx Psi
          @ [ Fmt.String ","; Fmt.Break ]
          @ [
              Fmt.Break;
              Fmt.String s;
              Fmt.Space;
              Fmt.String "::";
              Fmt.Space;
              TomegaPrint.formatFor (Psi, F);
            ]
  (* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)

  let rec formatState (S.State (W, Psi, P, F, _)) =
    Fmt.Vbox0
      ( 0,
        1,
        [
          Fmt.String "------------------------";
          Fmt.Break;
          Fmt.String "------------------------";
          Fmt.Break;
          TomegaPrint.formatPrg (Psi, P);
        ] )
  (* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *)

  let rec stateToString S = Fmt.makestring_fmt (formatState S)
  let nameState = nameState
  let formatState = formatState
  let stateToString = stateToString
  (* local *)
end

(* functor MTPrint *)
