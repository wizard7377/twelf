StatePrint  Global GLOBAL    State' STATE    Names NAMES    Formatter' FORMATTER    Print PRINT    Print Formatter  Formatter'   TomegaPrint TOMEGAPRINT    TomegaPrint Formatter  Formatter'    STATEPRINT  struct module (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
module exception module module module module module (*
    fun nameCtx I.Null = I.Null
      | nameCtx (I.Decl (Psi, T.UDec D)) =
          I.Decl (nameCtx Psi,
                  T.UDec (Names.decName (T.coerceCtx Psi, D)))
      | nameCtx (I.Decl (Psi, T.PDec (_, F, TC))) =
          I.Decl (nameCtx Psi,
                  T.PDec (SOME "s", F, TC))   (* to be fixed! --cs *)

*)
let rec nameCtxpsi psi(* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
let rec nameState(s) s(*
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
let rec formatCtx(null) [] formatCtx(decl (null,  , uDec d)) if ! chatter >= 4 then [hVbox ([break; formatDec (null,  , d)])] else [formatDec (null,  , d)] formatCtx(decl (null,  , pDec (sOME s,  , f,  , _))) if ! chatter >= 4 then [hVbox ([break; string s; space; string "::"; space; formatFor (null,  , f)])] else [string s; space; string "::"; space; formatFor (null,  , f)] formatCtx(decl (psi,  , uDec d)) let let  in in if ! chatter >= 4 then formatCtx psi @ [string ","; break; break] @ [hVbox ([break; formatDec (g,  , d)])] else formatCtx psi @ [string ","; break] @ [break; formatDec (g,  , d)] formatCtx(decl (psi,  , pDec (sOME s,  , f,  , _))) if ! chatter >= 4 then formatCtx psi @ [string ","; break; break] @ [hVbox ([break; string s; space; string "::"; space; formatFor (psi,  , f)])] else formatCtx psi @ [string ","; break] @ [break; string s; space; string "::"; space; formatFor (psi,  , f)](* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)
let rec formatState(state (w,  , psi,  , p,  , f,  , _)) vbox0 0 1 [string "------------------------"; break; string "------------------------"; break; formatPrg (psi,  , p)](* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *)
let rec stateToStrings (makestring_fmt (formatState s))let  inlet  inlet  in(* local *)
end