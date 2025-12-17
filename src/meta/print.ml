MTPrint  Global GLOBAL    Names NAMES    StateSyn' STATESYN    Formatter' FORMATTER    Print PRINT    Print Formatter  Formatter'   FunPrint FUNPRINT    FunPrint Formatter  Formatter'    MTPRINT  struct module module exception module module module module (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
let rec nameState(state (n,  , (g,  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f)) let let  inlet  in in state (n,  , (g',  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f)let rec formatOrder(g,  , arg (us,  , vs)) [formatExp (g,  , eClo us); string ":"; formatExp (g,  , eClo vs)] formatOrder(g,  , lex os) [string "{"; hVbox0 1 0 1 (formatOrders (g,  , os)); string "}"] formatOrder(g,  , simul os) [string "["; hVbox0 1 0 1 (formatOrders (g,  , os)); string "]"] formatOrders(g,  , nil) nil formatOrders(g,  , o :: nil) formatOrder (g,  , o) formatOrders(g,  , o :: os) formatOrder (g,  , o) @ [string ","; break] @ formatOrders (g,  , os)(* format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    *)
let rec formatTag(g,  , parameter l) [string "<p>"] formatTag(g,  , lemma (splits k)) [string "<i"; string (toString k); string ">"] formatTag(g,  , lemma (rL)) [string "<i >"] formatTag(g,  , lemma (rLdone)) [string "<i*>"](*      | formatTag (G, S.Assumption k) = [Fmt.String "<a",
                                         Fmt.String (Int.toString k),
                                         Fmt.String ">"] *)
(* formatCtx (G, B) = fmt'

       Invariant:
       If   |- G ctx       and G is already named
       and  |- B : G tags
       then fmt' is a format describing the context (G, B)
    *)
let rec formatCtx(null,  , b) [] formatCtx(decl (null,  , d),  , decl (null,  , t)) if ! chatter >= 4 then [hVbox (formatTag (null,  , t) @ [break; formatDec (null,  , d)])] else [formatDec (null,  , d)] formatCtx(decl (g,  , d),  , decl (b,  , t)) if ! chatter >= 4 then formatCtx (g,  , b) @ [string ","; break; break] @ [hVbox (formatTag (g,  , t) @ [break; formatDec (g,  , d)])] else formatCtx (g,  , b) @ [string ","; break] @ [break; formatDec (g,  , d)](* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)
let rec formatState(state (n,  , (g,  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f)) vbox0 0 1 [hVbox0 1 0 1 (formatOrder (g,  , o)); break; string "========================"; break; hVbox0 1 0 1 (formatCtx (g,  , b)); break; string "------------------------"; break; formatForBare (g,  , f)](* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *)
let rec stateToStrings (makestring_fmt (formatState s))let  inlet  inlet  in(* local *)
end