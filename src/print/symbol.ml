SymbolAscii   SYMBOL  struct let rec idSizes (s,  , size s)let  inlet  inlet  inlet  inlet  inlet  inlet  inlet rec fvars idSize ("`" ^ s)let  inend    SymbolTeXfp   SYMBOL  struct (* Illegal constituents: \ _ $ # *)
(* { } are also special, but cannot occur in identifiers *)
let rec quoteChar'\\' "\\\\" quoteChar'_' "\\_" quoteChar'$' "\\$" quoteChar'#' "\\#" quoteChar''' "$'$" quoteChar'<' "$<$" quoteChar'>' "$>$" quoteChar'^' "\\^{\\ }" quoteChar'0' "$_0$" quoteChar'1' "$_1$" quoteChar'2' "$_2$" quoteChar'3' "$_3$" quoteChar'4' "$_4$" quoteChar'5' "$_5$" quoteChar'6' "$_6$" quoteChar'7' "$_7$" quoteChar'8' "$_8$" quoteChar'9' "$_9$" quoteCharc str clet rec quotes translate quoteChar s(*
  fun mathQuoteChar #"\\" = "\\\\"
    | mathQuoteChar #"_" = "\\_"
    | mathQuoteChar #"$" = "\\$"
    | mathQuoteChar #"#" = "\\#"
    | mathquoteChar #"^" = "\\hat{\\quad}$"
    | mathQuoteChar #"0" = "{_0}"
    | mathQuoteChar #"1" = "{_1}"
    | mathQuoteChar #"2" = "{_2}"
    | mathQuoteChar #"3" = "{_3}"
    | mathQuoteChar #"4" = "{_4}"
    | mathQuoteChar #"5" = "{_5}"
    | mathQuoteChar #"6" = "{_6}"
    | mathQuoteChar #"7" = "{_7}"
    | mathQuoteChar #"8" = "{_8}"
    | mathQuoteChar #"9" = "{_9}"
    | mathQuoteChar c = String.str c

  fun mathQuote s = String.translate mathQuoteChar s
  *)
let rec strs ("\\Str{" ^ quote s ^ "}",  , size s)let rec evars ("\\EVar{" ^ quote s ^ "}",  , size s)let rec bvars ("\\BVar{" ^ quote s ^ "}",  , size s)let rec consts ("\\Const{" ^ quote s ^ "}",  , size s)let rec labels ("\\Label{" ^ quote s ^ "}",  , size s)let rec skonsts ("\\Skonst{" ^ quote s ^ "}",  , size s)let rec defs ("\\Def{" ^ quote s ^ "}",  , size s)let rec fvars ("\\FVar{" ^ quote s ^ "}",  , size s)let rec sym"->" ("$\\rightarrow$",  , 1) sym"<-" ("$\\leftarrow$",  , 1) sym"{" ("$\\Pi$",  , 1) sym"}" (".",  , 1) sym"[" ("$\\lambda$",  , 1) sym"]" (".",  , 1) sym"type" ("{\\Type}",  , 4) sym"kind" ("{\\Kind}",  , 4) sym"_" ("\\_",  , 1) sym"..." ("$\\ldots$",  , 3) sym"%%" ("%%",  , 2) sym"%skolem" ("%skolem",  , 7) syms (s,  , size s)(* ():.= *)
end    SymbolTeX   SYMBOL  struct (* Illegal constituents: \ _ $ # *)
(* { } are also special, but cannot occur in identifiers *)
let rec quoteChar'\\' "\\\\" quoteChar'_' "\\_" quoteChar'$' "\\$" quoteChar'#' "\\#" quoteChar'^' "\\^{\\ }" quoteChar'0' "$_0$" quoteChar'1' "$_1$" quoteChar'2' "$_2$" quoteChar'3' "$_3$" quoteChar'4' "$_4$" quoteChar'5' "$_5$" quoteChar'6' "$_6$" quoteChar'7' "$_7$" quoteChar'8' "$_8$" quoteChar'9' "$_9$" quoteCharc str clet rec quotes translate quoteChar s(*
  fun mathQuoteChar #"\\" = "\\\\"
    | mathQuoteChar #"_" = "\\_"
    | mathQuoteChar #"$" = "\\$"
    | mathQuoteChar #"#" = "\\#"
    | mathquoteChar #"^" = "\\hat{\\quad}$"
    | mathQuoteChar #"0" = "{_0}"
    | mathQuoteChar #"1" = "{_1}"
    | mathQuoteChar #"2" = "{_2}"
    | mathQuoteChar #"3" = "{_3}"
    | mathQuoteChar #"4" = "{_4}"
    | mathQuoteChar #"5" = "{_5}"
    | mathQuoteChar #"6" = "{_6}"
    | mathQuoteChar #"7" = "{_7}"
    | mathQuoteChar #"8" = "{_8}"
    | mathQuoteChar #"9" = "{_9}"
    | mathQuoteChar c = String.str c

  fun mathQuote s = String.translate mathQuoteChar s
  *)
let rec strs ("\\Str{" ^ quote s ^ "}",  , size s)let rec evars ("\\EVar{" ^ quote s ^ "}",  , size s)let rec bvars ("\\BVar{" ^ quote s ^ "}",  , size s)let rec consts ("\\Const{" ^ quote s ^ "}",  , size s)let rec labels ("\\Label{" ^ quote s ^ "}",  , size s)let rec skonsts ("\\Skonst{" ^ quote s ^ "}",  , size s)let rec defs ("\\Def{" ^ quote s ^ "}",  , size s)let rec fvars ("\\FVar{" ^ quote s ^ "}",  , size s)let rec sym"->" ("$\\rightarrow$",  , 1) sym"<-" ("$\\leftarrow$",  , 1) sym"{" ("$\\Pi$",  , 1) sym"}" (".",  , 1) sym"[" ("$\\lambda$",  , 1) sym"]" (".",  , 1) sym"type" ("{\\Type}",  , 4) sym"kind" ("{\\Kind}",  , 4) sym"_" ("\\_",  , 1) sym"..." ("$\\ldots$",  , 3) sym"%%" ("%%",  , 2) sym"%skolem" ("%skolem",  , 7) syms (s,  , size s)(* ():.= *)
end