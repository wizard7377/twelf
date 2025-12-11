functor SymbolAscii () :> SYMBOL =
struct

  fun idSize s = (s, String.size s)

  val str = idSize
  val evar = idSize
  val bvar = idSize
  val const = idSize
  val skonst = idSize
  val label = idSize
  val def = idSize
  fun fvar s = idSize ("`" ^ s)
  val sym = idSize

end;  (* functor SymbolAscii *)

functor SymbolTeXfp () :> SYMBOL =
struct

  (* Illegal constituents: \ _ $ # *)
  (* { } are also special, but cannot occur in identifiers *)
  fun quoteChar #"\\" = "\\\\"
    | (* GEN CASE BRANCH *) quoteChar #"_" = "\\_"
    | (* GEN CASE BRANCH *) quoteChar #"$" = "\\$"
    | (* GEN CASE BRANCH *) quoteChar #"#" = "\\#"
    | (* GEN CASE BRANCH *) quoteChar #"'" = "$'$"            (* not in math mode *)
    | (* GEN CASE BRANCH *) quoteChar #"<" = "$<$"            (* not in math mode *)
    | (* GEN CASE BRANCH *) quoteChar #">" = "$>$"            (* not in math mode *)
    | (* GEN CASE BRANCH *) quoteChar #"^" = "\\^{\\ }"
    | (* GEN CASE BRANCH *) quoteChar #"0" = "$_0$"
    | (* GEN CASE BRANCH *) quoteChar #"1" = "$_1$"
    | (* GEN CASE BRANCH *) quoteChar #"2" = "$_2$"
    | (* GEN CASE BRANCH *) quoteChar #"3" = "$_3$"
    | (* GEN CASE BRANCH *) quoteChar #"4" = "$_4$"
    | (* GEN CASE BRANCH *) quoteChar #"5" = "$_5$"
    | (* GEN CASE BRANCH *) quoteChar #"6" = "$_6$"
    | (* GEN CASE BRANCH *) quoteChar #"7" = "$_7$"
    | (* GEN CASE BRANCH *) quoteChar #"8" = "$_8$"
    | (* GEN CASE BRANCH *) quoteChar #"9" = "$_9$"
    | (* GEN CASE BRANCH *) quoteChar c = String.str c

  fun quote s = String.translate quoteChar s

  (*
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

  fun str s = ("\\Str{" ^ quote s ^ "}", String.size s)
  fun evar s = ("\\EVar{" ^ quote s ^ "}", String.size s)
  fun bvar s = ("\\BVar{" ^ quote s ^ "}", String.size s)
  fun const s = ("\\Const{" ^ quote s ^ "}", String.size s)
  fun label s = ("\\Label{" ^ quote s ^ "}", String.size s)
  fun skonst s = ("\\Skonst{" ^ quote s ^ "}", String.size s)
  fun def s = ("\\Def{" ^ quote s ^ "}", String.size s)
  fun fvar s = ("\\FVar{" ^ quote s ^ "}", String.size s)

  fun sym "->" = ("$\\rightarrow$", 1)
    | (* GEN CASE BRANCH *) sym "<-" = ("$\\leftarrow$", 1)
    | (* GEN CASE BRANCH *) sym "{" = ("$\\Pi$", 1)
    | (* GEN CASE BRANCH *) sym "}" = (".", 1)
    | (* GEN CASE BRANCH *) sym "[" = ("$\\lambda$", 1)
    | (* GEN CASE BRANCH *) sym "]" = (".", 1)
    | (* GEN CASE BRANCH *) sym "type" = ("{\\Type}", 4)
    | (* GEN CASE BRANCH *) sym "kind" = ("{\\Kind}", 4)
    | (* GEN CASE BRANCH *) sym "_" = ("\\_", 1)
    | (* GEN CASE BRANCH *) sym "..." = ("$\\ldots$", 3)
    | (* GEN CASE BRANCH *) sym "%%" = ("%%", 2)              (* itself, for now *)
    | (* GEN CASE BRANCH *) sym "%skolem" = ("%skolem", 7)    (* itself, for now *)
    | (* GEN CASE BRANCH *) sym s = (s, String.size s)        (* ():.= *)

end;  (* functor SymbolTeX *)


functor SymbolTeX () :> SYMBOL =
struct

  (* Illegal constituents: \ _ $ # *)
  (* { } are also special, but cannot occur in identifiers *)
  fun quoteChar #"\\" = "\\\\"
    | (* GEN CASE BRANCH *) quoteChar #"_" = "\\_"
    | (* GEN CASE BRANCH *) quoteChar #"$" = "\\$"
    | (* GEN CASE BRANCH *) quoteChar #"#" = "\\#"
    | (* GEN CASE BRANCH *) quoteChar #"^" = "\\^{\\ }"
    | (* GEN CASE BRANCH *) quoteChar #"0" = "$_0$"
    | (* GEN CASE BRANCH *) quoteChar #"1" = "$_1$"
    | (* GEN CASE BRANCH *) quoteChar #"2" = "$_2$"
    | (* GEN CASE BRANCH *) quoteChar #"3" = "$_3$"
    | (* GEN CASE BRANCH *) quoteChar #"4" = "$_4$"
    | (* GEN CASE BRANCH *) quoteChar #"5" = "$_5$"
    | (* GEN CASE BRANCH *) quoteChar #"6" = "$_6$"
    | (* GEN CASE BRANCH *) quoteChar #"7" = "$_7$"
    | (* GEN CASE BRANCH *) quoteChar #"8" = "$_8$"
    | (* GEN CASE BRANCH *) quoteChar #"9" = "$_9$"
    | (* GEN CASE BRANCH *) quoteChar c = String.str c

  fun quote s = String.translate quoteChar s

  (*
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

  fun str s = ("\\Str{" ^ quote s ^ "}", String.size s)
  fun evar s = ("\\EVar{" ^ quote s ^ "}", String.size s)
  fun bvar s = ("\\BVar{" ^ quote s ^ "}", String.size s)
  fun const s = ("\\Const{" ^ quote s ^ "}", String.size s)
  fun label s = ("\\Label{" ^ quote s ^ "}", String.size s)
  fun skonst s = ("\\Skonst{" ^ quote s ^ "}", String.size s)
  fun def s = ("\\Def{" ^ quote s ^ "}", String.size s)
  fun fvar s = ("\\FVar{" ^ quote s ^ "}", String.size s)

  fun sym "->" = ("$\\rightarrow$", 1)
    | (* GEN CASE BRANCH *) sym "<-" = ("$\\leftarrow$", 1)
    | (* GEN CASE BRANCH *) sym "{" = ("$\\Pi$", 1)
    | (* GEN CASE BRANCH *) sym "}" = (".", 1)
    | (* GEN CASE BRANCH *) sym "[" = ("$\\lambda$", 1)
    | (* GEN CASE BRANCH *) sym "]" = (".", 1)
    | (* GEN CASE BRANCH *) sym "type" = ("{\\Type}", 4)
    | (* GEN CASE BRANCH *) sym "kind" = ("{\\Kind}", 4)
    | (* GEN CASE BRANCH *) sym "_" = ("\\_", 1)
    | (* GEN CASE BRANCH *) sym "..." = ("$\\ldots$", 3)
    | (* GEN CASE BRANCH *) sym "%%" = ("%%", 2)              (* itself, for now *)
    | (* GEN CASE BRANCH *) sym "%skolem" = ("%skolem", 7)    (* itself, for now *)
    | (* GEN CASE BRANCH *) sym s = (s, String.size s)        (* ():.= *)

end;  (* functor SymbolTeXcd *)
