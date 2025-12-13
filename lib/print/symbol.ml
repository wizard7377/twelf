functor (* GEN BEGIN FUNCTOR DECL *) SymbolAscii () :> SYMBOL =
struct

  fun idSize s = (s, String.size s)

  (* GEN BEGIN TAG OUTSIDE LET *) val str = idSize (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val evar = idSize (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val bvar = idSize (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val const = idSize (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val skonst = idSize (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val label = idSize (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val def = idSize (* GEN END TAG OUTSIDE LET *)
  fun fvar s = idSize ("`" ^ s)
  (* GEN BEGIN TAG OUTSIDE LET *) val sym = idSize (* GEN END TAG OUTSIDE LET *)

end (* GEN END FUNCTOR DECL *);  (* functor SymbolAscii *)

functor (* GEN BEGIN FUNCTOR DECL *) SymbolTeXfp () :> SYMBOL =
struct

  (* Illegal constituents: \ _ $ # *)
  (* { } are also special, but cannot occur in identifiers *)
  fun (* GEN BEGIN FUN FIRST *) quoteChar #"\\" = "\\\\" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"_" = "\\_" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"$" = "\\$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"#" = "\\#" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"'" = "$'$" (* GEN END FUN BRANCH *)            (* not in math mode *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"<" = "$<$" (* GEN END FUN BRANCH *)            (* not in math mode *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #">" = "$>$" (* GEN END FUN BRANCH *)            (* not in math mode *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"^" = "\\^{\\ }" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"0" = "$_0$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"1" = "$_1$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"2" = "$_2$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"3" = "$_3$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"4" = "$_4$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"5" = "$_5$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"6" = "$_6$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"7" = "$_7$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"8" = "$_8$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"9" = "$_9$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar c = String.str c (* GEN END FUN BRANCH *)

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

  fun (* GEN BEGIN FUN FIRST *) sym "->" = ("$\\rightarrow$", 1) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) sym "<-" = ("$\\leftarrow$", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "{" = ("$\\Pi$", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "}" = (".", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "[" = ("$\\lambda$", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "]" = (".", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "type" = ("{\\Type}", 4) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "kind" = ("{\\Kind}", 4) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "_" = ("\\_", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "..." = ("$\\ldots$", 3) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "%%" = ("%%", 2) (* GEN END FUN BRANCH *)              (* itself, for now *)
    | (* GEN BEGIN FUN BRANCH *) sym "%skolem" = ("%skolem", 7) (* GEN END FUN BRANCH *)    (* itself, for now *)
    | (* GEN BEGIN FUN BRANCH *) sym s = (s, String.size s) (* GEN END FUN BRANCH *)        (* ():.= *)

end (* GEN END FUNCTOR DECL *);  (* functor SymbolTeX *)


functor (* GEN BEGIN FUNCTOR DECL *) SymbolTeX () :> SYMBOL =
struct

  (* Illegal constituents: \ _ $ # *)
  (* { } are also special, but cannot occur in identifiers *)
  fun (* GEN BEGIN FUN FIRST *) quoteChar #"\\" = "\\\\" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"_" = "\\_" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"$" = "\\$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"#" = "\\#" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"^" = "\\^{\\ }" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"0" = "$_0$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"1" = "$_1$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"2" = "$_2$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"3" = "$_3$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"4" = "$_4$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"5" = "$_5$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"6" = "$_6$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"7" = "$_7$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"8" = "$_8$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar #"9" = "$_9$" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) quoteChar c = String.str c (* GEN END FUN BRANCH *)

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

  fun (* GEN BEGIN FUN FIRST *) sym "->" = ("$\\rightarrow$", 1) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) sym "<-" = ("$\\leftarrow$", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "{" = ("$\\Pi$", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "}" = (".", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "[" = ("$\\lambda$", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "]" = (".", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "type" = ("{\\Type}", 4) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "kind" = ("{\\Kind}", 4) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "_" = ("\\_", 1) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "..." = ("$\\ldots$", 3) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) sym "%%" = ("%%", 2) (* GEN END FUN BRANCH *)              (* itself, for now *)
    | (* GEN BEGIN FUN BRANCH *) sym "%skolem" = ("%skolem", 7) (* GEN END FUN BRANCH *)    (* itself, for now *)
    | (* GEN BEGIN FUN BRANCH *) sym s = (s, String.size s) (* GEN END FUN BRANCH *)        (* ():.= *)

end (* GEN END FUNCTOR DECL *);  (* functor SymbolTeXcd *)
