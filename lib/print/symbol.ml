module SymbolAscii () : SYMBOL =
struct

  fun idSize s = (s, String.size s)

  let str = idSize
  let evar = idSize
  let bvar = idSize
  let const = idSize
  let skonst = idSize
  let label = idSize
  let def = idSize
  fun fvar s = idSize ("`" ^ s)
  let sym = idSize

end;; (* functor SymbolAscii *)

module SymbolTeXfp () : SYMBOL =
struct

  (* Illegal constituents: \ _ $ # *)
  (* { } are also special, but cannot occur in identifiers *)
  let rec quoteChar = function #"\\" -> "\\\\"
    | #"_" -> "\\_"
    | #"$" -> "\\$"
    | #"#" -> "\\#"
    | #"'" -> "$'$"            (* not in math mode *)
    | #"<" -> "$<$"            (* not in math mode *)
    | #">" -> "$>$"            (* not in math mode *)
    | #"^" -> "\\^{\\ }"
    | #"0" -> "$_0$"
    | #"1" -> "$_1$"
    | #"2" -> "$_2$"
    | #"3" -> "$_3$"
    | #"4" -> "$_4$"
    | #"5" -> "$_5$"
    | #"6" -> "$_6$"
    | #"7" -> "$_7$"
    | #"8" -> "$_8$"
    | #"9" -> "$_9$"
    | c -> String.str c

  fun quote s = String.translate quoteChar s

  (*
  let rec mathQuoteChar = function #"\\" -> "\\\\"
    | #"_" -> "\\_"
    | #"$" -> "\\$"
    | #"#" -> "\\#"
    | mathquoteChar #"^" = "\\hat{\\quad}$"
    | #"0" -> "{_0}"
    | #"1" -> "{_1}"
    | #"2" -> "{_2}"
    | #"3" -> "{_3}"
    | #"4" -> "{_4}"
    | #"5" -> "{_5}"
    | #"6" -> "{_6}"
    | #"7" -> "{_7}"
    | #"8" -> "{_8}"
    | #"9" -> "{_9}"
    | c -> String.str c

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

  let rec sym = function "->" -> ("$\\rightarrow$", 1)
    | "<-" -> ("$\\leftarrow$", 1)
    | "{" -> ("$\\Pi$", 1)
    | "}" -> (".", 1)
    | "[" -> ("$\\lambda$", 1)
    | "]" -> (".", 1)
    | "type" -> ("{\\Type}", 4)
    | "kind" -> ("{\\Kind}", 4)
    | "_" -> ("\\_", 1)
    | "..." -> ("$\\ldots$", 3)
    | "%%" -> ("%%", 2)              (* itself, for now *)
    | "%skolem" -> ("%skolem", 7)    (* itself, for now *)
    | s -> (s, String.size s)        (* ():.= *)

end;; (* functor SymbolTeX *)


module SymbolTeX () : SYMBOL =
struct

  (* Illegal constituents: \ _ $ # *)
  (* { } are also special, but cannot occur in identifiers *)
  let rec quoteChar = function #"\\" -> "\\\\"
    | #"_" -> "\\_"
    | #"$" -> "\\$"
    | #"#" -> "\\#"
    | #"^" -> "\\^{\\ }"
    | #"0" -> "$_0$"
    | #"1" -> "$_1$"
    | #"2" -> "$_2$"
    | #"3" -> "$_3$"
    | #"4" -> "$_4$"
    | #"5" -> "$_5$"
    | #"6" -> "$_6$"
    | #"7" -> "$_7$"
    | #"8" -> "$_8$"
    | #"9" -> "$_9$"
    | c -> String.str c

  fun quote s = String.translate quoteChar s

  (*
  let rec mathQuoteChar = function #"\\" -> "\\\\"
    | #"_" -> "\\_"
    | #"$" -> "\\$"
    | #"#" -> "\\#"
    | mathquoteChar #"^" = "\\hat{\\quad}$"
    | #"0" -> "{_0}"
    | #"1" -> "{_1}"
    | #"2" -> "{_2}"
    | #"3" -> "{_3}"
    | #"4" -> "{_4}"
    | #"5" -> "{_5}"
    | #"6" -> "{_6}"
    | #"7" -> "{_7}"
    | #"8" -> "{_8}"
    | #"9" -> "{_9}"
    | c -> String.str c

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

  let rec sym = function "->" -> ("$\\rightarrow$", 1)
    | "<-" -> ("$\\leftarrow$", 1)
    | "{" -> ("$\\Pi$", 1)
    | "}" -> (".", 1)
    | "[" -> ("$\\lambda$", 1)
    | "]" -> (".", 1)
    | "type" -> ("{\\Type}", 4)
    | "kind" -> ("{\\Kind}", 4)
    | "_" -> ("\\_", 1)
    | "..." -> ("$\\ldots$", 3)
    | "%%" -> ("%%", 2)              (* itself, for now *)
    | "%skolem" -> ("%skolem", 7)    (* itself, for now *)
    | s -> (s, String.size s)        (* ():.= *)

end;; (* functor SymbolTeXcd *)
