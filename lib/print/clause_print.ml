(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* This is like printing of expressions, except that
   types are interpreted as programs and therefore
   printed with backward arrows `<-'
*)

functor (* GEN BEGIN FUNCTOR DECL *) ClausePrint
  ((*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Formatter' : FORMATTER
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
     sharing Print.Formatter = Formatter'
   structure Symbol : SYMBOL)
     : CLAUSEPRINT =
struct

  (*! structure IntSyn = IntSyn' !*)
structure Formatter = Formatter'

local
  (* some shorthands *)
  structure I = IntSyn
  structure F = Formatter
  (* GEN BEGIN TAG OUTSIDE LET *) val Str = F.String (* GEN END TAG OUTSIDE LET *)
  fun Str0 (s, n) = F.String0 n s
  fun sym (s) = Str0 (Symbol.sym s)

  fun parens (fmt) = F.Hbox [sym "(", fmt, sym ")"]

  (* assumes NF *)
  fun (* GEN BEGIN FUN FIRST *) fmtDQuants (G, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decEName (G, D) (* GEN END TAG OUTSIDE LET *)
      in
        sym "{" :: Print.formatDec (G, D') :: sym "}" :: F.Break
        :: fmtDQuants (I.Decl (G, D'), V2)
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtDQuants (G, I.Pi ((D as I.Dec (_, V1), I.Meta), V2)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decEName (G, D) (* GEN END TAG OUTSIDE LET *)
      in
        sym "{" :: Print.formatDec (G, D') :: sym "}" :: F.Break
        :: fmtDQuants (I.Decl (G, D'), V2)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtDQuants (G, V as I.Pi _) = (* P = I.No *)
        [F.HOVbox (fmtDSubGoals (G, V, nil))] (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtDQuants (G, V) = (* V = Root _ *)
        [Print.formatExp (G, V)] (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) fmtDSubGoals (G, I.Pi ((D as I.Dec (_, V1), I.No), V2), acc) =
        fmtDSubGoals (I.Decl (G, D), V2,
                      F.Break :: sym "<-" :: F.Space :: fmtGparens (G, V1)
                      :: acc) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtDSubGoals (G, V as I.Pi _, acc) = (* acc <> nil *)
        parens (F.HVbox (fmtDQuants (G, V))) :: acc (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtDSubGoals (G, V, acc) = (* V = Root _ *)
        Print.formatExp (G, V) :: acc (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) fmtDparens (G, V as I.Pi _) = parens (F.HVbox (fmtDQuants (G, V))) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtDparens (G, V) = (* V = Root _ *)
        Print.formatExp (G, V) (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) fmtGparens (G, V as I.Pi _) = parens (F.HVbox (fmtGQuants (G, V))) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtGparens (G, V) = (* V = Root _ *)
        Print.formatExp (G, V) (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) fmtGQuants (G, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, D) (* GEN END TAG OUTSIDE LET *)
      in
        sym "{" :: Print.formatDec (G, D') :: sym "}" :: F.Break
        :: fmtGQuants (I.Decl (G, D'), V2)
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtGQuants (G, I.Pi ((D as I.Dec (_, V1), I.Meta), V2)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, D) (* GEN END TAG OUTSIDE LET *)
      in
        sym "{" :: Print.formatDec (G, D') :: sym "}" :: F.Break
        :: fmtGQuants (I.Decl (G, D'), V2)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtGQuants (G, V) = (* P = I.No or V = Root _ *)
        [F.HOVbox (fmtGHyps (G, V))] (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) fmtGHyps (G, I.Pi ((D as I.Dec (_, V1), I.No), V2)) =
        fmtDparens (G, V1) :: F.Break :: sym "->" :: F.Space :: fmtGHyps (I.Decl (G, D), V2) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtGHyps (G, V as I.Pi _) = (* P = I.Maybe *)
        [F.HVbox (fmtGQuants (G, V))] (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) fmtGHyps (G, V) = (* V = Root _ *)
        [Print.formatExp (G, V)] (* GEN END FUN BRANCH *)

  fun fmtClause (G, V) = F.HVbox (fmtDQuants (G, V))

  fun (* GEN BEGIN FUN FIRST *) fmtClauseI (0, G, V) = fmtClause (G, V) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtClauseI (i, G, I.Pi ((D, _), V)) =
        fmtClauseI (i-1, I.Decl (G, Names.decEName (G, D)), V) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) fmtConDec (I.ConDec (id, parent, i, _, V, I.Type)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Vfmt = fmtClauseI (i, I.Null, V) (* GEN END TAG OUTSIDE LET *)
      in
        F.HVbox [Str0 (Symbol.const (id)), F.Space, sym ":", F.Break,
                 Vfmt, sym "."]
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) fmtConDec (condec) =
      (* type family declaration, definition, or Skolem constant *)
      Print.formatConDec (condec) (* GEN END FUN BRANCH *)

in

  fun formatClause (G, V) = fmtClause (G, V)
  fun formatConDec (condec) = fmtConDec (condec)

  fun clauseToString (G, V) = F.makestring_fmt (formatClause (G, V))
  fun conDecToString (condec) = F.makestring_fmt (formatConDec (condec))

  fun printSgn () =
      IntSyn.sgnApp ((* GEN BEGIN FUNCTION EXPRESSION *) fn (cid) => (print (conDecToString (IntSyn.sgnLookup cid)); print "\n") (* GEN END FUNCTION EXPRESSION *))
end  (* local ... *)

end (* GEN END FUNCTOR DECL *)  (* functor ClausePrint *)
