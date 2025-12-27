open Basis

(* Clause Printing *)

(* Author: Frank Pfenning, Carsten Schuermann *)

module type CLAUSEPRINT = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  module Formatter : Formatter.FORMATTER

  val formatClause : IntSyn.dctx * IntSyn.exp -> Formatter.format
  val formatConDec : IntSyn.conDec -> Formatter.format
  val clauseToString : IntSyn.dctx * IntSyn.exp -> string
  val conDecToString : IntSyn.conDec -> string
  val printSgn : unit -> unit
end

(* signature CLAUSEPRINT *)
(* Clause Printing *)

(* Author: Frank Pfenning, Carsten Schuermann *)

(* This is like printing of expressions, except that
   types are programs and therefore
   printed with backward arrows `<-'
*)

module ClausePrint
    (Whnf : Whnf.WHNF)
    (Names : Names.NAMES)
    (Formatter' : Formatter.FORMATTER)
    (Print : Print.PRINT)
    (Symbol : Symbol.SYMBOL) : CLAUSEPRINT = struct
  (*! structure IntSyn = IntSyn' !*)

  module Formatter = Formatter'
  (* some shorthands *)

  module I = IntSyn
  module F = Formatter

  let Str = F.String
  let rec (Str0 (s, n)) = F.string0 n s
  let rec sym s = Str0 (Symbol.sym s)
  let rec parens fmt = F.Hbox [ sym "("; fmt; sym ")" ]
  (* assumes NF *)

  let rec fmtDQuants = function
    | G, I.Pi ((D, I.Maybe), V2) ->
        let D' = Names.decEName (G, D) in
        sym "{"
        :: Print.formatDec (G, D')
        :: sym "}" :: F.Break
        :: fmtDQuants (I.Decl (G, D'), V2)
    | G, I.Pi ((D, I.Meta), V2) ->
        let D' = Names.decEName (G, D) in
        sym "{"
        :: Print.formatDec (G, D')
        :: sym "}" :: F.Break
        :: fmtDQuants (I.Decl (G, D'), V2)
    | G, V -> [ F.HOVbox (fmtDSubGoals (G, V, [])) ]
    | G, V -> [ Print.formatExp (G, V) ]

  and fmtDSubGoals = function
    | G, I.Pi ((D, I.No), V2), acc ->
        fmtDSubGoals
          ( I.Decl (G, D),
            V2,
            F.Break :: sym "<-" :: F.Space :: fmtGparens (G, V1) :: acc )
    | G, V, acc -> parens (F.HVbox (fmtDQuants (G, V))) :: acc
    | G, V, acc -> Print.formatExp (G, V) :: acc

  and fmtDparens = function
    | G, V -> parens (F.HVbox (fmtDQuants (G, V)))
    | G, V -> Print.formatExp (G, V)

  and fmtGparens = function
    | G, V -> parens (F.HVbox (fmtGQuants (G, V)))
    | G, V -> Print.formatExp (G, V)

  and fmtGQuants = function
    | G, I.Pi ((D, I.Maybe), V2) ->
        let D' = Names.decLUName (G, D) in
        sym "{"
        :: Print.formatDec (G, D')
        :: sym "}" :: F.Break
        :: fmtGQuants (I.Decl (G, D'), V2)
    | G, I.Pi ((D, I.Meta), V2) ->
        let D' = Names.decLUName (G, D) in
        sym "{"
        :: Print.formatDec (G, D')
        :: sym "}" :: F.Break
        :: fmtGQuants (I.Decl (G, D'), V2)
    | G, V -> [ F.HOVbox (fmtGHyps (G, V)) ]

  and fmtGHyps = function
    | G, I.Pi ((D, I.No), V2) ->
        fmtDparens (G, V1)
        :: F.Break :: sym "->" :: F.Space
        :: fmtGHyps (I.Decl (G, D), V2)
    | G, V -> [ F.HVbox (fmtGQuants (G, V)) ]
    | G, V -> [ Print.formatExp (G, V) ]

  let rec fmtClause (G, V) = F.HVbox (fmtDQuants (G, V))

  let rec fmtClauseI = function
    | 0, G, V -> fmtClause (G, V)
    | i, G, I.Pi ((D, _), V) ->
        fmtClauseI (i - 1, I.Decl (G, Names.decEName (G, D)), V)

  let rec fmtConDec = function
    | I.ConDec (id, parent, i, _, V, I.Type) ->
        let _ = Names.varReset IntSyn.Null in
        let Vfmt = fmtClauseI (i, I.Null, V) in
        F.HVbox
          [ Str0 (Symbol.const id); F.Space; sym ":"; F.Break; Vfmt; sym "." ]
    | condec -> Print.formatConDec condec

  let rec formatClause (G, V) = fmtClause (G, V)
  let rec formatConDec condec = fmtConDec condec
  let rec clauseToString (G, V) = F.makestring_fmt (formatClause (G, V))
  let rec conDecToString condec = F.makestring_fmt (formatConDec condec)

  let rec printSgn () =
    IntSyn.sgnApp (fun cid ->
        print (conDecToString (IntSyn.sgnLookup cid));
        print "\n")
  (* local ... *)
end

(* functor ClausePrint *)
