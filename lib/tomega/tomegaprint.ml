(* Printing of functional proof terms *)


(* Author: Carsten Schuermann *)


module TomegaPrint (Formatter : FORMATTER) (Names : NAMES) (Print : PRINT) : TOMEGAPRINT = struct (*! structure IntSyn = IntSyn' !*)

(*! structure Tomega = Tomega' !*)

module Formatter = Formatter
exception Error of string
(* is just here because we don't have a
     module yet for_sml names. move later
     --cs Tue Apr 27 12:04:45 2004 *)

module I = IntSyn
module T = Tomega
module Fmt = Formatter
module P = Print
(* Invariant:

       The proof term must satisfy the following conditions:
       * proof term must have the structure
           Rec.     Lam ... Lam Case
                And Lam ... Lam Case
                ...
                And Lam ... Lam Case
         and the body of every case must be of the form
           (Let Decs in Case ...
           or
           Inx ... Inx Unit) *
         where Decs are always of the form
           New ... New App .. App Split .. Split Empty
     *)

let evarList : T.prg list ref = ref []
let rec evarReset ()  = (evarList := [])
let rec evarName n  = ( let rec evarName' = function [] -> raise (Error "not found") | ((Y) :: L) -> if Names.evarName (G, X) = n then Y else evarName' L in  evarName' (! evarList) )
let rec nameEVar (T.EVar (_, _, _, _, _, X))  = Names.evarName (G, X)
(* formatCtxBlock (G, (G1, s1)) = (G', s', fmts')

       Invariant:
       If   |- G ctx
       and  G |- G1 ctx
       and  G2 |- s1 : G
       then G' = G2, G1 [s1]
       and  G' |- s' : G, G1
       and  fmts is a format list of G1[s1]
    *)

let rec formatCtxBlock = function (G, (I.Null, s)) -> (G, s, []) | (G, (I.Decl (I.Null, D), s)) -> ( let D' = I.decSub (D, s) in let fmt = P.formatDec (G, D') in  (I.Decl (G, D'), I.dot1 s, [fmt]) ) | (G, (I.Decl (G', D), s)) -> ( let (G'', s'', fmts) = formatCtxBlock (G, (G', s)) in let D'' = I.decSub (D, s'') in let fmt = P.formatDec (G'', D'') in  (I.Decl (G'', D''), I.dot1 s'', fmts @ [Fmt.String ","; Fmt.Break; fmt]) )
let rec constName c  = I.conDecName (I.sgnLookup c)
let rec formatWorld = function [] -> [] | [c] -> [Fmt.String (constName c)] | (c :: cids) -> [Fmt.String (constName c); Fmt.String ","; Fmt.Break] @ formatWorld cids
(* formatFor' (G, (F, s)) = fmts'

       Invariant:
       If   |- G ctx
       and  G |- s : Psi'
       and  Psi' |- F formula
       then fmts' is a list of formats for_sml F
    *)

let rec formatFor' = function (Psi, T.All ((D, T.Explicit), F)) -> (match D with T.UDec D -> ( let G = T.coerceCtx Psi in let D' = Names.decName (G, D) in  [Fmt.String "all {"; P.formatDec (G, D'); Fmt.String "}"; Fmt.Break] @ formatFor' (I.Decl (Psi, T.UDec D'), F) )) | (Psi, T.All ((D, T.Implicit), F)) -> (match D with T.UDec D -> ( let G = T.coerceCtx Psi in let D' = Names.decName (G, D) in  [Fmt.String "all^ {"; P.formatDec (G, D'); Fmt.String "}"; Fmt.Break] @ formatFor' (I.Decl (Psi, T.UDec D'), F) )) | (Psi, T.Ex ((D, T.Explicit), F)) -> ( let G = T.coerceCtx Psi in let D' = Names.decName (G, D) in  [Fmt.String "exists {"; P.formatDec (G, D'); Fmt.String "}"; Fmt.Break] @ formatFor' (I.Decl (Psi, T.UDec D'), F) ) | (Psi, T.Ex ((D, T.Implicit), F)) -> ( let G = T.coerceCtx Psi in let D' = Names.decName (G, D) in  [Fmt.String "exists^ {"; P.formatDec (G, D'); Fmt.String "}"; Fmt.Break] @ formatFor' (I.Decl (Psi, T.UDec D'), F) ) | (Psi, T.And (F1, F2)) -> [Fmt.String "("; Fmt.HVbox (formatFor' (Psi, F1)); Fmt.String ")"; Fmt.Break; Fmt.String "/\\"; Fmt.Space; Fmt.String "("; Fmt.HVbox (formatFor' (Psi, F2)); Fmt.String ")"] | (Psi, T.True) -> [Fmt.String "true"] | (Psi, T.World (T.Worlds L, F)) -> [Fmt.String "world ("; Fmt.HVbox (formatWorld L); Fmt.String ")"; Fmt.Break] @ formatFor' (Psi, F)
let rec formatFor (G, F)  = Fmt.HVbox (formatFor' (G, T.forSub (F, T.id)))
let rec forToString (Psi, F)  = Fmt.makestring_fmt (formatFor (Psi, F))
(* formatPrg (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *)

(*      fun nameLookup index = List.nth (names, index) *)

(* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *)

let rec decName = function (G, T.UDec D) -> T.UDec (Names.decName (G, D)) | (G, T.PDec (None, F, TC1, TC2)) -> T.PDec (Some "xx", F, TC1, TC2) | (G, D) -> D
(*      (* numberOfSplits Ds = n'

           Invariant:
           If   Psi, Delta |- Ds :: Psi', Delta'
           then n'= |Psi'| - |Psi|
        *)
        fun numberOfSplits Ds =
            let
              fun numberOfSplits' (T.Empty, n) = n
                | numberOfSplits' (T.New (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.App (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Lemma (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Split (_, Ds), n) = numberOfSplits' (Ds, n+1)
                | numberOfSplits' (T.Left (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Right (_, Ds), n) = numberOfSplits' (Ds, n)
            in
              numberOfSplits' (Ds, 0)
            end
*)

(* psiName (Psi1, s, Psi2, l) = Psi1'

           Invariant:
           If   |- Psi1 ctx
           and  |- Psi1' ctx
           and  |- Psi2 ctx
           and  Psi2 = Psi2', Psi2''
           and  Psi1 |- s : Psi2
           and  |Psi2''| = l
           then Psi1' = Psi1 modulo variable naming
           and  for_sml all x in Psi2 s.t. s(x) = x in Psi1'
        *)

let rec psiName (Psi1, s, Psi2, l)  = ( let rec nameDec = function (D, name) -> D | (I.Dec (None, V), name) -> I.Dec (Some name, V) in let rec namePsi = function (I.Decl (Psi, T.UDec D), 1, name) -> I.Decl (Psi, T.UDec (nameDec (D, name))) | (I.Decl (Psi, LD), n, name) -> I.Decl (namePsi (Psi, n - 1, name), LD)
and nameG = function (Psi, I.Null, n, name, k) -> (k n, I.Null) | (Psi, I.Decl (G, D), 1, name, k) -> (Psi, I.Decl (G, nameDec (D, name))) | (Psi, I.Decl (G, D), n, name, k) -> ( let (Psi', G') = nameG (Psi, G, n - 1, name, k) in  (Psi', I.Decl (G', D)) ) in let rec ignore = function (s, 0) -> s | (T.Dot (_, s), k) -> ignore (s, k - 1) | (T.Shift n, k) -> ignore (T.Dot (T.Idx (n + 1), T.Shift (n + 1)), k - 1) in let rec copyNames = function ((T.Shift n, G), Psi1) -> copyNames (T.Dot (T.Idx (n + 1), T.Shift (n + 1)), G) Psi1 | ((T.Dot (T.Exp _, s), I.Decl (G, _)), Psi1) -> copyNames (s, G) Psi1 | ((T.Dot (T.Idx k, s), I.Decl (G, T.UDec (I.Dec (None, _)))), Psi1) -> copyNames (s, G) Psi1 | ((T.Dot (T.Idx k, s), I.Decl (G, T.UDec (I.Dec (Some name, _)))), Psi1) -> ( let Psi1' = namePsi (Psi1, k, name) in  copyNames (s, G) Psi1' ) | ((T.Dot (T.Prg k, s), I.Decl (G, T.PDec (None, _, _, _))), Psi1) -> copyNames (s, G) Psi1 | ((T.Dot (T.Prg k, s), I.Decl (G, T.PDec (Some name, _, _, _))), Psi1) -> copyNames (s, G) Psi1 | ((T.Shift _, I.Null), Psi1) -> Psi1 in let rec psiName' = function (I.Null) -> I.Null | (I.Decl (Psi, D)) -> ( let Psi' = psiName' Psi in  I.Decl (Psi', decName (T.coerceCtx Psi', D)) ) in  psiName' ((* copyNames  (ignore (s, l),  Psi2) *)
Psi1) )
(*

        (* merge (G1, G2) = G'

           Invariant:
           G' = G1, G2
        *)
        fun merge (G1, I.Null) = G1
          | merge (G1, I.Decl (G2, D)) =
              I.Decl (merge (G1, G2), D)

        (* formatCtx (Psi, G) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- G ctx
           then fmt' is a pretty print format of G
        *)
        fun formatCtx (Psi, G) =
          let
            val G0 = T.makectx Psi

            fun formatCtx' (I.Null) = nil
              | formatCtx' (I.Decl (I.Null, I.Dec (SOME name, V))) =
                  [Fmt.String name, Fmt.String ":",
                   Print.formatExp (G0, V)]
              | formatCtx' (I.Decl (G, I.Dec (SOME name, V))) =
                  (formatCtx' G) @
                  [Fmt.String ",", Fmt.Break,
                   Fmt.String name, Fmt.String ":",
                   Print.formatExp (merge (G0, G), V)]
          in
            Fmt.Hbox (Fmt.String "|" :: (formatCtx' G @ [Fmt.String "|"]))
          end

        (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
        fun formatTuple (Psi, P) =
          let
            fun formatTuple' (T.Unit) = nil
              | formatTuple' (T.Inx (M, T.Unit)) =
              [Print.formatExp (T.makectx Psi, M)]
              | formatTuple' (T.Inx (M, P')) =
              (Print.formatExp (T.makectx Psi, M) ::
               Fmt.String "," :: Fmt.Break :: formatTuple' P')
          in
            case P
              of (T.Inx (_, T.Unit)) => Fmt.Hbox (formatTuple' P)
              | _ => Fmt.HVbox0 1 1 1
                (Fmt.String "(" :: (formatTuple' P @ [Fmt.String ")"]))
          end

        (* formatSplitArgs (Psi, L) = fmt'

           Invariant:
           If   |- Psi ctx
           and  L = (M1, .., Mn)
           and  Psi |- Mk:Ak for_sml all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
        fun formatSplitArgs (Psi, L) =
          let
            fun formatSplitArgs' (nil) = nil
              | formatSplitArgs' (M :: nil) =
                  [Print.formatExp (T.makectx Psi, M)]
              | formatSplitArgs' (M :: L) =
                  (Print.formatExp (T.makectx Psi, M) ::
                   Fmt.String "," :: Fmt.Break :: formatSplitArgs' L)
          in
            if List.length L = 1 then Fmt.Hbox (formatSplitArgs' L)
            else Fmt.HVbox0 1 1 1
              (Fmt.String "(" :: (formatSplitArgs' L @ [Fmt.String ")"]))
          end


        (* formatDecs1 (Psi, Ds, s, L) = L'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi' = x1:A1 .. xn:An
           and  Psi'' |- s : Psi
           and  for_sml i<=n
                L = (M1 .. Mi)
                s.t   Psi'' |- Mi : Ai
           then L' extends L
           s.t. L = (M1 .. Mn)
                for_sml all i <=n
                Psi'' |- Mi : Ai
                (and Mi is a splitting of a the result of an inductive call)
        *)
        fun formatDecs1 (Psi, T.Split (xx, Ds), I.Dot (Ft, s1), L) =
              formatDecs1 (Psi, Ds, s1, frontToExp (Ft) :: L)
          | formatDecs1 (Psi, T.Empty, s1, L) = L
          | formatDecs1 (Psi, Ds, I.Shift n, L) =
              formatDecs1 (Psi, Ds, I.Dot (I.Idx (n+1), I.Shift (n+1)), L)


        (* formatDecs0 (Psi, Ds) = (Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- Ds : Psi', Delta'
           and  Ds = App M1 ... App Mn Ds'   (where Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- Ds' : Psi1', Delta1'
                (for_sml some Psi1, Delta1, Psi1', Delta1')
        *)
        fun formatDecs0 (Psi, T.App ((xx, M), Ds)) =
            let
              val (Ds', S) =
                formatDecs0 (Psi, Ds)
            in
              (Ds', I.App (M, S))
            end
          | formatDecs0 (Psi, Ds) = (Ds, I.Nil)


        (* formatDecs (index, Psi, Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of Ds
        *)
        fun formatDecs (index, Psi, T.App ((xx, _), P), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val name = nameLookup index
            in
              Fmt.Hbox [formatSplitArgs (Psi1, L'), Fmt.Space,
                        Fmt.String "=", Fmt.Break,
                        Fmt.HVbox (Fmt.String name :: Fmt.Break ::
                                   Print.formatSpine callname (T.makectx Psi, S))]
            end
          | formatDecs (index, Psi, T.New (T.CtxBlock (_, G), Ds),
                        (Psi1, s1)) =
            let
              val B' = ctxBlockName (T.makectx Psi, B)
              val fmt =
                formatDecs (index, I.Decl (Psi, T.Block B'), Ds, (Psi1, s1))
            in
              Fmt.Vbox [formatCtx (Psi, G), Fmt.Break, fmt]
            end
          | formatDecs (index, Psi, T.Lemma (lemma, Ds), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val (T.LemmaDec (names, _, _)) = T.lemmaLookup lemma
            in
              Fmt.Hbox [formatSplitArgs (Psi1, L'), Fmt.Space,
                        Fmt.String "=", Fmt.Break,
                        Fmt.HVbox (Fmt.String (List.nth (names, index)) :: Fmt.Break ::
                                   Print.formatSpine callname (T.makectx Psi, S))]
            end
          | formatDecs (index, Psi, T.Left (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index, Psi, Ds, (Psi1, s1))
            in
              fmt
            end
          | formatDecs (index, Psi, T.Right (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index+1, Psi, Ds, (Psi1, s1))
            in
              fmt
            end


*)

(* fmtSpine callname (G, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)

let rec fmtSpine = function (callname, (Psi, T.Nil)) -> [] | (callname, (Psi, T.AppExp (U, S))) -> Fmt.HVbox (Print.formatSpine (T.coerceCtx Psi, I.App (U, I.Nil))) :: fmtSpine' callname (Psi, S) | (callname, (Psi, T.AppPrg (P, S))) -> formatPrg3 callname (Psi, P) :: fmtSpine' callname (Psi, S)
and fmtSpine' = function (callname, (Psi, T.Nil)) -> [] | (callname, (Psi, S)) -> Fmt.Break :: fmtSpine callname (Psi, S)
and argsToSpine = function (s, 0, S) -> S | (T.Shift (n), k, S) -> argsToSpine (T.Dot (T.Idx (n + 1), T.Shift (n + 1)), k, S) | (T.Dot (T.Idx n, s), k, S) -> argsToSpine (s, k - 1, T.AppExp (I.Root (I.BVar n, I.Nil), S)) | (T.Dot (T.Exp (U), s), k, S) -> argsToSpine (s, k - 1, T.AppExp (U, S)) | (T.Dot (T.Prg P, s), k, S) -> argsToSpine (s, k - 1, T.AppPrg (P, S))
and formatTuple (Psi, P)  = ( let rec formatTuple' = function (T.Unit) -> [] | (T.PairExp (M, T.Unit)) -> [Print.formatExp (T.coerceCtx Psi, M)] | (T.PairExp (M, P')) -> (Print.formatExp (T.coerceCtx Psi, M) :: Fmt.String "," :: Fmt.Break :: formatTuple' P') in  match P with (T.PairExp (_, T.Unit)) -> Fmt.Hbox (formatTuple' P) | _ -> Fmt.HVbox0 1 1 1 (Fmt.String "(" :: (formatTuple' P @ [Fmt.String ")"])) )
and formatRedex = function (callname, (Psi, T.Var k, S)) -> ( let T.PDec (Some name, _, _, _) = I.ctxLookup (Psi, k) in let Fspine = fmtSpine callname (Psi, S) in  Fmt.Hbox [Fmt.Space; Fmt.HVbox (Fmt.String name :: Fmt.Break :: Fspine)] ) | (callname, (Psi, T.Const l, S)) -> ( let T.ValDec (name, _, _) = T.lemmaLookup l in let Fspine = fmtSpine callname (Psi, S) in  Fmt.Hbox [Fmt.Space; Fmt.HVbox (Fmt.String name :: Fmt.Break :: Fspine)] ) | (callname, (Psi, (T.Redex (T.Const l, _)), S)) -> ( (* val T.ValDec (name, _, _) = T.lemmaLookup l *)
let name = callname l in let Fspine = fmtSpine callname (Psi, S) in  Fmt.Hbox [Fmt.Space; Fmt.HVbox (Fmt.String name :: Fmt.Break :: Fspine)] )
and formatCase callname (max, Psi', s, Psi)  = ( let S = argsToSpine (s, I.ctxLength Psi - max, T.Nil) in let Fspine = fmtSpine callname (Psi', S) in  Fmt.Hbox [Fmt.HVbox (Fspine)] )
and formatCases = function (max, Psi, [], callname) -> [] | (max, Psi, (Psi', s, P) :: [], callname) -> ( let Psi'' = psiName (Psi', s, Psi, 0) in let _ = Names.varReset I.Null in  [Fmt.HVbox0 1 5 1 [formatCase callname (max, Psi'', s, Psi); Fmt.Space; Fmt.String "="; Fmt.Break; formatPrg3 callname (Psi'', P)]; Fmt.Break] ) | (max, Psi, (Psi', s, P) :: O, callname) -> ( let Psi'' = psiName (Psi', s, Psi, 0) in let _ = Names.varReset I.Null in  formatCases (max, Psi, O, callname) @ [Fmt.HVbox0 1 5 1 [Fmt.String "|"; Fmt.Space; formatCase callname (max, Psi'', s, Psi); Fmt.Space; Fmt.String "="; Fmt.Break; formatPrg3 callname (Psi'', P)]; Fmt.Break] )
and formatPrg3 = function (callname, (Psi, T.Unit)) -> Fmt.String "<>" | (callname, (Psi, T.PairExp (U, P))) -> Fmt.HVbox [Fmt.String "<"; Print.formatExp (T.coerceCtx Psi, U); Fmt.String ","; Fmt.Break; formatPrg3 callname (Psi, P); Fmt.String ">"] | (callname, (Psi, P)) -> formatLet callname (Psi, P, []) | (callname, (Psi, P)) -> formatLet callname (Psi, P, []) | (callname, (Psi, P)) -> formatLet callname (Psi, P, []) | (callname, (Psi, P)) -> formatNew callname (Psi, P, []) | (callname, (Psi, T.Redex (P, S))) -> formatRedex callname (Psi, P, S) | (callname, (Psi, T.Lam (D, P))) -> Fmt.HVbox [Fmt.String "lam"; Fmt.Space; Fmt.String "("; Print.formatDec (T.coerceCtx Psi, D'); Fmt.String ")"; Fmt.Space; formatPrg3 callname (I.Decl (Psi, D), P)] | (callname, (Psi, T.Rec (D, P))) -> Fmt.HVbox [Fmt.String "fix*"; Fmt.Space; Fmt.String "("; Fmt.String name; Fmt.String ":"; formatFor (Psi, F); Fmt.String ")"; Fmt.Space; formatPrg3 callname (I.Decl (Psi, D), P)] | (callname, (Psi, T.Rec (D, P))) -> Fmt.HVbox [Fmt.String "fix"; Fmt.Space; Fmt.String "("; Fmt.String name; Fmt.String ":"; formatFor (Psi, F); Fmt.String ")"; Fmt.Space; formatPrg3 callname (I.Decl (Psi, D), P)] | (callname, (Psi, T.PClo (P, t))) -> Fmt.HVbox [formatPrg3 callname (Psi, P); Fmt.String "..."] | (callname, (Psi, X)) -> formatPrg3 callname (Psi, P) | (callname, (Psi, X)) -> Fmt.String (nameEVar X) | (callname, (Psi, T.Case (T.Cases Cs))) -> Fmt.HVbox (Fmt.String "case" :: Fmt.Break :: formatCases (1, Psi, Cs, callname) @ [Fmt.String "."]) | (callname, (Psi, T.Var n)) -> ( let T.PDec (Some n, _, _, _) = I.ctxLookup (Psi, n) in  Fmt.String n ) | (callname, _) -> Fmt.String "missing case"
and formatNew = function (callname, (Psi, T.New (T.Lam (T.UDec (D), P)), fmts)) -> ( let G = T.coerceCtx Psi in let D' = Names.decName (G, D) in  formatNew callname (I.Decl (Psi, T.UDec D'), P, Fmt.Break :: Fmt.HVbox [Print.formatDec (G, D')] :: fmts) ) | (callname, (Psi, P, fmts)) -> Fmt.Vbox0 0 1 ([Fmt.String "new"; Fmt.Vbox0 0 1 (fmts); Fmt.Break; Fmt.String "in"; Fmt.Break; Fmt.Spaces 2; formatPrg3 callname (Psi, P); Fmt.Break; Fmt.String "end"])
and formatLet = function (callname, (Psi, T.Let (D, P1, T.Case (T.Cases ((Psi1, s1, P2) :: []))), fmts)) -> ( (* was I.ctxLength Psi - max  --cs *)
(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
let Psi1' = psiName (Psi1, s1, Psi, 1) in let F1 = Fmt.HVbox [formatPrg3 callname (Psi, P1)] in let S = argsToSpine (s1, 1, T.Nil) in let Fspine = fmtSpine callname (Psi1, S) in let Fpattern = Fmt.HVbox [Fmt.Hbox (Fspine)] in let Fbody = Fmt.HVbox [F1] in let fmt = Fmt.HVbox [Fmt.HVbox [Fmt.String "val"; Fmt.Space; Fpattern; Fmt.Space; Fmt.String "="]; Fmt.Break; Fbody] in  formatLet callname (Psi1', P2, fmts @ [Fmt.Break; fmt]) ) | (callname, (Psi, T.Let (D, P1, T.Case (T.Cases ((Psi1, s1, P2) :: []))), fmts)) -> ( (* was I.ctxLength Psi - max  --cs *)
(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *)
(*            val fmt = (* formatDecs (0, Psi, Ds, (Psi1', s1)) *)
                Fmt.Hbox [Fmt.String " ..." , Fmt.Space, Fmt.String "=",  Fmt.Break, F1] *)
let Psi1' = psiName (Psi1, s1, Psi, 1) in let F1 = Fmt.HVbox [formatPrg3 callname (Psi, P1)] in let S = argsToSpine (s1, 1, T.Nil) in let Fspine = fmtSpine callname (Psi1, S) in let Fpattern = Fmt.HVbox [Fmt.Hbox (Fspine)] in let Fbody = Fmt.HVbox [F1] in let fmt = Fmt.HVbox [Fmt.HVbox [Fmt.String "val"; Fmt.Space; Fpattern; Fmt.Space; Fmt.String "="]; Fmt.Break; Fbody] in  Fmt.Vbox0 0 1 ([Fmt.String "let"; Fmt.Vbox0 2 1 (fmts @ [Fmt.Break; fmt]); Fmt.Break; Fmt.String "in"; Fmt.Break; Fmt.Spaces 2; formatPrg3 callname (Psi1', P2); Fmt.Break; Fmt.String "end"]) ) | (callname, (Psi, T.Let (D, P1, T.Case (T.Cases L)), [])) -> ( let rec fmtCaseRest = function [] -> [] | ((Psi1, s1, P2) :: L) -> ( let Psi1' = psiName (Psi1, s1, Psi, 1) in let S = argsToSpine (s1, 1, T.Nil) in let Fspine = fmtSpine callname (Psi1, S) in let Fpattern = Fmt.HVbox [Fmt.Hbox (Fspine)] in  [Fmt.HVbox [Fmt.Space; Fmt.String "|"; Fmt.Space; Fpattern; Fmt.Space; Fmt.String "-->"]; Fmt.Spaces 2; Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', P2)]; Fmt.Break] @ fmtCaseRest (L) ) in let rec fmtCase ((Psi1, s1, P2) :: L)  = ( let Psi1' = psiName (Psi1, s1, Psi, 1) in let S = argsToSpine (s1, 1, T.Nil) in let Fspine = fmtSpine callname (Psi1, S) in let Fpattern = Fmt.HVbox [Fmt.Hbox (Fspine)] in  Fmt.Vbox0 0 1 ([Fmt.HVbox [Fmt.String "of"; Fmt.Space; Fpattern; Fmt.Space; Fmt.String "-->"]; Fmt.Spaces 2; Fmt.Vbox0 0 1 [formatPrg3 callname (Psi1', P2)]; Fmt.Break] @ fmtCaseRest (L)) ) in let F1 = Fmt.HVbox [formatPrg3 callname (Psi, P1)] in let Fbody = Fmt.HVbox [F1] in let fmt = fmtCase (L) in  Fmt.Vbox0 0 1 ([Fmt.String "case ("; Fbody; Fmt.Space(* need space since there is one before Fbody *)
; Fmt.String ")"; Fmt.Break; fmt]) ) | (callname, (Psi, R, fmts)) -> Fmt.Vbox0 0 1 ([Fmt.String "let"; Fmt.Vbox0 0 1 (fmts @ [Fmt.Break]); Fmt.Break; Fmt.String "in"; Fmt.Break; Fmt.Spaces 2; formatLet callname (Psi, R, []); Fmt.Break; Fmt.String "end"]) | (callname, (Psi, R, fmts)) -> Fmt.Vbox0 0 1 ([Fmt.String "let"; Fmt.Break; Fmt.Vbox0 0 1 ([Fmt.String name; Fmt.Space; Fmt.String "="; formatPrg3 callname (Psi, P1)]); Fmt.Break; Fmt.String "in"; Fmt.Break; Fmt.Spaces 2; formatPrg3 callname (I.Decl (Psi, D), P2); Fmt.Break; Fmt.String "end"]) | (callname, (Psi, R, fmts)) -> Fmt.Vbox0 0 1 ([Fmt.String "let"; Fmt.Break; Fmt.Spaces 2; Fmt.Vbox0 0 1 ([Fmt.String "("; Fmt.String n1; Fmt.String ","; Fmt.Space; Fmt.String n2; Fmt.String ")"; Fmt.Space; Fmt.String "="; Fmt.Space; formatPrg3 callname (Psi, P1)]); Fmt.Break; Fmt.String "in"; Fmt.Break; Fmt.Spaces 2; formatPrg3 callname (I.Decl (I.Decl (Psi, T.UDec D1), D2), P2); Fmt.Break; Fmt.String "end"]) | (callname, (Psi, R, fmts)) -> Fmt.Vbox0 0 1 ([Fmt.String "let"; Fmt.Break; Fmt.Spaces 2; Fmt.Vbox0 0 1 ([Fmt.String "()"; Fmt.Space; Fmt.String "="; Fmt.Space; formatPrg3 callname (Psi, P1)]); Fmt.Break; Fmt.String "in"; Fmt.Break; Fmt.Spaces 2; formatPrg3 callname (Psi, P2); Fmt.Break; Fmt.String "end"])
and formatHead callname (name, (max, index), Psi', s, Psi)  = ( (*            val T.PDec (SOME name, _) = I.ctxLookup (Psi, index) *)
(*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi', S) *)
let S = argsToSpine (s, I.ctxLength Psi - max, T.Nil) in let Fspine = fmtSpine callname (Psi', S) in  Fmt.Hbox [Fmt.Space; Fmt.HVbox (Fmt.String name :: Fmt.Break :: Fspine)] )
(* formatPrg2 ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)

let rec formatPrg2 = function (name, (max, index), Psi, [], callname) -> [] | (name, (max, index), Psi, (Psi', s, P) :: [], callname) -> ( let Psi'' = psiName (Psi', s, Psi, 0) in let fhead = if index = I.ctxLength Psi then "fun" else "and" in  [Fmt.HVbox0 1 5 1 [Fmt.String fhead; formatHead callname (name, (max, index), Psi'', s, Psi); Fmt.Space; Fmt.String "="; Fmt.Break; formatPrg3 callname (Psi'', P)]; Fmt.Break] ) | (name, (max, index), Psi, (Psi', s, P) :: O, callname) -> ( let Psi'' = psiName (Psi', s, Psi, 0) in  formatPrg2 (name, (max, index), Psi, O, callname) @ [Fmt.HVbox0 1 5 1 [Fmt.String "  |"; formatHead callname (name, (max, index), Psi'', s, Psi); Fmt.Space; Fmt.String "="; Fmt.Break; formatPrg3 callname (Psi'', P)]; Fmt.Break] )
let rec formatPrg11 = function (name, (max, index), Psi, T.Lam (D, P), callname) -> formatPrg11 (name, (max, index + 1), I.Decl (Psi, decName (T.coerceCtx Psi, D)), P, callname) | (name, (max, index), Psi, T.Case (T.Cases Os), callname) -> formatPrg2 (name, (max, index), Psi, Os, callname)
(* formatPrg1 ((max, index), Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *)

let rec formatPrg1 = function (name :: names, (max, index), Psi, T.PairPrg (P1, P2), callname) -> formatPrg11 (name, (max, index), Psi, P1, callname) @ formatPrg1 (names, (max, index - 1), Psi, P2, callname) | ([name], (max, index), Psi, P, callname) -> formatPrg11 (name, (max, index), Psi, P, callname)
(* formatPrg0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *)

(*      fun formatPrg0 (T.Rec (T.PDec (SOME _, F),
                             T.Case (T.Cases [(Psi, t, P)]))) =
          let
            val max = I.ctxLength Psi   (* number of ih. *)
          in
            Fmt.Vbox0 0 1 (formatPrg1 ((max, max), Psi, P))
          end
*)

let rec lookup (name :: names, proj :: projs) lemma  = if lemma = proj then name else lookup (names, projs) lemma
let rec formatPrg0 ((names, projs), T.Rec (D, P))  = ( (* number of ih. *)
let max = 1 in  Fmt.Vbox0 0 1 (formatPrg1 (names, (max, max), I.Decl (I.Null, D), P, fun lemma -> lookup (names, projs) lemma)) )
let rec formatFun Args  = (Names.varReset I.Null; formatPrg0 Args)
(*    fun formatLemmaDec (T.LemmaDec (names, P, F)) =
      Fmt.Vbox0 0 1 [formatFor (I.Null, F) names, Fmt.Break,
                     formatPrg (I.Null, P) names]
*)

let rec funToString Args  = Fmt.makestring_fmt (formatFun Args)
let rec prgToString Args  = Fmt.makestring_fmt (formatPrg3 (fun _ -> "?") Args)
(*   fun lemmaDecToString Args = Fmt.makestring_fmt (formatLemmaDec Args) *)

(*    fun prgToString Args names = "not yet implemented " *)

let rec nameCtx = function I.Null -> I.Null | (I.Decl (Psi, T.UDec D)) -> I.Decl (nameCtx Psi, T.UDec (Names.decName (T.coerceCtx Psi, D))) | (I.Decl (Psi, T.PDec (None, F, TC1, TC2))) -> ( let Psi' = nameCtx Psi in let I.NDec x = Names.decName (T.coerceCtx Psi', I.NDec None) in  I.Decl (Psi', T.PDec (x, F, TC1, TC2)) ) | (I.Decl (Psi, D)) -> I.Decl (nameCtx Psi, D)
let rec flag = function None -> "" | (Some _) -> "*"
(* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)

let rec formatCtx = function (I.Null) -> [] | (I.Decl (I.Null, T.UDec D)) -> if ! Global.chatter >= 4 then [Fmt.HVbox ([Fmt.Break; Print.formatDec (I.Null, D)])] else [Print.formatDec (I.Null, D)] | (I.Decl (I.Null, T.PDec (Some s, F, TC1, TC2))) -> if ! Global.chatter >= 4 then [Fmt.HVbox ([Fmt.Break; Fmt.String s; Fmt.Space; Fmt.String ("::" ^ flag TC1); Fmt.Space; formatFor (I.Null, F)])] else [Fmt.String s; Fmt.Space; Fmt.String ("::" ^ flag TC1); Fmt.Space; formatFor (I.Null, F)] | (I.Decl (Psi, T.UDec D)) -> ( let G = T.coerceCtx Psi in  if ! Global.chatter >= 4 then formatCtx Psi @ [Fmt.String ","; Fmt.Break; Fmt.Break] @ [Fmt.HVbox ([Fmt.Break; Print.formatDec (G, D)])] else formatCtx Psi @ [Fmt.String ","; Fmt.Break] @ [Fmt.Break; Print.formatDec (G, D)] ) | (I.Decl (Psi, T.PDec (Some s, F, TC1, TC2))) -> if ! Global.chatter >= 4 then formatCtx Psi @ [Fmt.String ","; Fmt.Break; Fmt.Break] @ [Fmt.HVbox ([Fmt.Break; Fmt.String s; Fmt.Space; Fmt.String ("::" ^ flag TC1); Fmt.Space; formatFor (Psi, F)])] else formatCtx Psi @ [Fmt.String ","; Fmt.Break] @ [Fmt.Break; Fmt.String s; Fmt.Space; Fmt.String ("::" ^ flag TC1); Fmt.Space; formatFor (Psi, F)]
let rec ctxToString Psi  = Fmt.makestring_fmt (Fmt.HVbox (formatCtx Psi))
let formatFor = formatFor
let forToString = forToString
let formatFun = formatFun
let formatPrg = formatPrg3 (fun _ -> "?")
(*    val formatLemmaDec = formatLemmaDec *)

let evarName = evarName
let evarReset = evarReset
let nameEVar = nameEVar
let prgToString = prgToString
let funToString = funToString
let nameCtx = nameCtx
let formatCtx = fun Psi -> Fmt.HVbox (formatCtx Psi)
let ctxToString = ctxToString
(*    val lemmaDecToString = lemmaDecToString *)
 end


(* signature FUNPRINT *)

