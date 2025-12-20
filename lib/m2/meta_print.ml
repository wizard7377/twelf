(* Meta printer for_sml proof states *)


(* Author: Carsten Schuermann *)


module MetaPrint (Global : GLOBAL) (MetaSyn' : METASYN) (Formatter : FORMATTER) (Print : PRINT) (ClausePrint : CLAUSEPRINT) : METAPRINT = struct module MetaSyn = MetaSyn'
module M = MetaSyn
module I = IntSyn
module F = Formatter
let rec modeToString = function M.Top -> "+" | M.Bot -> "-"
(* depthToString is used to format splitting depth *)

let rec depthToString (b)  = if b <= 0 then "" else Int.toString b
let rec fmtPrefix (GM)  = ( let rec fmtPrefix' = function (M.Prefix (I.Null, I.Null, I.Null), Fmt) -> Fmt | (M.Prefix (I.Decl (I.Null, D), I.Decl (I.Null, mode), I.Decl (I.Null, b)), Fmt) -> [F.String (depthToString b); F.String (modeToString mode); Print.formatDec (I.Null, D)] @ Fmt | (M.Prefix (I.Decl (G, D), I.Decl (M, mode), I.Decl (B, b)), Fmt) -> fmtPrefix' (M.Prefix (G, M, B), [F.String ","; F.Space; F.Break; F.String (depthToString b); F.String (modeToString mode); Print.formatDec (G, D)] @ Fmt) in  F.HVbox (fmtPrefix' (GM, [])) )
let rec prefixToString GM  = F.makestring_fmt (fmtPrefix GM)
let rec stateToString (M.State (name, GM, V))  = name ^ ":\n" ^ prefixToString GM ^ "\n--------------\n" ^ ClausePrint.clauseToString (G, V) ^ "\n\n"
let rec sgnToString = function (M.SgnEmpty) -> "" | (M.ConDec (e, S)) -> (if ! Global.chatter >= 4(* use explicitly quantified form *)
 then Print.conDecToString e ^ "\n" else if ! Global.chatter >= 3(* use form without quantifiers, which is reparsable *)
 then ClausePrint.conDecToString e ^ "\n" else "") ^ sgnToString S
let modeToString = modeToString
let sgnToString = sgnToString
let stateToString = stateToString
let conDecToString = ClausePrint.conDecToString
(* local *)

 end


(* functor MetaPrint *)

