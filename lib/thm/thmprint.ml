(* Printer for_sml Meta Theorems *)

(* Author: Carsten Schuermann *)

module type THMPRINT = sig
  module ThmSyn : THMSYN

  val tDeclToString : ThmSyn.tDecl -> string
  val callpatsToString : ThmSyn.callpats -> string
  val rDeclToString : ThmSyn.rDecl -> string

  (* -bp *)
  val rOrderToString : ThmSyn.redOrder -> string

  (* -bp *)
  val tabledDeclToString : ThmSyn.tabledDecl -> string

  (* -bp *)
  val keepTableDeclToString : ThmSyn.keepTableDecl -> string
  (* -bp *)
end

(* signature THMPRINT *)
(* Printer for_sml Meta Theorems *)

(* Author: Carsten Schuermann *)

(* Modified: Brigitte Pientka *)

module ThmPrint (ThmSyn' : THMSYN) (Formatter : FORMATTER) : THMPRINT = struct
  module ThmSyn = ThmSyn'
  module L = ThmSyn
  module I = IntSyn
  module F = Formatter

  let rec fmtIds = function
    | [] -> []
    | n :: [] -> [ F.String n ]
    | n :: L -> [ F.String n; F.String " " ] @ fmtIds L

  let rec fmtParams = function
    | [] -> []
    | Some n :: [] -> [ F.String n ]
    | None :: [] -> [ F.String "_" ]
    | Some n :: L -> [ F.String n; F.String " " ] @ fmtParams L
    | None :: L -> [ F.String "_"; F.String " " ] @ fmtParams L

  let rec fmtType (c, L) =
    F.HVbox
      ([ F.String (I.conDecName (I.sgnLookup c)); F.String " " ] @ fmtParams L)

  let rec fmtCallpats = function
    | [] -> []
    | T :: [] -> [ F.String "("; fmtType T; F.String ")" ]
    | T :: L -> [ F.String "("; fmtType T; F.String ") " ] @ fmtCallpats L

  let rec fmtOptions = function
    | L -> [ F.HVbox (fmtIds L) ]
    | L -> [ F.String "("; F.HVbox (fmtIds L); F.String ") " ]

  let rec fmtOrder = function
    | L.Varg L -> (
        match L with
        | H :: [] -> fmtIds L
        | _ -> [ F.String "("; F.HVbox (fmtIds L); F.String ")" ])
    | L.Lex L -> [ F.String "{"; F.HVbox (fmtOrders L); F.String "}" ]
    | L.Simul L -> [ F.String "["; F.HVbox (fmtOrders L); F.String "]" ]

  and fmtOrders = function
    | [] -> []
    | O :: [] -> fmtOrder O
    | O :: L -> fmtOrder O @ (F.String " " :: fmtOrders L)

  let rec tDeclToString (L.TDecl (O, L.Callpats L)) =
    F.makestring_fmt (F.HVbox (fmtOrder O @ (F.String " " :: fmtCallpats L)))

  let rec callpatsToString (L.Callpats L) =
    F.makestring_fmt (F.HVbox (fmtCallpats L))
  (* -bp *)

  let rec fmtROrder (L.RedOrder (P, O, O')) =
    match P with
    | L.Less -> fmtOrder O @ (F.String " < " :: fmtOrder O')
    | L.Leq -> fmtOrder O @ (F.String " <= " :: fmtOrder O')
    | L.Eq -> fmtOrder O @ (F.String " = " :: fmtOrder O')

  let rec rOrderToString R = F.makestring_fmt (F.HVbox (fmtROrder R))

  let rec rDeclToString (L.RDecl (R, L.Callpats L)) =
    F.makestring_fmt (F.HVbox (fmtROrder R @ (F.String " " :: fmtCallpats L)))

  let rec tabledDeclToString (L.TabledDecl cid) =
    F.makestring_fmt (F.HVbox [ F.String (I.conDecName (I.sgnLookup cid)) ])

  let rec keepTableDeclToString (L.KeepTableDecl cid) =
    F.makestring_fmt (F.HVbox [ F.String (I.conDecName (I.sgnLookup cid)) ])

  let tDeclToString = tDeclToString
  let callpatsToString = callpatsToString
  let rOrderToString = rOrderToString
  (* -bp *)

  let rDeclToString = rDeclToString
  (* -bp *)

  let tabledDeclToString = tabledDeclToString
  let keepTableDeclToString = keepTableDeclToString
  (* local *)
end

(* functor ThmPrint *)
