(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

let recctor ThmPrint (module ThmSyn' : THMSYN
                    module Formatter : FORMATTER)
  : THMPRINT =
struct
  module ThmSyn = ThmSyn'

  local
    module L = ThmSyn
    module I = IntSyn
    module F = Formatter

    fun fmtIds nil = []
      | fmtIds (n :: nil) = [F.String (n)]
      | fmtIds (n :: L) = [F.String (n), F.String " "] @ (fmtIds L)

    fun fmtParams nil = []
      | fmtParams (SOME n :: nil) = [F.String (n)]
      | fmtParams (NONE :: nil) = [F.String ("_")]
      | fmtParams (SOME n :: L) = [F.String (n), F.String " "] @ (fmtParams L)
      | fmtParams (NONE :: L) = [F.String ("_"), F.String " "] @ (fmtParams L)

    fun fmtType (c, L) = F.HVbox ([F.String (I.conDecName (I.sgnLookup c)), F.String " "] @ (fmtParams L))

    fun fmtCallpats nil = []
      | fmtCallpats (T :: nil) = [F.String "(", fmtType T, F.String ")"]
      | fmtCallpats (T :: L) = [F.String "(", fmtType T, F.String ") "] @ (fmtCallpats L)

    fun fmtOptions (L as (_ :: nil)) = [F.HVbox (fmtIds L)]
      | fmtOptions L = [F.String "(", F.HVbox (fmtIds L), F.String ") "]


    fun fmtOrder (L.Varg L) =
        (case L of
           (H :: nil) => (fmtIds L)
         | _ => [F.String "(", F.HVbox (fmtIds L), F.String ")"])
      | fmtOrder (L.Lex L) = [F.String "{", F.HVbox (fmtOrders L), F.String "}"]
      | fmtOrder (L.Simul L) = [F.String "[", F.HVbox (fmtOrders L), F.String "]"]

    and fmtOrders nil = nil
      | fmtOrders (O :: nil) = fmtOrder O
      | fmtOrders (O :: L) = fmtOrder O @ (F.String " " :: fmtOrders L)

    fun tDeclToString (L.TDecl (O, L.Callpats L)) = F.makestring_fmt (F.HVbox (fmtOrder O @
                                                           (F.String " " :: fmtCallpats L)))
    fun callpatsToString (L.Callpats L) = F.makestring_fmt (F.HVbox (fmtCallpats L))

   (* -bp *)
    fun fmtROrder (L.RedOrder(P,O,O'))=
        case P of
            L.Less => (fmtOrder O) @ (F.String " < " :: fmtOrder O')
          | L.Leq => (fmtOrder O) @ (F.String " <= " :: fmtOrder O')
          | L.Eq => (fmtOrder O) @ (F.String " = " :: fmtOrder O')

    fun ROrderToString R =
        F.makestring_fmt (F.HVbox (fmtROrder R))

    fun rDeclToString (L.RDecl (R,L.Callpats L)) =
        F.makestring_fmt (F.HVbox ((fmtROrder R @ (F.String " " :: fmtCallpats L))))


    fun tabledDeclToString (L.TabledDecl cid) =
        F.makestring_fmt (F.HVbox ([F.String (I.conDecName (I.sgnLookup cid))]))

    fun keepTableDeclToString (L.KeepTableDecl cid) =
        F.makestring_fmt (F.HVbox ([F.String (I.conDecName (I.sgnLookup cid))]))

  in
    let tDeclToString = tDeclToString
    let callpatsToString = callpatsToString
    let ROrderToString = ROrderToString            (* -bp *)
    let rDeclToString = rDeclToString              (* -bp *)
    let tabledDeclToString = tabledDeclToString
    let keepTableDeclToString = keepTableDeclToString
  end (* local *)

end; (* functor ThmPrint *)
