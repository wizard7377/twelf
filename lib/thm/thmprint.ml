(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

module ThmPrint (module ThmSyn' : THMSYN)
   (Formatter : FORMATTER)
  : THMPRINT =
struct
  module ThmSyn = ThmSyn'

  local
    module L = ThmSyn
    module I = IntSyn
    module F = Formatter

    let rec fmtIds = function nil -> []
      | (n :: nil) -> [F.String (n)]
      | (n :: L) -> [F.String (n), F.String " "] @ (fmtIds L)

    let rec fmtParams = function nil -> []
      | (SOME n :: nil) -> [F.String (n)]
      | (NONE :: nil) -> [F.String ("_")]
      | (SOME n :: L) -> [F.String (n), F.String " "] @ (fmtParams L)
      | (NONE :: L) -> [F.String ("_"), F.String " "] @ (fmtParams L)

    let rec fmtType (c, L) = F.HVbox ([F.String (I.conDecName (I.sgnLookup c)), F.String " "] @ (fmtParams L))

    let rec fmtCallpats = function nil -> []
      | (T :: nil) -> [F.String "(", fmtType T, F.String ")"]
      | (T :: L) -> [F.String "(", fmtType T, F.String ") "] @ (fmtCallpats L)

    let rec fmtOptions = function (L as (_ :: nil)) -> [F.HVbox (fmtIds L)]
      | L -> [F.String "(", F.HVbox (fmtIds L), F.String ") "]


    let rec fmtOrder = function (L.Varg L) -> 
        (case L of
           (H :: nil) => (fmtIds L)
         | _ => [F.String "(", F.HVbox (fmtIds L), F.String ")"])
      | (L.Lex L) -> [F.String "{", F.HVbox (fmtOrders L), F.String "}"]
      | (L.Simul L) -> [F.String "[", F.HVbox (fmtOrders L), F.String "]"]

    and fmtOrders nil = nil
      | fmtOrders (O :: nil) = fmtOrder O
      | fmtOrders (O :: L) = fmtOrder O @ (F.String " " :: fmtOrders L)

    let rec tDeclToString (L.TDecl (O, L.Callpats L)) = F.makestring_fmt (F.HVbox (fmtOrder O @
                                                           (F.String " " :: fmtCallpats L)))
    let rec callpatsToString (L.Callpats L) = F.makestring_fmt (F.HVbox (fmtCallpats L))

   (* -bp *)
    let rec fmtROrder (L.RedOrder(P,O,O'))=
        case P of
            L.Less => (fmtOrder O) @ (F.String " < " :: fmtOrder O')
          | L.Leq => (fmtOrder O) @ (F.String " <= " :: fmtOrder O')
          | L.Eq => (fmtOrder O) @ (F.String " = " :: fmtOrder O')

    let rec ROrderToString R =
        F.makestring_fmt (F.HVbox (fmtROrder R))

    let rec rDeclToString (L.RDecl (R,L.Callpats L)) =
        F.makestring_fmt (F.HVbox ((fmtROrder R @ (F.String " " :: fmtCallpats L))))


    let rec tabledDeclToString (L.TabledDecl cid) =
        F.makestring_fmt (F.HVbox ([F.String (I.conDecName (I.sgnLookup cid))]))

    let rec keepTableDeclToString (L.KeepTableDecl cid) =
        F.makestring_fmt (F.HVbox ([F.String (I.conDecName (I.sgnLookup cid))]))

  in
    let tDeclToString = tDeclToString
    let callpatsToString = callpatsToString
    let ROrderToString = ROrderToString            (* -bp *)
    let rDeclToString = rDeclToString              (* -bp *)
    let tabledDeclToString = tabledDeclToString
    let keepTableDeclToString = keepTableDeclToString
  end (* local *)

end;; (* functor ThmPrint *)
