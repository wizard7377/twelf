(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

functor ThmPrint (structure ThmSyn' : THMSYN
                    structure Formatter : FORMATTER)
  : THMPRINT =
struct
  structure ThmSyn = ThmSyn'

  local
    structure L = ThmSyn
    structure I = IntSyn
    structure F = Formatter

    fun fmtIds nil = []
      | fmtIds (n :: nil) = [F.string (n)]
      | fmtIds (n :: L) = [F.string (n), F.string " "] @ (fmtIds L)

    fun fmtParams nil = []
      | fmtParams (SOME n :: nil) = [F.string (n)]
      | fmtParams (NONE :: nil) = [F.string ("_")]
      | fmtParams (SOME n :: L) = [F.string (n), F.string " "] @ (fmtParams L)
      | fmtParams (NONE :: L) = [F.string ("_"), F.string " "] @ (fmtParams L)

    fun fmtType (c, L) = F.hvbox ([F.string (I.conDecName (I.sgnLookup c)), F.string " "] @ (fmtParams L))

    fun fmtCallpats nil = []
      | fmtCallpats (T :: nil) = [F.string "(", fmtType T, F.string ")"]
      | fmtCallpats (T :: L) = [F.string "(", fmtType T, F.string ") "] @ (fmtCallpats L)

    fun fmtOptions (L as (_ :: nil)) = [F.hvbox (fmtIds L)]
      | fmtOptions L = [F.string "(", F.hvbox (fmtIds L), F.string ") "]


    fun fmtOrder (L.Varg L) =
        (case L of
           (H :: nil) => (fmtIds L)
         | _ => [F.string "(", F.hvbox (fmtIds L), F.string ")"])
      | fmtOrder (L.Lex L) = [F.string "{", F.hvbox (fmtOrders L), F.string "}"]
      | fmtOrder (L.Simul L) = [F.string "[", F.hvbox (fmtOrders L), F.string "]"]

    and fmtOrders nil = nil
      | fmtOrders (O :: nil) = fmtOrder O
      | fmtOrders (O :: L) = fmtOrder O @ (F.string " " :: fmtOrders L)

    fun tDeclToString (L.TDecl (O, L.Callpats L)) = F.makestring_fmt (F.hvbox (fmtOrder O @
                                                           (F.string " " :: fmtCallpats L)))
    fun callpatsToString (L.Callpats L) = F.makestring_fmt (F.hvbox (fmtCallpats L))

   (* -bp *)
    fun fmtROrder (L.RedOrder(P,O,O'))=
        case P of
            L.Less => (fmtOrder O) @ (F.string " < " :: fmtOrder O')
          | L.Leq => (fmtOrder O) @ (F.string " <= " :: fmtOrder O')
          | L.Eq => (fmtOrder O) @ (F.string " = " :: fmtOrder O')

    fun ROrderToString R =
        F.makestring_fmt (F.hvbox (fmtROrder R))

    fun rDeclToString (L.RDecl (R,L.Callpats L)) =
        F.makestring_fmt (F.hvbox ((fmtROrder R @ (F.string " " :: fmtCallpats L))))


    fun tabledDeclToString (L.TabledDecl cid) =
        F.makestring_fmt (F.hvbox ([F.string (I.conDecName (I.sgnLookup cid))]))

    fun keepTableDeclToString (L.KeepTableDecl cid) =
        F.makestring_fmt (F.hvbox ([F.string (I.conDecName (I.sgnLookup cid))]))

  in
    val tDeclToString = tDeclToString
    val callpatsToString = callpatsToString
    val ROrderToString = ROrderToString            (* -bp *)
    val rDeclToString = rDeclToString              (* -bp *)
    val tabledDeclToString = tabledDeclToString
    val keepTableDeclToString = keepTableDeclToString
  end (* local *)

end; (* functor ThmPrint *)
