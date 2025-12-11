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
      | (* GEN CASE BRANCH *) fmtIds (n :: nil) = [F.String (n)]
      | (* GEN CASE BRANCH *) fmtIds (n :: L) = [F.String (n), F.String " "] @ (fmtIds L)

    fun fmtParams nil = []
      | (* GEN CASE BRANCH *) fmtParams (SOME n :: nil) = [F.String (n)]
      | (* GEN CASE BRANCH *) fmtParams (NONE :: nil) = [F.String ("_")]
      | (* GEN CASE BRANCH *) fmtParams (SOME n :: L) = [F.String (n), F.String " "] @ (fmtParams L)
      | (* GEN CASE BRANCH *) fmtParams (NONE :: L) = [F.String ("_"), F.String " "] @ (fmtParams L)

    fun fmtType (c, L) = F.HVbox ([F.String (I.conDecName (I.sgnLookup c)), F.String " "] @ (fmtParams L))

    fun fmtCallpats nil = []
      | (* GEN CASE BRANCH *) fmtCallpats (T :: nil) = [F.String "(", fmtType T, F.String ")"]
      | (* GEN CASE BRANCH *) fmtCallpats (T :: L) = [F.String "(", fmtType T, F.String ") "] @ (fmtCallpats L)

    fun fmtOptions (L as (_ :: nil)) = [F.HVbox (fmtIds L)]
      | (* GEN CASE BRANCH *) fmtOptions L = [F.String "(", F.HVbox (fmtIds L), F.String ") "]


    fun fmtOrder (L.Varg L) =
        (case L of
           (H :: nil) => (fmtIds L)
         | _ => [F.String "(", F.HVbox (fmtIds L), F.String ")"])
      | (* GEN CASE BRANCH *) fmtOrder (L.Lex L) = [F.String "{", F.HVbox (fmtOrders L), F.String "}"]
      | (* GEN CASE BRANCH *) fmtOrder (L.Simul L) = [F.String "[", F.HVbox (fmtOrders L), F.String "]"]

    and fmtOrders nil = nil
      | (* GEN CASE BRANCH *) fmtOrders (O :: nil) = fmtOrder O
      | (* GEN CASE BRANCH *) fmtOrders (O :: L) = fmtOrder O @ (F.String " " :: fmtOrders L)

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
    val tDeclToString = tDeclToString
    val callpatsToString = callpatsToString
    val ROrderToString = ROrderToString            (* -bp *)
    val rDeclToString = rDeclToString              (* -bp *)
    val tabledDeclToString = tabledDeclToString
    val keepTableDeclToString = keepTableDeclToString
  end (* local *)

end; (* functor ThmPrint *)
