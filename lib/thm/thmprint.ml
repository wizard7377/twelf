(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) ThmPrint (structure ThmSyn' : THMSYN
                    structure Formatter : FORMATTER)
  : THMPRINT =
struct
  structure ThmSyn = ThmSyn'

  local
    structure L = ThmSyn
    structure I = IntSyn
    structure F = Formatter

    fun (* GEN BEGIN FUN FIRST *) fmtIds nil = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fmtIds (n :: nil) = [F.String (n)] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) fmtIds (n :: L) = [F.String (n), F.String " "] @ (fmtIds L) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) fmtParams nil = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fmtParams (SOME n :: nil) = [F.String (n)] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) fmtParams (NONE :: nil) = [F.String ("_")] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) fmtParams (SOME n :: L) = [F.String (n), F.String " "] @ (fmtParams L) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) fmtParams (NONE :: L) = [F.String ("_"), F.String " "] @ (fmtParams L) (* GEN END FUN BRANCH *)

    fun fmtType (c, L) = F.HVbox ([F.String (I.conDecName (I.sgnLookup c)), F.String " "] @ (fmtParams L))

    fun (* GEN BEGIN FUN FIRST *) fmtCallpats nil = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fmtCallpats (T :: nil) = [F.String "(", fmtType T, F.String ")"] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) fmtCallpats (T :: L) = [F.String "(", fmtType T, F.String ") "] @ (fmtCallpats L) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) fmtOptions (L as (_ :: nil)) = [F.HVbox (fmtIds L)] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fmtOptions L = [F.String "(", F.HVbox (fmtIds L), F.String ") "] (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) fmtOrder (L.Varg L) =
        (case L of
           (H :: nil) => (fmtIds L)
         | _ => [F.String "(", F.HVbox (fmtIds L), F.String ")"]) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fmtOrder (L.Lex L) = [F.String "{", F.HVbox (fmtOrders L), F.String "}"] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) fmtOrder (L.Simul L) = [F.String "[", F.HVbox (fmtOrders L), F.String "]"] (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) fmtOrders nil = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fmtOrders (O :: nil) = fmtOrder O (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) fmtOrders (O :: L) = fmtOrder O @ (F.String " " :: fmtOrders L) (* GEN END FUN BRANCH *)

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
    (* GEN BEGIN TAG OUTSIDE LET *) val tDeclToString = tDeclToString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val callpatsToString = callpatsToString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val ROrderToString = ROrderToString (* GEN END TAG OUTSIDE LET *)            (* -bp *)
    (* GEN BEGIN TAG OUTSIDE LET *) val rDeclToString = rDeclToString (* GEN END TAG OUTSIDE LET *)              (* -bp *)
    (* GEN BEGIN TAG OUTSIDE LET *) val tabledDeclToString = tabledDeclToString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val keepTableDeclToString = keepTableDeclToString (* GEN END TAG OUTSIDE LET *)
  end (* local *)

end (* GEN END FUNCTOR DECL *); (* functor ThmPrint *)
