(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) FunWeaken ((*! structure FunSyn' : FUNSYN !*)
                   structure Weaken : WEAKEN
                   (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
                     ) : FUNWEAKEN =
struct
  (*! structure FunSyn = FunSyn' !*)

  local
    structure F = FunSyn
    structure I = IntSyn

    (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenPsi (I.Null, s) = (I.Null, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenPsi (I.Decl (Psi, F.Prim D), s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', s') = strengthenPsi (Psi, s) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (Psi', F.Prim (Weaken.strengthenDec (D, s'))), I.dot1 s')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strengthenPsi (I.Decl (Psi, F.Block (F.CtxBlock (l, G))), s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', s') = strengthenPsi (Psi, s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (G'', s'') = Weaken.strengthenCtx (G, s') (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (Psi', F.Block (F.CtxBlock (l, G''))), s'')
        end (* GEN END FUN BRANCH *)

    (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenPsi' (nil, s) = (nil, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenPsi' (F.Prim D :: Psi, s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = Weaken.strengthenDec (D, s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val s' = I.dot1 s (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi'', s'') = strengthenPsi' (Psi, s') (* GEN END TAG OUTSIDE LET *)
        in
          (F.Prim D' :: Psi'', s'')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strengthenPsi' (F.Block (F.CtxBlock (l, G)) :: Psi, s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', s') = Weaken.strengthenCtx (G, s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi'', s'') = strengthenPsi' (Psi, s') (* GEN END TAG OUTSIDE LET *)
        in
          (F.Block (F.CtxBlock (l, G')) :: Psi'', s'')
        end (* GEN END FUN BRANCH *)
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val strengthenPsi = strengthenPsi (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val strengthenPsi' = strengthenPsi' (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *) (* functor FunWeaken *)
