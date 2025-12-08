(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)

module FunWeaken ((*! module FunSyn' : FUNSYN !*)
                   (Weaken : WEAKEN): FUNWEAKEN =
                   (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
struct
  (*! module FunSyn = FunSyn' !*)

  local
    module F = FunSyn
    module I = IntSyn

    (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'
    *)
    let rec strengthenPsi = function (I.Null, s) -> (I.Null, s)
      | (I.Decl (Psi, F.Prim D), s) -> 
        let
          let (Psi', s') = strengthenPsi (Psi, s)
        in
          (I.Decl (Psi', F.Prim (Weaken.strengthenDec (D, s'))), I.dot1 s')
        end
      | (I.Decl (Psi, F.Block (F.CtxBlock (l, G))), s) -> 
        let
          let (Psi', s') = strengthenPsi (Psi, s)
          let (G'', s'') = Weaken.strengthenCtx (G, s')
        in
          (I.Decl (Psi', F.Block (F.CtxBlock (l, G''))), s'')
        end

    (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
    let rec strengthenPsi' = function (nil, s) -> (nil, s)
      | (F.Prim D :: Psi, s) -> 
        let
          let D' = Weaken.strengthenDec (D, s)
          let s' = I.dot1 s
          let (Psi'', s'') = strengthenPsi' (Psi, s')
        in
          (F.Prim D' :: Psi'', s'')
        end
      | (F.Block (F.CtxBlock (l, G)) :: Psi, s) -> 
        let
          let (G', s') = Weaken.strengthenCtx (G, s)
          let (Psi'', s'') = strengthenPsi' (Psi, s')
        in
          (F.Block (F.CtxBlock (l, G')) :: Psi'', s'')
        end
  in
    let strengthenPsi = strengthenPsi
    let strengthenPsi' = strengthenPsi'
  end
end (* functor FunWeaken *)
