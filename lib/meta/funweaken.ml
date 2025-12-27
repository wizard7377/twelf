open Basis

(* Weakening substitutions for_sml meta substitutions *)

(* Author: Carsten Schuermann *)

module type FUNWEAKEN = sig
  (*! structure FunSyn : Funsyn.FUNSYN !*)
  val strengthenPsi : FunSyn.lfctx * IntSyn.sub -> FunSyn.lfctx * IntSyn.sub

  val strengthenPsi' :
    FunSyn.lFDec list * IntSyn.sub -> FunSyn.lFDec list * IntSyn.sub
end

(* signature FUNWEAKEN *)
(* Weakening substitutions for_sml meta substitutions *)

(* Author: Carsten Schuermann *)

module FunWeaken (Weaken : Weaken.Weaken.WEAKEN) : FUNWEAKEN = struct
  (*! structure FunSyn = FunSyn' !*)

  module F = FunSyn
  module I = IntSyn
  (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'
    *)

  let rec strengthenPsi = function
    | I.Null, s -> (I.Null, s)
    | I.Decl (Psi, F.Prim D), s ->
        let Psi', s' = strengthenPsi (Psi, s) in
        (I.Decl (Psi', F.Prim (Weaken.strengthenDec (D, s'))), I.dot1 s')
    | I.Decl (Psi, F.Block (F.CtxBlock (l, G))), s ->
        let Psi', s' = strengthenPsi (Psi, s) in
        let G'', s'' = Weaken.strengthenCtx (G, s') in
        (I.Decl (Psi', F.Block (F.CtxBlock (l, G''))), s'')
  (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)

  let rec strengthenPsi' = function
    | [], s -> ([], s)
    | F.Prim D :: Psi, s ->
        let D' = Weaken.strengthenDec (D, s) in
        let s' = I.dot1 s in
        let Psi'', s'' = strengthenPsi' (Psi, s') in
        (F.Prim D' :: Psi'', s'')
    | F.Block (F.CtxBlock (l, G)) :: Psi, s ->
        let G', s' = Weaken.strengthenCtx (G, s) in
        let Psi'', s'' = strengthenPsi' (Psi, s') in
        (F.Block (F.CtxBlock (l, G')) :: Psi'', s'')

  let strengthenPsi = strengthenPsi
  let strengthenPsi' = strengthenPsi'
end

(* functor FunWeaken *)
