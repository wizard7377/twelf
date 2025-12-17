FunWeaken  Weaken WEAKEN     FUNWEAKEN  struct (*! structure FunSyn = FunSyn' !*)
module module (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'
    *)
let rec strengthenPsi(null,  , s) (null,  , s) strengthenPsi(decl (psi,  , prim d),  , s) let let  in in (decl (psi',  , prim (strengthenDec (d,  , s'))),  , dot1 s') strengthenPsi(decl (psi,  , block (ctxBlock (l,  , g))),  , s) let let  inlet  in in (decl (psi',  , block (ctxBlock (l,  , g''))),  , s'')(* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
let rec strengthenPsi'(nil,  , s) (nil,  , s) strengthenPsi'(prim d :: psi,  , s) let let  inlet  inlet  in in (prim d' :: psi'',  , s'') strengthenPsi'(block (ctxBlock (l,  , g)) :: psi,  , s) let let  inlet  in in (block (ctxBlock (l,  , g')) :: psi'',  , s'')let  inlet  inend