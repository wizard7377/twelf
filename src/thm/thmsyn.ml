ThmSyn  Abstract ABSTRACT    Whnf WHNF    Names' NAMES     THMSYN  struct (*! structure IntSyn = IntSyn !*)
(*! structure ModeSyn = ModeSyn' *)
(*! structure Paths = Paths' !*)
module exception let rec error(r,  , msg) raise (error (wrap (r,  , msg)))type Paramtype Order(* -bp *)
type Predicatetype RedOrdertype Callpats(* Termination declaration *)
type TDecl(* -bp *)
(* Reduction declaration *)
type RDecl(* Tabled declaration *)
type TabledDecl(* KeepTable declaration *)
type KeepTableDecl(* Theorem declaration *)
type ThDecl(* Proof declaration *)
type PDecl(* World declaration *)
(*  datatype WDecl =
    WDecl of (IntSyn.Dec IntSyn.Ctx *
              IntSyn.Dec IntSyn.Ctx) list * Callpats *)
type WDeclmodule module (* theoremDecToConDec (name, T) = D'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then D' is a constant type declaration of this theorem
    *)
let rec theoremDecToConDec((name,  , thDecl (gBs,  , g,  , mG,  , i)),  , r) let (* theoremToConDec' G V = V'

             Invariant:
             If   G = V1 .. Vn
             and  G |- V : kind
             then V' = {V1} .. {Vn} V
             and  . |-  V' : kind
          *)
let rec theoremToConDec'(null,  , v) v theoremToConDec'(decl (g,  , d),  , v) if closedDec (g,  , (d,  , id)) then theoremToConDec' (g,  , piDepend ((normalizeDec (d,  , id),  , maybe),  , v)) else error (r,  , "Free variables in theorem declaration") in (gBs,  , conDec (name,  , nONE,  , i,  , normal,  , theoremToConDec' (g,  , uni (type)),  , kind))(* theoremDecToModeSpine (name, T) = mS'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then mS' is a mode spine reflecting the
         quantifier information for the theorem
    *)
let rec theoremDecToModeSpine((name,  , thDecl (gBs,  , g,  , mG,  , i)),  , r) let let rec theoremToModeSpine'(null,  , null,  , mS) mS theoremToModeSpine'(decl (g,  , dec (x,  , _)),  , decl (mG,  , m),  , mS) theoremToModeSpine' (g,  , mG,  , mapp (marg (m,  , x),  , mS)) in theoremToModeSpine' (g,  , mG,  , mnil)let  inlet  in(* local *)
end