(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) (* GEN BEGIN FUNCTOR DECL *) ThmSyn ((*! structure IntSyn : INTSYN !*)
                (*! structure ModeSyn' : MODESYN !*)
                (*! sharing ModeSyn'.IntSyn = IntSyn !*)
                structure Abstract : ABSTRACT
                (*! sharing Abstract.IntSyn = IntSyn !*)
                structure Whnf : WHNF
                (*! sharing Whnf.IntSyn = IntSyn !*)
                (*! structure Paths' : PATHS !*)
                structure Names' : NAMES
                (*! sharing Names'.IntSyn = IntSyn !*)
                  )
  : THMSYN =
struct
  (*! structure IntSyn = IntSyn !*)
  (*! structure ModeSyn = ModeSyn' *)
  (*! structure Paths = Paths' !*)
  structure Names = Names'

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))


  type param = string option

  datatype order =
    Varg of string list
  | Lex of order list
  | Simul of order list

  (* -bp *)
  datatype predicate = Less | Leq | Eq

  datatype red_order =
      RedOrder of predicate * order * order

  datatype callpats =
    Callpats of (IntSyn.cid * param list) list

  (* Termination declaration *)
  datatype t_decl =
    TDecl of (order * callpats)

  (* -bp *)
  (* Reduction declaration *)
  datatype r_decl =
    RDecl of (red_order * callpats)

  (* Tabled declaration *)
  datatype tabled_decl =
    TabledDecl of IntSyn.cid

  (* KeepTable declaration *)
  datatype keep_table_decl =
    KeepTableDecl of IntSyn.cid

  (* Theorem declaration *)
  datatype th_decl =
    ThDecl of (IntSyn.dec IntSyn.ctx * IntSyn.dec IntSyn.ctx) list
              * IntSyn.dec IntSyn.ctx * ModeSyn.mode IntSyn.ctx * int

  (* Proof declaration *)
  datatype p_decl =
    PDecl of int * t_decl

  (* World declaration *)
(*  datatype WDecl =
    WDecl of (IntSyn.Dec IntSyn.Ctx *
              IntSyn.Dec IntSyn.Ctx) list * Callpats *)
  datatype w_decl =
    WDecl of Names.qid list * callpats

  local

    structure I = IntSyn
    structure M = ModeSyn

    (* theoremDecToConDec (name, T) = D'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then D' is a constant type declaration of this theorem
    *)

    fun theoremDecToConDec ((name, ThDecl (GBs, G, MG, i)), r) =
        let
          (* theoremToConDec' G V = V'
    
             Invariant:
             If   G = V1 .. Vn
             and  G |- V : kind
             then V' = {V1} .. {Vn} V
             and  . |-  V' : kind
          *)
    
          fun theoremToConDec' (I.Null, V) = V
            | theoremToConDec' (I.Decl (G, D), V) =
                if Abstract.closedDec (G, (D, I.id))
                  then theoremToConDec' (G, Abstract.piDepend ((Whnf.normalizeDec (D, I.id),
                                                                I.Maybe), V))
                else error (r, "Free variables in theorem declaration")
        in
          (GBs, I.ConDec (name, NONE, i, I.Normal, theoremToConDec' (G, I.Uni (I.Type)), I.Kind))
        end


    (* theoremDecToModeSpine (name, T) = mS'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then mS' is a mode spine reflecting the
         quantifier information for the theorem
    *)

    fun theoremDecToModeSpine ((name,  ThDecl (GBs, G, MG, i)), r) =
      let
        fun theoremToModeSpine' (I.Null, I.Null, mS) = mS
          | theoremToModeSpine' (I.Decl (G, I.Dec (x, _)), I.Decl (MG, m), mS) =
              theoremToModeSpine' (G, MG, M.Mapp (M.Marg (m, x), mS))
      in
        theoremToModeSpine' (G, MG, M.Mnil)
      end

  in
    val theoremDecToConDec = theoremDecToConDec
    val theoremDecToModeSpine = theoremDecToModeSpine
  end (* local *)

end (* GEN END FUNCTOR DECL *) (* GEN END FUNCTOR DECL *); (* functor ThmSyn *)
