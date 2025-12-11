(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

signature FUNSYN = 
sig
  (*! structure IntSyn : INTSYN !*)

  (* make abstract *)
  type label = int      
  type lemma = int 

  datatype label_dec =			(* ContextBody                *)
    LabelDec of string * IntSyn.dec list * IntSyn.dec list
					(* BB ::= l: SOME Theta. Phi  *)

  datatype ctx_block =                   (* ContextBlocks              *)
    CtxBlock of 
     label option * IntSyn.dctx		(* B ::= l : Phi              *) 

  datatype lf_dec =			(* Contexts                   *)
    Prim of IntSyn.dec			(* LD ::= x :: A              *)
  | Block of ctx_block			(*      | B                   *)

  (* ??? *)
  type lfctx = lf_dec IntSyn.ctx         (* Psi ::= . | Psi, LD        *) 

  datatype for =			(* Formulas                   *)
    All of lf_dec * for			(* F ::= All LD. F            *)
  | Ex  of IntSyn.dec * for		(*     | Ex  D. F             *)
  | True				(*     | T                    *)
  | And of for * for                    (*     | F1 ^ F2              *)

  datatype pro =			(* Programs                   *)
    Lam of lf_dec * pro			(* P ::= lam LD. P            *)
  | Inx of IntSyn.exp * pro             (*     | <M, P>               *)
  | Unit				(*     | <>                   *)
  | Rec of m_dec * pro			(*     | mu xx. P             *)
  | Let of decs * pro			(*     | let Ds in P          *)
  | Case of opts                        (*     | case O               *)
  | Pair of pro * pro                   (*     | <P1, P2>             *)

  and opts =				(* Option list                *)
    Opts of (lfctx * IntSyn.sub * pro) list
                                        (* O ::= (Psi' |> s |-> P     *)

  and m_dec =				(* Meta Declaration:          *)
    MDec of string option * for		(* DD ::= xx : F              *)
 
  and decs =				(* Declarations               *)
    Empty				(* Ds ::= .                   *)
  | Split of int * decs			(*      | <x, yy> = P, Ds     *)
  | New of ctx_block * decs		(*      | nu B. Ds            *)
  | App of (int * IntSyn.exp) * decs	(*      | xx = yy M, Ds       *)
  | PApp of (int * int) * decs		(*      | xx = yy Phi, Ds     *)
  | Lemma of lemma * decs               (*      | xx = cc, Ds         *)
  | Left of int * decs                  (*      | xx = pi1 yy, Ds     *)
  | Right of int * decs                 (*      | xx = pi2 yy, Ds     *)
 
  datatype lemma_dec =			(* Lemmas                     *)
    LemmaDec of string list * pro * for	(* L ::= c:F = P              *)

  (* ??? *)
  type mctx = m_dec IntSyn.ctx           (* Delta ::= . | Delta, xx : F*)

  val labelLookup : label -> label_dec
  val labelAdd : label_dec -> label
  val labelSize : unit -> int
  val labelReset : unit -> unit

  val lemmaLookup : lemma -> lemma_dec
  val lemmaAdd : lemma_dec -> lemma
  val lemmaSize : unit -> int

  val mdecSub : m_dec * IntSyn.sub -> m_dec
  val makectx : lfctx -> IntSyn.dctx

  val lfctxLength : lfctx -> int
  val lfctxLFDec : (lfctx * int) -> (lf_dec * IntSyn.sub) 


  val dot1n : (IntSyn.dctx * IntSyn.sub) -> IntSyn.sub

  val convFor : (for * IntSyn.sub) * 
                (for * IntSyn.sub) -> bool
  val forSub : for * IntSyn.sub -> for
  val normalizeFor : for * IntSyn.sub -> for

  val listToCtx : IntSyn.dec list -> IntSyn.dctx
  val ctxToList : IntSyn.dctx -> IntSyn.dec list
end (* Signature FUNSYN *)       






