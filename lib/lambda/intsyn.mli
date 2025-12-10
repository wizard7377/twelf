(* Internal Syntax *)  
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

module type INTSYN =
sig

  type cid = int			(* Constant identifier        *)
  type mid = int                        (* Structure identifier       *)
  type csid = int                       (* CS module identifier       *)


  type fgnexp = exn                     (* foreign expression representation *)
  exception UnexpectedFgnExp of FgnExp
                                        (* raised by a constraint solver
					   if passed an incorrect arg *)
  type fgncnstr = exn                   (* foreign constraint representation *)
  exception UnexpectedFgnCnstr of FgnCnstr
                                        (* raised by a constraint solver
                                           if passed an incorrect arg *)

  (* Contexts *)

  type 'a Ctx =			(* Contexts                   *)
    Null				(* G ::= .                    *)
  | Decl of 'a Ctx * 'a			(*     | G, D                 *)
    
  val ctxPop : 'a Ctx -> 'a Ctx
  val ctxLookup: 'a Ctx * int -> 'a
  val ctxLength: 'a Ctx -> int

  type depend =                     (* Dependency information     *)
    No                                  (* P ::= No                   *)
  | Maybe                               (*     | Maybe                *)
  | Meta				(*     | Meta                 *)

  (* expressions *)

  type uni =			(* Universes:                 *)
    Kind				(* L ::= Kind                 *)
  | Type				(*     | Type                 *)

  type exp =			(* Expressions:               *)
    Uni   of Uni			(* U ::= L                    *)
  | Pi    of (dec * Depend) * Exp	(*     | Pi (D, P). V         *)
  | Root  of head * spine		(*     | H @ S                *)
  | Redex of Exp * spine		(*     | U @ S                *)
  | Lam   of dec * Exp			(*     | lam D. U             *)
  | EVar  of Exp option ref * dec Ctx * Exp * (cnstr ref) list ref
                                        (*     | X<I> : G|-V, Cnstr   *)
  | EClo  of Exp * sub			(*     | U[s]                 *)
  | AVar  of Exp option ref             (*     | A<I>                 *)

  | FgnExp of csid * FgnExp             (*     | (foreign expression) *)

  | NVar  of int			(*     | n (linear, 
                                               fully applied variable
                                               used in indexing       *)

  and head =				(* Head:                      *)
    BVar  of int			(* H ::= k                    *)
  | Const of cid			(*     | c                    *)
  | Proj  of block * int		(*     | #k(b)                *)
  | Skonst of cid			(*     | c#                   *)
  | Def   of cid			(*     | d (strict)           *)
  | NSDef of cid			(*     | d (non strict)       *)
  | FVar  of string * Exp * Sub		(*     | F[s]                 *)
  | FgnConst of csid * conDec           (*     | (foreign constant)   *)

  and spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | App   of Exp * spine		(*     | U ; S                *)
  | SClo  of spine * sub		(*     | S[s]                 *)

  and sub =				(* Explicit substitutions:    *)
    Shift of int			(* s ::= ^n                   *)
  | Dot   of front * sub		(*     | Ft.s                 *)

  and front =				(* Fronts:                    *)
    Idx of int				(* Ft ::= k                   *)
  | Exp of Exp				(*     | U                    *)
  | Axp of Exp				(*     | U                    *)
  | Block of block			(*     | _x                   *)
  | Undef				(*     | _                    *)

  and dec =				(* Declarations:              *)
    Dec of string option * Exp		(* D ::= x:V                  *)
  | BDec of string option * (cid * sub)	(*     | v:l[s]               *)
  | ADec of string option * int	        (*     | v[^-d]               *)
  | NDec of string option 

  and block =				(* Blocks:                    *)
    Bidx of int				(* b ::= v                    *)
  | LVar of block option ref * sub * (cid * sub)
                                        (*     | L(l[^k],t)           *)
  | Inst of Exp list                    (*     | U1, ..., Un          *)
  (* It would be better to consider having projections count
     like substitutions, then we could have Inst of Sub here, 
     which would simplify a lot of things.  

     I suggest however to wait until the next big overhaul 
     of the system -- cs *)


(*  | BClo of block * sub                 (*     | b[s]                 *) *)

  (* constraints *)

  and cnstr =				(* Constraint:                *)
    Solved                      	(* Cnstr ::= solved           *)
  | Eqn      of dec Ctx * Exp * Exp     (*         | G|-(U1 == U2)    *)
  | FgnCnstr of csid * FgnCnstr         (*         | (foreign)        *)

  and status =                          (* Status of a constant:      *)
    Normal                              (*   inert                    *)
  | Constraint of csid * (dec Ctx * spine * int -> Exp option)
                                        (*   acts as constraint       *)
  | Foreign of csid * (Spine -> Exp)    (*   is converted to foreign  *)

  and fgnUnify =                        (* Result of foreign unify    *)
    Succeed of FgnUnifyResidual list
    (* succeed with a list of residual operations *)
  | Fail

  and fgnUnifyResidual =
    Assign of dec Ctx * Exp * Exp * Sub
    (* perform the assignment G |- X = U [ss] *)
  | Delay of Exp * cnstr ref
    (* delay cnstr, associating it with all the rigid EVars in U  *)

  (* Global module type *)

  and conDec =			        (* Constant declaration       *)
    ConDec of string * mid option * int * status
                                        (* a : K : kind  or           *)
              * Exp * Uni	        (* c : A : type               *)
  | ConDef of string * mid option * int	(* a = A : K : kind  or       *)
              * Exp * Exp * Uni		(* d = M : A : type           *)
              * ancestor                (* ancestor info for d or a   *)
  | AbbrevDef of string * mid option * int
                                        (* a = A : K : kind  or       *)
              * Exp * Exp * Uni		(* d = M : A : type           *)
  | BlockDec of string * mid option     (* %block l : SOME G1 PI G2   *)
              * dec Ctx * dec list
  | BlockDef of string * mid option * cid list
                                        (* %block l = (l1 | ... | ln) *)
  | SkoDec of string * mid option * int	(* sa: K : kind  or           *)
              * Exp * Uni	        (* sc: A : type               *)

  and ancestor =			(* ancestor of d or a         *)
    Anc of cid option * int * cid option (* head(expand(d)), height, head(expand[height](d)) *)
                                        (* NONE means expands to {x:A}B *)

  type strdec =                     (* Structure declaration      *)
      StrDec of string * mid option

  (* Form of constant declaration *)
  type condecform =
    FromCS				(* from constraint domain *)
  | Ordinary				(* ordinary declaration *)
  | Clause				(* %clause declaration *)

  (* Type abbreviations *)
  type dctx = Dec Ctx			(* G = . | G,D                *)
  type eclo = Exp * Sub   		(* Us = U[s]                  *)
  type bclo = Block * Sub   		(* Bs = B[s]                  *)
  type cnstr = Cnstr ref

  exception Error of string		(* raised if out of space     *)

  (* standard operations on foreign expressions *)
  module FgnExpStd : sig
    (* convert to internal syntax *)
    module ToInternal : FGN_OPN with type arg = unit
                                   with type result = Exp

    (* apply function to subterms *)
    module Map : FGN_OPN with type arg = Exp -> Exp
			    with type result = Exp

    (* apply function to subterms, for effect *)
    module App : FGN_OPN with type arg = Exp -> unit
			    with type result = unit

    (* test for equality *)
    module EqualTo : FGN_OPN with type arg = Exp
                                with type result = bool

    (* unify with another term *)
    module UnifyWith : FGN_OPN with type arg = Dec Ctx * Exp
                                  with type result = FgnUnify

    (* fold a function over the subterms *)
    val fold : (csid * FgnExp) -> (Exp * 'a -> 'a) -> 'a -> 'a
  end

  (* standard operations on foreign constraints *)
  module FgnCnstrStd : sig
    (* convert to internal syntax *)
    module ToInternal : FGN_OPN with type arg = unit
                                   with type result = (Dec Ctx * Exp) list

    (* awake *)
    module Awake : FGN_OPN with type arg = unit
                              with type result = bool

    (* simplify *)
    module Simplify : FGN_OPN with type arg = unit
                                 with type result = bool
  end
  
  val conDecName   : ConDec -> string
  val conDecParent : ConDec -> mid option
  val conDecImp    : ConDec -> int
  val conDecStatus : ConDec -> Status
  val conDecType   : ConDec -> Exp
  val conDecBlock  : ConDec -> dctx * Dec list
  val conDecUni    : ConDec -> Uni

  val strDecName   : StrDec -> string
  val strDecParent : StrDec -> mid option

  val sgnReset     : unit -> unit
  val sgnSize      : unit -> cid * mid

  val sgnAdd   : ConDec -> cid
  val sgnLookup: cid -> ConDec
  val sgnApp   : (cid -> unit) -> unit

  val sgnStructAdd    : StrDec -> mid
  val sgnStructLookup : mid -> StrDec

  val constType   : cid -> Exp		(* type of c or d             *)
  val constDef    : cid -> Exp		(* definition of d            *)
  val constImp    : cid -> int
  val constStatus : cid -> Status
  val constUni    : cid -> Uni
  val constBlock  : cid -> dctx * Dec list

  (* Declaration Contexts *)

  val ctxDec    : dctx * int -> Dec	(* get variable declaration   *)
  val blockDec  : dctx * Block * int -> Dec 

  (* Explicit substitutions *)

  val id        : Sub			(* id                         *)
  val shift     : Sub			(* ^                          *)
  val invShift  : Sub                   (* ^-1                        *)

  val bvarSub   : int * Sub -> Front    (* k[s]                       *)
  val frontSub  : Front * Sub -> Front	(* H[s]                       *)
  val decSub    : Dec * Sub -> Dec	(* x:V[s]                     *)
  val blockSub  : Block * Sub -> Block  (* B[s]                       *)

  val comp      : Sub * Sub -> Sub	(* s o s'                     *)
  val dot1      : Sub -> Sub		(* 1 . (s o ^)                *)
  val invDot1   : Sub -> Sub		(* (^ o s) o ^-1)             *)

  (* EVar related functions *)

  val newEVar    : dctx * Exp -> Exp	(* creates X:G|-V, []         *) 
  val newAVar    : unit ->  Exp	        (* creates A (bare)           *) 
  val newTypeVar : dctx -> Exp		(* creates X:G|-type, []      *)
  val newLVar    : Sub * (cid * Sub) -> Block	
					(* creates B:(l[^k],t)        *) 

  (* Definition related functions *)
  val headOpt : Exp -> Head option
  val ancestor : Exp -> Ancestor
  val defAncestor : cid -> Ancestor

  (* Type related functions *)

  (* Not expanding type definitions *)
  val targetHeadOpt : Exp -> Head option (* target type family or NONE *)
  val targetHead : Exp -> Head           (* target type family         *)

  (* Expanding type definitions *)
  val targetFamOpt : Exp -> cid option  (* target type family or NONE *)
  val targetFam : Exp -> cid            (* target type family         *)

  (* Used in Flit *)
  val rename : cid * string -> unit

end;; (* module type INTSYN *)
