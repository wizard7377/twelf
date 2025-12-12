(* Internal Syntax *)  
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature INTSYN =
sig

  type cid = int			(* Constant identifier        *)
  type mid = int                        (* Structure identifier       *)
  type csid = int                       (* CS module identifier       *)


  type fgn_exp = exn                     (* foreign expression representation *)
  exception UnexpectedFgnExp of fgn_exp
                                        (* raised by a constraint solver
					   if passed an incorrect arg *)
  type fgn_cnstr = exn                   (* foreign constraint representation *)
  exception UnexpectedFgnCnstr of fgn_cnstr
                                        (* raised by a constraint solver
                                           if passed an incorrect arg *)

  (* Contexts *)

  datatype 'a ctx =			(* Contexts                   *)
    Null				(* G ::= .                    *)
  | Decl of 'a ctx * 'a			(*     | G, D                 *)
    
  val ctxPop : 'a ctx -> 'a ctx
  val ctxLookup: 'a ctx * int -> 'a
  val ctxLength: 'a ctx -> int

  datatype depend =                     (* Dependency information     *)
    No                                  (* P ::= No                   *)
  | Maybe                               (*     | Maybe                *)
  | Meta				(*     | Meta                 *)

  (* expressions *)

  datatype uni =			(* Universes:                 *)
    Kind				(* L ::= Kind                 *)
  | Type				(*     | Type                 *)

  datatype exp =			(* Expressions:               *)
    Uni   of uni			(* U ::= L                    *)
  | Pi    of (dec * depend) * exp	(*     | Pi (D, P). V         *)
  | Root  of head * spine		(*     | H @ S                *)
  | Redex of exp * spine		(*     | U @ S                *)
  | Lam   of dec * exp			(*     | lam D. U             *)
  | EVar  of exp option ref * dec ctx * exp * (cnstr ref) list ref
                                        (*     | X<I> : G|-V, Cnstr   *)
  | EClo  of exp * sub			(*     | U[s]                 *)
  | AVar  of exp option ref             (*     | A<I>                 *)

  | FgnExp of csid * fgn_exp             (*     | (foreign expression) *)

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
  | FVar  of string * exp * sub		(*     | F[s]                 *)
  | FgnConst of csid * con_dec           (*     | (foreign constant)   *)

  and spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | App   of exp * spine		(*     | U ; S                *)
  | SClo  of spine * sub		(*     | S[s]                 *)

  and sub =				(* Explicit substitutions:    *)
    Shift of int			(* s ::= ^n                   *)
  | Dot   of front * sub		(*     | Ft.s                 *)

  and front =				(* Fronts:                    *)
    Idx of int				(* Ft ::= k                   *)
  | Exp of exp				(*     | U                    *)
  | Axp of exp				(*     | U                    *)
  | Block of block			(*     | _x                   *)
  | Undef				(*     | _                    *)

  and dec =				(* Declarations:              *)
    Dec of string option * exp		(* D ::= x:V                  *)
  | BDec of string option * (cid * sub)	(*     | v:l[s]               *)
  | ADec of string option * int	        (*     | v[^-d]               *)
  | NDec of string option 

  and block =				(* Blocks:                    *)
    Bidx of int				(* b ::= v                    *)
  | LVar of block option ref * sub * (cid * sub)
                                        (*     | L(l[^k],t)           *)
  | Inst of exp list                    (*     | U1, ..., Un          *)
  (* It would be better to consider having projections count
     like substitutions, then we could have Inst of Sub here, 
     which would simplify a lot of things.  

     I suggest however to wait until the next big overhaul 
     of the system -- cs *)


(*  | BClo of Block * Sub                 (*     | b[s]                 *) *)

  (* constraints *)

  and cnstr =				(* Constraint:                *)
    Solved                      	(* Cnstr ::= solved           *)
  | Eqn      of dec ctx * exp * exp     (*         | G|-(U1 == U2)    *)
  | FgnCnstr of csid * fgn_cnstr         (*         | (foreign)        *)

  and status =                          (* Status of a constant:      *)
    Normal                              (*   inert                    *)
  | Constraint of csid * (dec ctx * spine * int -> exp option)
                                        (*   acts as constraint       *)
  | Foreign of csid * (spine -> exp)    (*   is converted to foreign  *)

  and fgn_unify =                        (* Result of foreign unify    *)
    Succeed of fgn_unify_residual list
    (* succeed with a list of residual operations *)
  | Fail

  and fgn_unify_residual =
    Assign of dec ctx * exp * exp * sub
    (* perform the assignment G |- X = U [ss] *)
  | Delay of exp * cnstr ref
    (* delay cnstr, associating it with all the rigid EVars in U  *)

  (* Global signature *)

  and con_dec =			        (* Constant declaration       *)
    ConDec of string * mid option * int * status
                                        (* a : K : kind  or           *)
              * exp * uni	        (* c : A : type               *)
  | ConDef of string * mid option * int	(* a = A : K : kind  or       *)
              * exp * exp * uni		(* d = M : A : type           *)
              * ancestor                (* Ancestor info for d or a   *)
  | AbbrevDef of string * mid option * int
                                        (* a = A : K : kind  or       *)
              * exp * exp * uni		(* d = M : A : type           *)
  | BlockDec of string * mid option     (* %block l : SOME G1 PI G2   *)
              * dec ctx * dec list
  | BlockDef of string * mid option * cid list
                                        (* %block l = (l1 | ... | ln) *)
  | SkoDec of string * mid option * int	(* sa: K : kind  or           *)
              * exp * uni	        (* sc: A : type               *)

  and ancestor =			(* Ancestor of d or a         *)
    Anc of cid option * int * cid option (* head(expand(d)), height, head(expand[height](d)) *)
                                        (* NONE means expands to {x:A}B *)

  datatype str_dec =                     (* Structure declaration      *)
      StrDec of string * mid option

  (* Form of constant declaration *)
  datatype con_dec_form =
    FromCS				(* from constraint domain *)
  | Ordinary				(* ordinary declaration *)
  | Clause				(* %clause declaration *)

  (* Type abbreviations *)
  type dctx = dec ctx			(* G = . | G,D                *)
  type eclo = exp * sub   		(* Us = U[s]                  *)
  type bclo = block * sub   		(* Bs = B[s]                  *)
  type cnstr = cnstr ref

  exception Error of string		(* raised if out of space     *)

  (* standard operations on foreign expressions *)
  structure FgnExpStd : sig
    (* convert to internal syntax *)
    structure ToInternal : FGN_OPN where type arg = unit
                                   where type result = exp

    (* apply function to subterms *)
    structure Map : FGN_OPN where type arg = exp -> exp
			    where type result = exp

    (* apply function to subterms, for effect *)
    structure App : FGN_OPN where type arg = exp -> unit
			    where type result = unit

    (* test for equality *)
    structure EqualTo : FGN_OPN where type arg = exp
                                where type result = bool

    (* unify with another term *)
    structure UnifyWith : FGN_OPN where type arg = dec ctx * exp
                                  where type result = fgn_unify

    (* fold a function over the subterms *)
    val fold : (csid * fgn_exp) -> (exp * 'a -> 'a) -> 'a -> 'a
  end

  (* standard operations on foreign constraints *)
  structure FgnCnstrStd : sig
    (* convert to internal syntax *)
    structure ToInternal : FGN_OPN where type arg = unit
                                   where type result = (dec ctx * exp) list

    (* awake *)
    structure Awake : FGN_OPN where type arg = unit
                              where type result = bool

    (* simplify *)
    structure Simplify : FGN_OPN where type arg = unit
                                 where type result = bool
  end
  
  val conDecName   : con_dec -> string
  val conDecParent : con_dec -> mid option
  val conDecImp    : con_dec -> int
  val conDecStatus : con_dec -> status
  val conDecType   : con_dec -> exp
  val conDecBlock  : con_dec -> dctx * dec list
  val conDecUni    : con_dec -> uni

  val strDecName   : str_dec -> string
  val strDecParent : str_dec -> mid option

  val sgnReset     : unit -> unit
  val sgnSize      : unit -> cid * mid

  val sgnAdd   : con_dec -> cid
  val sgnLookup: cid -> con_dec
  val sgnApp   : (cid -> unit) -> unit

  val sgnStructAdd    : str_dec -> mid
  val sgnStructLookup : mid -> str_dec

  val constType   : cid -> exp		(* type of c or d             *)
  val constDef    : cid -> exp		(* definition of d            *)
  val constImp    : cid -> int
  val constStatus : cid -> status
  val constUni    : cid -> uni
  val constBlock  : cid -> dctx * dec list

  (* Declaration Contexts *)

  val ctxDec    : dctx * int -> dec	(* get variable declaration   *)
  val blockDec  : dctx * block * int -> dec 

  (* Explicit substitutions *)

  val id        : sub			(* id                         *)
  val shift     : sub			(* ^                          *)
  val invShift  : sub                   (* ^-1                        *)

  val bvarSub   : int * sub -> front    (* k[s]                       *)
  val frontSub  : front * sub -> front	(* H[s]                       *)
  val decSub    : dec * sub -> dec	(* x:V[s]                     *)
  val blockSub  : block * sub -> block  (* B[s]                       *)

  val comp      : sub * sub -> sub	(* s o s'                     *)
  val dot1      : sub -> sub		(* 1 . (s o ^)                *)
  val invDot1   : sub -> sub		(* (^ o s) o ^-1)             *)

  (* EVar related functions *)

  val newEVar    : dctx * exp -> exp	(* creates X:G|-V, []         *) 
  val newAVar    : unit ->  exp	        (* creates A (bare)           *) 
  val newTypeVar : dctx -> exp		(* creates X:G|-type, []      *)
  val newLVar    : sub * (cid * sub) -> block	
					(* creates B:(l[^k],t)        *) 

  (* Definition related functions *)
  val headOpt : exp -> head option
  val ancestor : exp -> ancestor
  val defAncestor : cid -> ancestor

  (* Type related functions *)

  (* Not expanding type definitions *)
  val targetHeadOpt : exp -> head option (* target type family or NONE *)
  val targetHead : exp -> head           (* target type family         *)

  (* Expanding type definitions *)
  val targetFamOpt : exp -> cid option  (* target type family or NONE *)
  val targetFam : exp -> cid            (* target type family         *)

  (* Used in Flit *)
  val rename : cid * string -> unit

end (* GEN END SIGNATURE DECLARATION *);  (* signature INTSYN *)
