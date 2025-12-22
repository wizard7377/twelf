(* Internal Syntax *)

(* Author: Frank Pfenning, Carsten Schuermann *)

(* Modified: Roberto Virga *)

module type INTSYN = sig
  type cid = int

  (* Constant identifier        *)
  type mid = int

  (* Structure identifier       *)
  type csid = int

  (* CS module identifier       *)
  type fgnExp = exn

  (* foreign expression representation *)
  exception UnexpectedFgnExp of fgnExp

  (* raised by a constraint solver
					   if passed an incorrect arg *)
  type fgnCnstr = exn

  (* foreign constraint representation *)
  exception UnexpectedFgnCnstr of fgnCnstr

  (* raised by a constraint solver
                                           if passed an incorrect arg *)
  (* Contexts *)
  type 'a ctx = Null | Decl of 'a ctx * 'a

  (*     | G, D                 *)
  val ctxPop : 'a ctx -> 'a ctx
  val ctxLookup : 'a ctx * int -> 'a
  val ctxLength : 'a ctx -> int

  type depend = No | Maybe | Meta

  (*     | Meta                 *)
  (* expressions *)
  type uni = Kind | Type

  (*     | Type                 *)
  type exp =
    | Uni of uni
    | Pi of (dec * depend) * exp
    | Root of head * spine
    | Redex of exp * spine
    | Lam of dec * exp
    | EVar of exp option ref * dec ctx * exp * cnstr ref list ref
    | EClo of exp * sub
    | AVar of exp option ref
    | FgnExp of csid * fgnExp
    | NVar of int

  and head =
    | BVar of int
    | Const of cid
    | Proj of block * int
    | Skonst of cid
    | Def of cid
    | NSDef of cid
    | FVar of string * exp * sub
    | FgnConst of csid * conDec

  and spine = Nil | App of exp * spine | SClo of spine * sub
  and sub = Shift of int | Dot of front * sub
  and front = Idx of int | Exp of exp | Axp of exp | Block of block | Undef

  and dec =
    | Dec of string option * exp
    | BDec of string option * (cid * sub)
    | ADec of string option * int
    | NDec of string option

  and block =
    | Bidx of int
    | LVar of block option ref * sub * (cid * sub)
    | Inst of exp list

  and cnstr =
    | Solved
    | Eqn of dec ctx * exp * exp
    | FgnCnstr of csid * fgnCnstr

  and status =
    | Normal
    | Constraint of csid * (dec ctx * spine * int -> exp option)
    | Foreign of csid * (spine -> exp)

  and fgnUnify = Succeed of fgnUnifyResidual list | Fail

  and fgnUnifyResidual =
    | Assign of dec ctx * exp * exp * sub
    | Delay of exp * cnstr ref

  and conDec =
    | ConDec of
        string
        * mid option
        * int
        * status (* a : K : kind  or           *)
        * exp
        * uni
    | ConDef of
        string
        * mid option
        * int (* a = A : K : kind  or       *)
        * exp
        * exp
        * uni (* d = M : A : type           *)
        * ancestor
    | AbbrevDef of
        string
        * mid option
        * int (* a = A : K : kind  or       *)
        * exp
        * exp
        * uni
    | BlockDec of
        string
        * mid option (* %block l : SOME G1 PI G2   *)
        * dec ctx
        * dec list
    | BlockDef of string * mid option * cid list
    | SkoDec of
        string * mid option * int (* sa: K : kind  or           *) * exp * uni

  and ancestor = Anc of cid option * int * cid option

  (* head(expand(d)), height, head(expand[height](d)) *)
  (* NONE means expands to {x:A}B *)
  type strDec = StrDec of string * mid option

  (* Form of constant declaration *)
  type conDecForm = FromCS | Ordinary | Clause

  (* %clause declaration *)
  (* Type abbreviations *)
  type dctx = dec ctx

  (* G = . | G,D                *)
  type eclo = exp * sub

  (* Us = U[s]                  *)
  type bclo = block * sub

  (* Bs = B[s]                  *)
  type cnstr = cnstr ref

  exception Error of string

  (* raised if out of space     *)
  (* standard operations on foreign expressions *)
  module FgnExpStd : sig
    (* convert to internal syntax *)
    module ToInternal : FGN_OPN with type arg = unit with type result = exp

    (* apply function to subterms *)
    module Map : FGN_OPN with type arg = exp -> exp with type result = exp

    (* apply function to subterms, for_sml effect *)
    module App : FGN_OPN with type arg = exp -> unit with type result = unit

    (* test for_sml equality *)
    module EqualTo : FGN_OPN with type arg = exp with type result = bool

    (* unify with another term *)
    module UnifyWith :
      FGN_OPN with type arg = dec ctx * exp with type result = fgnUnify

    (* fold a function over the subterms *)
    val fold : csid * fgnExp -> (exp * 'a -> 'a) -> 'a -> 'a
  end

  (* standard operations on foreign constraints *)
  module FgnCnstrStd : sig
    (* convert to internal syntax *)
    module ToInternal :
      FGN_OPN with type arg = unit with type result = dec ctx * exp list

    (* awake *)
    module Awake : FGN_OPN with type arg = unit with type result = bool

    (* simplify *)
    module Simplify : FGN_OPN with type arg = unit with type result = bool
  end

  val conDecName : conDec -> string
  val conDecParent : conDec -> mid option
  val conDecImp : conDec -> int
  val conDecStatus : conDec -> status
  val conDecType : conDec -> exp
  val conDecBlock : conDec -> dctx * dec list
  val conDecUni : conDec -> uni
  val strDecName : strDec -> string
  val strDecParent : strDec -> mid option
  val sgnReset : unit -> unit
  val sgnSize : unit -> cid * mid
  val sgnAdd : conDec -> cid
  val sgnLookup : cid -> conDec
  val sgnApp : (cid -> unit) -> unit
  val sgnStructAdd : strDec -> mid
  val sgnStructLookup : mid -> strDec
  val constType : cid -> exp

  (* type of c or d             *)
  val constDef : cid -> exp

  (* definition of d            *)
  val constImp : cid -> int
  val constStatus : cid -> status
  val constUni : cid -> uni
  val constBlock : cid -> dctx * dec list

  (* Declaration Contexts *)
  val ctxDec : dctx * int -> dec

  (* get variable declaration   *)
  val blockDec : dctx * block * int -> dec

  (* Explicit substitutions *)
  val id : sub

  (* id                         *)
  val shift : sub

  (* ^                          *)
  val invShift : sub

  (* ^-1                        *)
  val bvarSub : int * sub -> front

  (* k[s]                       *)
  val frontSub : front * sub -> front

  (* H[s]                       *)
  val decSub : dec * sub -> dec

  (* x:V[s]                     *)
  val blockSub : block * sub -> block

  (* B[s]                       *)
  val comp : sub * sub -> sub

  (* s o s'                     *)
  val dot1 : sub -> sub

  (* 1 . (s o ^)                *)
  val invDot1 : sub -> sub

  (* (^ o s) o ^-1)             *)
  (* EVar related functions *)
  val newEVar : dctx * exp -> exp

  (* creates X:G|-V, []         *)
  val newAVar : unit -> exp

  (* creates A (bare)           *)
  val newTypeVar : dctx -> exp

  (* creates X:G|-type, []      *)
  val newLVar : sub * (cid * sub) -> block

  (* creates B:(l[^k],t)        *)
  (* Definition related functions *)
  val headOpt : exp -> head option
  val ancestor : exp -> ancestor
  val defAncestor : cid -> ancestor

  (* Type related functions *)
  (* Not expanding type definitions *)
  val targetHeadOpt : exp -> head option

  (* target type family or NONE *)
  val targetHead : exp -> head

  (* target type family         *)
  (* Expanding type definitions *)
  val targetFamOpt : exp -> cid option

  (* target type family or NONE *)
  val targetFam : exp -> cid

  (* target type family         *)
  (* Used in Flit *)
  val rename : cid * string -> unit
end

(* signature INTSYN *)
