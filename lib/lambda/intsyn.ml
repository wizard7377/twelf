open Basis ;; 
(* Internal Syntax *)

(* Author: Frank Pfenning, Carsten Schuermann *)

(* Modified: Roberto Virga *)
include Fgnopn

module type INTSYN = sig
  type cid = int

  (* Constant identifier        *)
  type mid = int

  (* Structure identifier       *)
  type csid = int

  (* Cs.CS module identifier       *)
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
  type cnstr' = cnstr ref

  exception Error of string

  (* raised if out of space     *)
  (* standard operations on foreign expressions *)
  module FgnExpStd : sig
    (* convert to internal syntax *)
    module ToInternal :
      Fgnopn.FGN_OPN with type arg = unit with type result = exp

    (* apply function to subterms *)
    module Map :
      Fgnopn.FGN_OPN with type arg = exp -> exp with type result = exp

    (* apply function to subterms, for_sml effect *)
    module App :
      Fgnopn.FGN_OPN with type arg = exp -> unit with type result = unit

    (* test for_sml equality *)
    module EqualTo : Fgnopn.FGN_OPN with type arg = exp with type result = bool

    (* unify with another term *)
    module UnifyWith :
      Fgnopn.FGN_OPN with type arg = dec ctx * exp with type result = fgnUnify

    (* fold a function over the subterms *)
    val fold : csid * fgnExp -> (exp * 'a -> 'a) -> 'a -> 'a
  end

  (* standard operations on foreign constraints *)
  module FgnCnstrStd : sig
    (* convert to internal syntax *)
    module ToInternal :
      Fgnopn.FGN_OPN with type arg = unit with type result = dec ctx * exp list

    (* awake *)
    module Awake : Fgnopn.FGN_OPN with type arg = unit with type result = bool

    (* simplify *)
    module Simplify :
      Fgnopn.FGN_OPN with type arg = unit with type result = bool
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
(* Internal Syntax *)

(* Author: Frank Pfenning, Carsten Schuermann *)

(* Modified: Roberto Virga *)

module IntSyn (Global : Global.GLOBAL) : INTSYN = struct
  type cid = int
  (* Constant identifier        *)

  type name = string
  (* Variable name              *)

  type mid = int
  (* Structure identifier       *)

  type csid = int
  (* Cs.CS module identifier       *)

  (* Contexts *)

  type 'a ctx = Null | Decl of 'a ctx * 'a
  (*     | G, D                 *)

  (* ctxPop (G) => G'
     Invariant: G = G',D
  *)

  let rec ctxPop (Decl (G, D)) = G

  exception Error of string
  (* raised if out of space     *)

  (* ctxLookup (G, k) = D, kth declaration in G from right to left
     Invariant: 1 <= k <= |G|, where |G| is length of G
  *)

  let rec ctxLookup = function
    | Decl (G', D), 1 -> D
    | Decl (G', _), k' -> ctxLookup (G', k' - 1)
  (*    | ctxLookup (Null, k') = (print ("Looking up k' = " ^ Int.toString k' ^ "\n"); raise Error "Out of Bounce\n")*)

  (* ctxLookup (Null, k')  should not occur by invariant *)

  (* ctxLength G = |G|, the number of declarations in G *)

  let rec ctxLength G =
    let rec ctxLength' = function
      | Null, n -> n
      | Decl (G, _), n -> ctxLength' (G, n + 1)
    in
    ctxLength' (G, 0)

  type fgnExp = exn
  (* foreign expression representation *)

  exception UnexpectedFgnExp of fgnExp
  (* raised by a constraint solver
                                           if passed an incorrect arg *)

  type fgnCnstr = exn
  (* foreign unification constraint
                                           representation *)

  exception UnexpectedFgnCnstr of fgnCnstr
  (* raised by a constraint solver
                                           if passed an incorrect arg *)

  type depend = No | Maybe | Meta
  (*     | Meta                 *)

  (* Expressions *)

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
    | NVar of int
    | FgnExp of csid * fgnExp

  and head =
    | BVar of int
    | Const of cid
    | Proj of block * int
    | Skonst of cid
    | Def of cid
    | NSDef of cid
    | FVar of name * exp * sub
    | FgnConst of csid * conDec

  and spine = Nil | App of exp * spine | SClo of spine * sub
  and sub = Shift of int | Dot of front * sub
  and front = Idx of int | Exp of exp | Axp of exp | Block of block | Undef

  and dec =
    | Dec of name option * exp
    | BDec of name option * (cid * sub)
    | ADec of name option * int
    | NDec of name option

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
  (*  exception Error of string             (* raised if out of space     *) *)

  module FgnExpStd = struct
    module ToInternal = FgnOpnTable
    module Map = FgnOpnTable
    module App = FgnOpnTable
    module EqualTo = FgnOpnTable
    module UnifyWith = FgnOpnTable

    let rec fold csfe f b =
      let r = ref b in
      let rec g U = r := f (U, !r) in
      App.apply csfe g;
      !r
  end

  module FgnCnstrStd = struct
    module ToInternal = FgnOpnTable
    module Awake = FgnOpnTable
    module Simplify = FgnOpnTable
  end

  let rec conDecName = function
    | ConDec (name, _, _, _, _, _) -> name
    | ConDef (name, _, _, _, _, _, _) -> name
    | AbbrevDef (name, _, _, _, _, _) -> name
    | SkoDec (name, _, _, _, _) -> name
    | BlockDec (name, _, _, _) -> name
    | BlockDef (name, _, _) -> name

  let rec conDecParent = function
    | ConDec (_, parent, _, _, _, _) -> parent
    | ConDef (_, parent, _, _, _, _, _) -> parent
    | AbbrevDef (_, parent, _, _, _, _) -> parent
    | SkoDec (_, parent, _, _, _) -> parent
    | BlockDec (_, parent, _, _) -> parent
    | BlockDef (_, parent, _) -> parent
  (* conDecImp (CD) = k

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then k stands for_sml the number of implicit elements.
  *)

  let rec conDecImp = function
    | ConDec (_, _, i, _, _, _) -> i
    | ConDef (_, _, i, _, _, _, _) -> i
    | AbbrevDef (_, _, i, _, _, _) -> i
    | SkoDec (_, _, i, _, _) -> i
    | BlockDec (_, _, _, _) -> 0
  (* watch out -- carsten *)

  let rec conDecStatus = function
    | ConDec (_, _, _, status, _, _) -> status
    | _ -> Normal
  (* conDecType (CD) =  V

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then V is the respective type
  *)

  let rec conDecType = function
    | ConDec (_, _, _, _, V, _) -> V
    | ConDef (_, _, _, _, V, _, _) -> V
    | AbbrevDef (_, _, _, _, V, _) -> V
    | SkoDec (_, _, _, V, _) -> V
  (* conDecBlock (CD) =  (Gsome, Lpi)

     Invariant:
     If   CD is block definition
     then Gsome is the context of some variables
     and  Lpi is the list of pi variables
  *)

  let rec conDecBlock (BlockDec (_, _, Gsome, Lpi)) = (Gsome, Lpi)
  (* conDecUni (CD) =  L

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then L is the respective universe
  *)

  let rec conDecUni = function
    | ConDec (_, _, _, _, _, L) -> L
    | ConDef (_, _, _, _, _, L, _) -> L
    | AbbrevDef (_, _, _, _, _, L) -> L
    | SkoDec (_, _, _, _, L) -> L

  let rec strDecName (StrDec (name, _)) = name
  let rec strDecParent (StrDec (_, parent)) = parent
  let maxCid = Global.maxCid
  let dummyEntry = ConDec ("", None, 0, Normal, Uni Kind, Kind)
  let sgnArray = (Array.array (maxCid + 1, dummyEntry) : conDec Array.array)
  let nextCid = ref 0
  let maxMid = Global.maxMid

  let sgnStructArray =
    (Array.array (maxMid + 1, StrDec ("", None)) : strDec Array.array)

  let nextMid = ref 0
  (* Invariants *)

  (* Constant declarations are all well-typed *)

  (* Constant declarations are stored in beta-normal form *)

  (* All definitions are strict in all their arguments *)

  (* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)

  (* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)

  let rec sgnClean i =
    if i >= !nextCid then ()
    else (
      Array.update (sgnArray, i, dummyEntry);
      sgnClean (i + 1))

  let rec sgnReset () =
    (* Fri Dec 20 12:04:24 2002 -fp *)
    (* this circumvents a space leak *)
    sgnClean 0;
    nextCid := 0;
    nextMid := 0

  let rec sgnSize () = (!nextCid, !nextMid)

  let rec sgnAdd conDec =
    let cid = !nextCid in
    if cid > maxCid then
      raise
        (Error
           ("Global signature size " ^ Int.toString (maxCid + 1) ^ " exceeded"))
    else (
      Array.update (sgnArray, cid, conDec);
      nextCid := cid + 1;
      cid)
  (* 0 <= cid < !nextCid *)

  let rec sgnLookup cid = Array.sub (sgnArray, cid)

  let rec sgnApp f =
    let rec sgnApp' cid =
      if cid = !nextCid then ()
      else (
        f cid;
        sgnApp' (cid + 1))
    in
    sgnApp' 0

  let rec sgnStructAdd strDec =
    let mid = !nextMid in
    if mid > maxMid then
      raise
        (Error
           ("Global signature size " ^ Int.toString (maxMid + 1) ^ " exceeded"))
    else (
      Array.update (sgnStructArray, mid, strDec);
      nextMid := mid + 1;
      mid)
  (* 0 <= mid < !nextMid *)

  let rec sgnStructLookup mid = Array.sub (sgnStructArray, mid)
  (* A hack used in Flit - jcreed 6/05 *)

  let rec rename (cid, new_) =
    let newConDec =
      match sgnLookup cid with
      | ConDec (n, m, i, s, e, u) -> ConDec (new_, m, i, s, e, u)
      | ConDef (n, m, i, e, e', u, a) -> ConDef (new_, m, i, e, e', u, a)
      | AbbrevDef (n, m, i, e, e', u) -> AbbrevDef (new_, m, i, e, e', u)
      | BlockDec (n, m, d, d') -> BlockDec (new_, m, d, d')
      | SkoDec (n, m, i, e, u) -> SkoDec (new_, m, i, e, u)
    in
    Array.update (sgnArray, cid, newConDec)

  let rec constDef d =
    match sgnLookup d with
    | ConDef (_, _, _, U, _, _, _) -> U
    | AbbrevDef (_, _, _, U, _, _) -> U

  let rec constType c = conDecType (sgnLookup c)
  let rec constImp c = conDecImp (sgnLookup c)
  let rec constUni c = conDecUni (sgnLookup c)
  let rec constBlock c = conDecBlock (sgnLookup c)

  let rec constStatus c =
    match sgnLookup c with
    | ConDec (_, _, _, status, _, _) -> status
    | _ -> Normal
  (* Explicit Substitutions *)

  (* id = ^0

     Invariant:
     G |- id : G        id is patsub
  *)

  let id = Shift 0
  (* shift = ^1

     Invariant:
     G, V |- ^ : G       ^ is patsub
  *)

  let shift = Shift 1
  (* invShift = ^-1 = _.^0
     Invariant:
     G |- ^-1 : G, V     ^-1 is patsub
  *)

  let invShift = Dot (Undef, id)
  (* comp (s1, s2) = s'

     Invariant:
     If   G'  |- s1 : G
     and  G'' |- s2 : G'
     then s'  = s1 o s2
     and  G'' |- s1 o s2 : G

     If  s1, s2 patsub
     then s' patsub
   *)

  let rec comp = function
    | Shift 0, s -> s
    | s, Shift 0 -> s
    | Shift n, Dot (Ft, s) -> comp (Shift (n - 1), s)
    | Shift n, Shift m -> Shift (n + m)
    | Dot (Ft, s), s' -> Dot (frontSub (Ft, s'), comp (s, s'))

  and bvarSub = function
    | 1, Dot (Ft, s) -> Ft
    | n, Dot (Ft, s) -> bvarSub (n - 1, s)
    | n, Shift k -> Idx (n + k)

  and blockSub = function
    | Bidx k, s -> (
        match bvarSub (k, s) with Idx k' -> Bidx k' | Block B -> B)
    | LVar ({ contents = Some B }, sk, _), s -> blockSub (B, comp (sk, s))
    | LVar (r, sk, (l, t)), s -> LVar (r, comp (sk, s), (l, t))
    | L, s' -> Inst (map (fun U -> EClo (U, s')) ULs)

  and frontSub = function
    | Idx n, s -> bvarSub (n, s)
    | Exp U, s -> Exp (EClo (U, s))
    | Undef, s -> Undef
    | Block B, s -> Block (blockSub (B, s))
  (* decSub (x:V, s) = D'

     Invariant:
     If   G  |- s : G'    G' |- V : L
     then D' = x:V[s]
     and  G  |- V[s] : L
  *)

  (* First line is an optimization suggested by cs *)

  (* D[id] = D *)

  (* Sat Feb 14 18:37:44 1998 -fp *)

  (* seems to have no statistically significant effect *)

  (* undo for_sml now Sat Feb 14 20:22:29 1998 -fp *)

  (*
  fun decSub (D, Shift(0)) = D
    | decSub (Dec (x, V), s) = Dec (x, EClo (V, s))
  *)

  let rec decSub = function
    | Dec (x, V), s -> Dec (x, EClo (V, s))
    | NDec x, s -> NDec x
    | BDec (n, (l, t)), s -> BDec (n, (l, comp (t, s)))
  (* dot1 (s) = s'

     Invariant:
     If   G |- s : G'
     then s' = 1. (s o ^)
     and  for_sml all V s.t.  G' |- V : L
          G, V[s] |- s' : G', V

     If s patsub then s' patsub
  *)

  (* first line is an optimization *)

  (* roughly 15% on standard suite for_sml Twelf 1.1 *)

  (* Sat Feb 14 10:16:16 1998 -fp *)

  let rec dot1 = function s -> s | s -> Dot (Idx 1, comp (s, shift))
  (* invDot1 (s) = s'
     invDot1 (1. s' o ^) = s'

     Invariant:
     s = 1 . s' o ^
     If G' |- s' : G
     (so G',V[s] |- s : G,V)
  *)

  let rec invDot1 s = comp (comp (shift, s), invShift)
  (* Declaration Contexts *)

  (* ctxDec (G, k) = x:V
     Invariant:
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)

  let rec ctxDec (G, k) =
    (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
    (* ctxDec' (Null, k')  should not occur by invariant *)
    let rec ctxDec' = function
      | Decl (G', Dec (x, V')), 1 -> Dec (x, EClo (V', Shift k))
      | Decl (G', BDec (n, (l, s))), 1 -> BDec (n, (l, comp (s, Shift k)))
      | Decl (G', _), k' -> ctxDec' (G', k' - 1)
    in
    ctxDec' (G, k)
  (* blockDec (G, v, i) = V

     Invariant:
     If   G (v) = l[s]
     and  Sigma (l) = SOME Gsome BLOCK Lblock
     and  G |- s : Gsome
     then G |- pi (v, i) : V
  *)

  let rec blockDec (G, v, i) =
    (* G |- s : Gsome *)
    let (BDec (_, (l, s))) = ctxDec (G, k) in
    let Gsome, Lblock = conDecBlock (sgnLookup l) in
    let rec blockDec' = function
      | t, D :: L, 1, j -> decSub (D, t)
      | t, _ :: L, n, j ->
          blockDec' (Dot (Exp (Root (Proj (v, j), Nil)), t), L, n - 1, j + 1)
    in
    blockDec' (s, Lblock, i, 1)
  (* EVar related functions *)

  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)

  let rec newEVar (G, V) = EVar (ref None, G, V, ref [])
  (* newAVar G = new AVar (assignable variable) *)

  (* AVars carry no type, ctx, or cnstr *)

  let rec newAVar () = AVar (ref None)
  (* newTypeVar (G) = X, X new
     where G |- X : type
  *)

  let rec newTypeVar G = EVar (ref None, G, Uni Type, ref [])
  (* newLVar (l, s) = (l[s]) *)

  let rec newLVar (sk, (cid, t)) = LVar (ref None, sk, (cid, t))
  (* Definition related functions *)

  (* headOpt (U) = SOME(H) or NONE, U should be strict, normal *)

  let rec headOpt = function
    | Root (H, _) -> Some H
    | Lam (_, U) -> headOpt U
    | _ -> None

  let rec ancestor' = function
    | None -> Anc (None, 0, None)
    | Some (Const c) -> Anc (Some c, 1, Some c)
    | Some (Def d) -> (
        match sgnLookup d with
        | ConDef (_, _, _, _, _, _, Anc (_, height, cOpt)) ->
            Anc (Some d, height + 1, cOpt))
    | Some _ -> Anc (None, 0, None)
  (* ancestor(U) = ancestor info for_sml d = U *)

  let rec ancestor U = ancestor' (headOpt U)
  (* defAncestor(d) = ancestor of d, d must be defined *)

  let rec defAncestor d =
    match sgnLookup d with ConDef (_, _, _, _, _, _, anc) -> anc
  (* Type related functions *)

  (* targetHeadOpt (V) = SOME(H) or NONE
     where H is the head of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does not expand type definitions.
  *)

  (* should there possibly be a FgnConst case? also targetFamOpt -kw *)

  let rec targetHeadOpt = function
    | Root (H, _) -> Some H
    | Pi (_, V) -> targetHeadOpt V
    | Redex (V, S) -> targetHeadOpt V
    | Lam (_, V) -> targetHeadOpt V
    | EVar ({ contents = Some V }, _, _, _) -> targetHeadOpt V
    | EClo (V, s) -> targetHeadOpt V
    | _ -> None
  (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)

  (* Root(Skonst _, _) can't occur *)

  (* targetHead (A) = in targetHeadOpt, except V must be a valid type
  *)

  let rec targetHead A = valOf (targetHeadOpt A)
  (* targetFamOpt (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does expand type definitions.
  *)

  let rec targetFamOpt = function
    | Root (Const cid, _) -> Some cid
    | Pi (_, V) -> targetFamOpt V
    | Root (Def cid, _) -> targetFamOpt (constDef cid)
    | Redex (V, S) -> targetFamOpt V
    | Lam (_, V) -> targetFamOpt V
    | EVar ({ contents = Some V }, _, _, _) -> targetFamOpt V
    | EClo (V, s) -> targetFamOpt V
    | _ -> None
  (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)

  (* Root(Skonst _, _) can't occur *)

  (* targetFam (A) = in targetFamOpt, except V must be a valid type
  *)

  let rec targetFam A = valOf (targetFamOpt A)
end

(* functor IntSyn *)

module IntSyn : INTSYN = IntSyn (struct
  module Global = Global
end)
