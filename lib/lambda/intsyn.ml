(* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

module IntSyn (Global : GLOBAL) : INTSYN =
struct

  type cid = int                        (* Constant identifier        *)
  type name = string                    (* Variable name              *)
  type mid = int                        (* Structure identifier       *)
  type csid = int                       (* CS module identifier       *)


  (* Contexts *)
  type 'a Ctx =                     (* Contexts                   *)
    Null                                (* G ::= .                    *)
  | Decl of 'a Ctx * 'a                 (*     | G, D                 *)

  (* ctxPop (G) => G'
     Invariant: G = G',D
  *)
  let rec ctxPop (Decl (G, D)) = G

  exception Error of string             (* raised if out of space     *)
  (* ctxLookup (G, k) = D, kth declaration in G from right to left
     Invariant: 1 <= k <= |G|, where |G| is length of G
  *)

  let rec ctxLookup = function (Decl (G', D), 1) -> D
    | (Decl (G', _), k') -> ctxLookup (G', k'-1)
(*    | ctxLookup (Null, k') = (print ("Looking up k' = " ^ Int.toString k' ^ "\n"); raise Error "Out of Bounce\n")*)
    (* ctxLookup (Null, k')  should not occur by invariant *)

  (* ctxLength G = |G|, the number of declarations in G *)
  let rec ctxLength G =
      let
        let rec ctxLength' = function (Null, n) -> n
          | (Decl(G, _), n) -> ctxLength' (G, n+1)
      in
        ctxLength' (G, 0)
      end

  type fgnexp = exn                     (* foreign expression representation *)
  exception UnexpectedFgnExp of FgnExp
                                        (* raised by a constraint solver
                                           if passed an incorrect arg *)

  type fgncnstr = exn                   (* foreign unification constraint
                                           representation *)
  exception UnexpectedFgnCnstr of FgnCnstr
                                        (* raised by a constraint solver
                                           if passed an incorrect arg *)

  type depend =                     (* Dependency information     *)
    No                                  (* P ::= No                   *)
  | Maybe                               (*     | Maybe                *)
  | Meta                                (*     | Meta                 *)

  (* Expressions *)

  type uni =                        (* Universes:                 *)
    Kind                                (* L ::= Kind                 *)
  | Type                                (*     | Type                 *)

  type exp =                        (* Expressions:               *)
    Uni   of uni                        (* U ::= L                    *)
  | Pi    of (dec * depend) * exp       (*     | bPi (D, P). V         *)
  | Root  of head * spine               (*     | C @ S                *)
  | Redex of exp * spine                (*     | U @ S                *)
  | Lam   of dec * exp                  (*     | lam D. U             *)
  | EVar  of exp option ref * dec Ctx * exp * (cnstr ref) list ref
                                        (*     | X<I> : G|-V, Cnstr   *)

  | EClo  of exp * sub                  (*     | U[s]                 *)
  | AVar  of exp option ref             (*     | A<I>                 *)
  | NVar  of int                        (*     | n (linear, fully applied) *)
                                        (* grafting variable *)

  | FgnExp of csid * fgnExp
                                        (*     | (foreign expression) *)

  and head =                            (* Heads:                     *)
    BVar  of int                        (* H ::= k                    *)
  | Const of cid                        (*     | c                    *)
  | Proj  of block * int                (*     | #k(b)                *)
  | Skonst of cid                       (*     | c#                   *)
  | Def   of cid                        (*     | d                    *)
  | NSDef of cid                        (*     | d (non strict)       *)
  | FVar  of name * exp * sub           (*     | F[s]                 *)
  | FgnConst of csid * conDec           (*     | (foreign constant)   *)

  and spine =                           (* Spines:                    *)
    Nil                                 (* S ::= Nil                  *)
  | App   of exp * spine                (*     | U ; S                *)
  | SClo  of spine * sub                (*     | S[s]                 *)

  and sub =                             (* Explicit substitutions:    *)
    Shift of int                        (* s ::= ^n                   *)
  | Dot   of front * sub                (*     | Ft.s                 *)

  and front =                           (* Fronts:                    *)
    Idx of int                          (* Ft ::= k                   *)
  | Exp of exp                          (*     | U                    *)
  | Axp of exp                          (*     | U (assignable)       *)
  | Block of block                      (*     | _x                   *)
  | Undef                               (*     | _                    *)

  and dec =                             (* Declarations:              *)
    Dec of name option * exp            (* D ::= x:V                  *)
  | BDec of name option * (cid * sub)   (*     | v:l[s]               *)
  | ADec of name option * int           (*     | v[^-d]               *)
  | NDec of name option

  and block =                           (* Blocks:                    *)
    Bidx of int                         (* b ::= v                    *)
  | LVar of block option ref * sub * (cid * sub)
                                        (*     | L(l[^k],t)           *)
  | Inst of exp list                    (*     | u1, ..., Un          *)


  (* Constraints *)

  and cnstr =                           (* Constraint:                *)
    Solved                              (* Cnstr ::= solved           *)
  | Eqn      of dec Ctx * exp * exp     (*         | G|-(U1 == U2)    *)
  | FgnCnstr of csid * fgnCnstr         (*         | (foreign)        *)

  and status =                          (* Status of a constant:      *)
    Normal                              (*   inert                    *)
  | Constraint of csid * (dec Ctx * spine * int -> exp option)
                                        (*   acts as constraint       *)
  | Foreign of csid * (spine -> exp)    (*   is converted to foreign  *)

  and fgnUnify =                        (* Result of foreign unify    *)
    Succeed of fgnUnifyResidual list
    (* succeed with a list of residual operations *)
  | Fail

  and fgnUnifyResidual =                (* Residual of foreign unify  *)
    Assign of dec Ctx * exp * exp * sub
    (* perform the assignment G |- X = U [ss] *)
  | Delay of exp * cnstr ref
    (* delay cnstr, associating it with all the rigid EVars in U  *)

  (* Global module type *)

  and conDec =                          (* Constant declaration       *)
    ConDec of string * mid option * int * status
                                        (* a : K : kind  or           *)
              * exp * uni               (* c : A : type               *)
  | ConDef of string * mid option * int (* a = A : K : kind  or       *)
              * exp * exp * uni         (* d = M : A : type           *)
              * ancestor                (* Ancestor info for d or a   *)
  | AbbrevDef of string * mid option * int
                                        (* a = A : K : kind  or       *)
              * exp * exp * uni         (* d = M : A : type           *)
  | BlockDec of string * mid option     (* %block l : SOME G1 PI G2   *)
              * dec Ctx * dec list

  | BlockDef of string * mid option * cid list
                                        (* %block l = (l1 | ... | ln) *)

  | SkoDec of string * mid option * int (* sa: K : kind  or           *)
              * exp * uni               (* sc: A : type               *)

  and ancestor =                        (* Ancestor of d or a         *)
    Anc of cid option * int * cid option (* head(expand(d)), height, head(expand[height](d)) *)
                                        (* NONE means expands to {x:A}B *)

  type strdec =                     (* Structure declaration      *)
      StrDec of string * mid option

  (* Form of constant declaration *)
  type condecform =
    FromCS                              (* from constraint domain *)
  | Ordinary                            (* ordinary declaration *)
  | Clause                              (* %clause declaration *)

  (* Type abbreviations *)
  type dctx = dec Ctx                   (* G = . | G,D                *)
  type eclo = exp * sub                 (* Us = U[s]                  *)
  type bclo = block * sub               (* Bs = B[s]                  *)
  type cnstr = cnstr ref

(*  exception Error of string             (* raised if out of space     *) *)


  module FgnExpStd = struct

    module ToInternal = FgnOpnTable (type arg = unit
                                        type result = Exp)

    module Map = FgnOpnTable (type arg = Exp -> Exp
                                 type result = Exp)

    module App = FgnOpnTable (type arg = Exp -> unit
                                 type result = unit)

    module EqualTo = FgnOpnTable (type arg = Exp
                                     type result = bool)

    module UnifyWith = FgnOpnTable (type arg = Dec Ctx * Exp
                                       type result = FgnUnify)



    let rec fold csfe f b = let
        let r = ref b
        let rec g U = r := f (U,!r)
    in
        App.apply csfe g ; !r
    end

  end

  module FgnCnstrStd = struct

    module ToInternal = FgnOpnTable (type arg = unit
                                        type result = (Dec Ctx * Exp) list)

    module Awake = FgnOpnTable (type arg = unit
                                   type result = bool)

    module Simplify = FgnOpnTable (type arg = unit
                                      type result = bool)

  end

  let rec conDecName = function (ConDec (name, _, _, _, _, _)) -> name
    | (ConDef (name, _, _, _, _, _, _)) -> name
    | (AbbrevDef (name, _, _, _, _, _)) -> name
    | (SkoDec (name, _, _, _, _)) -> name
    | (BlockDec (name, _, _, _)) -> name
    | (BlockDef (name, _, _)) -> name

  let rec conDecParent = function (ConDec (_, parent, _, _, _, _)) -> parent
    | (ConDef (_, parent, _, _, _, _, _)) -> parent
    | (AbbrevDef (_, parent, _, _, _, _)) -> parent
    | (SkoDec (_, parent, _, _, _)) -> parent
    | (BlockDec (_, parent, _, _)) -> parent
    | (BlockDef (_, parent, _)) -> parent


  (* conDecImp (CD) = k

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then k stands for the number of implicit elements.
  *)
  let rec conDecImp = function (ConDec (_, _, i, _, _, _)) -> i
    | (ConDef (_, _, i, _, _, _, _)) -> i
    | (AbbrevDef (_, _, i, _, _, _)) -> i
    | (SkoDec (_, _, i, _, _)) -> i
    | (BlockDec (_, _,  _, _)) -> 0   (* watch out -- carsten *)

  let rec conDecStatus = function (ConDec (_, _, _, status, _, _)) -> status
    | _ -> Normal

  (* conDecType (CD) =  V

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then V is the respective type
  *)
  let rec conDecType = function (ConDec (_, _, _, _, V, _)) -> V
    | (ConDef (_, _, _, _, V, _, _)) -> V
    | (AbbrevDef (_, _, _, _, V, _)) -> V
    | (SkoDec (_, _, _, V, _)) -> V


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
  let rec conDecUni = function (ConDec (_, _, _, _, _, L)) -> L
    | (ConDef (_, _, _, _, _, L, _)) -> L
    | (AbbrevDef (_, _, _, _, _, L)) -> L
    | (SkoDec (_, _, _, _, L)) -> L


  let rec strDecName (StrDec (name, _)) = name

  let rec strDecParent (StrDec (_, parent)) = parent

  local
    let maxCid = Global.maxCid
    let dummyEntry = ConDec("", NONE, 0, Normal, Uni (Kind), Kind)
    let sgnArray = Array.array (maxCid+1, dummyEntry)
      : ConDec Array.array
    let nextCid  = ref(0)

    let maxMid = Global.maxMid
    let sgnStructArray = Array.array (maxMid+1, StrDec("", NONE))
      : StrDec Array.array
    let nextMid = ref (0)

  in
    (* Invariants *)
    (* Constant declarations are all well-typed *)
    (* Constant declarations are stored in beta-normal form *)
    (* All definitions are strict in all their arguments *)
    (* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
    (* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)

    let rec sgnClean (i) = if i >= !nextCid then ()
                       else (Array.update (sgnArray, i, dummyEntry);
                             sgnClean (i+1))

    let rec sgnReset () = ((* Fri Dec 20 12:04:24 2002 -fp *)
                       (* this circumvents a space leak *)
                       sgnClean (0);
                       nextCid := 0; nextMid := 0)
    let rec sgnSize () = (!nextCid, !nextMid)

    let rec sgnAdd (conDec) =
        let
          let cid = !nextCid
        in
          if cid > maxCid
            then raise Error ("Global module type size " ^ Int.toString (maxCid+1) ^ " exceeded")
          else (Array.update (sgnArray, cid, conDec) ;
                nextCid := cid + 1;
                cid)
        end

    (* 0 <= cid < !nextCid *)
    let rec sgnLookup (cid) = Array.sub (sgnArray, cid)

    let rec sgnApp (f) =
        let
          let rec sgnApp' (cid) =
              if cid = !nextCid then () else (f cid; sgnApp' (cid+1))
        in
          sgnApp' (0)
        end

    let rec sgnStructAdd (strDec) =
        let
          let mid = !nextMid
        in
          if mid > maxMid
            then raise Error ("Global module type size " ^ Int.toString (maxMid+1) ^ " exceeded")
          else (Array.update (sgnStructArray, mid, strDec) ;
                nextMid := mid + 1;
                mid)
        end

    (* 0 <= mid < !nextMid *)
    let rec sgnStructLookup (mid) = Array.sub (sgnStructArray, mid)

    (* A hack used in Flit - jcreed 6/05 *)
    let rec rename (cid, new) =
        let
            let newConDec = case sgnLookup cid of
                ConDec (n,m,i,s,e,u) => ConDec(new,m,i,s,e,u)
              | ConDef (n,m,i,e,e',u,a) => ConDef(new,m,i,e,e',u,a)
              | AbbrevDef (n,m,i,e,e',u) => AbbrevDef (new,m,i,e,e',u)
              | BlockDec (n,m,d,d') => BlockDec (new,m,d,d')
              | SkoDec (n,m,i,e,u) => SkoDec (new,m,i,e,u)
        in
            Array.update (sgnArray, cid, newConDec)
        end

  end

  let rec constDef (d) =
      (case sgnLookup (d)
         of ConDef(_, _, _, U,_, _, _) => U
          | AbbrevDef (_, _, _, U,_, _) => U)

  let rec constType (c) = conDecType (sgnLookup c)
  let rec constImp (c) = conDecImp (sgnLookup c)
  let rec constUni (c) = conDecUni (sgnLookup c)
  let rec constBlock (c) = conDecBlock (sgnLookup c)

  let rec constStatus (c) =
      (case sgnLookup (c)
         of ConDec (_, _, _, status, _, _) => status
          | _ => Normal)


  (* Explicit Substitutions *)

  (* id = ^0

     Invariant:
     G |- id : G        id is patsub
  *)
  let id = Shift(0)

  (* shift = ^1

     Invariant:
     G, V |- ^ : G       ^ is patsub
  *)
  let shift = Shift(1)

  (* invShift = ^-1 = _.^0
     Invariant:
     G |- ^-1 : G, V     ^-1 is patsub
  *)
  let invShift = Dot(Undef, id)


  (* comp (s1, s2) = s'

     Invariant:
     If   G'  |- s1 : G
     and  G'' |- s2 : G'
     then s'  = s1 o s2
     and  G'' |- s1 o s2 : G

     If  s1, s2 patsub
     then s' patsub
   *)
  let rec comp = function (Shift (0), s) -> s
    (* next line is an optimization *)
    (* roughly 15% on standard suite for Twelf 1.1 *)
    (* Sat Feb 14 10:15:16 1998 -fp *)
    | (s, Shift (0)) -> s
    | (Shift (n), Dot (Ft, s)) -> comp (Shift (n-1), s)
    | (Shift (n), Shift (m)) -> Shift (n+m)
    | (Dot (Ft, s), s') -> Dot (frontSub (Ft, s'), comp (s, s'))

  (* bvarSub (n, s) = Ft'

      Invariant:
     If    G |- s : G'    G' |- n : V
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
       or  Ft' = ^(n+k)     if  s = Ft1 .. Ftm ^k   and m<n
     and   G |- Ft' : V [s]
  *)
  and bvarSub (1, Dot(Ft, s)) = Ft
    | bvarSub (n, Dot(Ft, s)) = bvarSub (n-1, s)
    | bvarSub (n, Shift(k))  = Idx (n+k)

  (* blockSub (B, s) = B'

     Invariant:
     If   G |- s : G'
     and  G' |- B block
     then G |- B' block
     and  B [s] == B'
  *)
  (* in front of substitutions, first case is irrelevant *)
  (* Sun Dec  2 11:56:41 2001 -fp *)
  and blockSub (Bidx k, s) =
      (case bvarSub (k, s)
         of Idx k' => Bidx k'
          | Block B => B)
    | blockSub (LVar (ref (SOME B), sk, _), s) =
        blockSub (B, comp (sk, s))
    (* -fp Sun Dec  1 21:18:30 2002 *)
    (* --cs Sun Dec  1 11:25:41 2002 *)
    (* Since always . |- t : Gsome, discard s *)
    (* where is this needed? *)
    (* Thu Dec  6 20:30:26 2001 -fp !!! *)
    | blockSub (LVar (r as ref NONE, sk, (l, t)), s) =
        LVar(r, comp(sk, s), (l, t))
      (* was:
        LVar (r, comp(sk, s), (l, comp (t, s)))
        July 22, 2010 -fp -cs
       *)
        (* comp(^k, s) = ^k' for some k' by invariant *)
    | blockSub (L as Inst ULs, s') = Inst (map (fun U -> EClo (U, s')) ULs)
    (* this should be right but somebody should verify *)

  (* frontSub (Ft, s) = Ft'

     Invariant:
     If   G |- s : G'     G' |- Ft : V
     then Ft' = Ft [s]
     and  G |- Ft' : V [s]

     NOTE: EClo (U, s) might be undefined, so if this is ever
     computed eagerly, we must introduce an "Undefined" exception,
     raise it in whnf and handle it here so Exp (EClo (U, s)) => Undef
  *)
  and frontSub (Idx (n), s) = bvarSub (n, s)
    | frontSub (Exp (U), s) = Exp (EClo (U, s))
    | frontSub (Undef, s) = Undef
    | frontSub (Block (B), s) = Block (blockSub (B, s))

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
  (* undo for now Sat Feb 14 20:22:29 1998 -fp *)
  (*
  let rec decSub = function (D, Shift(0)) -> D
    | (Dec (x, V), s) -> Dec (x, EClo (V, s))
  *)
  let rec decSub = function (Dec (x, V), s) -> Dec (x, EClo (V, s))
    | (NDec x, s) -> NDec x
    | (BDec (n, (l, t)), s) -> BDec (n, (l, comp (t, s)))

  (* dot1 (s) = s'

     Invariant:
     If   G |- s : G'
     then s' = 1. (s o ^)
     and  for all V s.t.  G' |- V : L
          G, V[s] |- s' : G', V

     If s patsub then s' patsub
  *)
  (* first line is an optimization *)
  (* roughly 15% on standard suite for Twelf 1.1 *)
  (* Sat Feb 14 10:16:16 1998 -fp *)
  let rec dot1 = function (s as Shift (0)) -> s
    | s -> Dot (Idx(1), comp(s, shift))

  (* invDot1 (s) = s'
     invDot1 (1. s' o ^) = s'

     Invariant:
     s = 1 . s' o ^
     If G' |- s' : G
     (so G',V[s] |- s : G,V)
  *)
  let rec invDot1 (s) = comp (comp(shift, s), invShift)


  (* Declaration Contexts *)

  (* ctxDec (G, k) = x:V
     Invariant:
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)
  let rec ctxDec (G, k) =
      let (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
        let rec ctxDec' = function (Decl (G', Dec (x, V')), 1) -> Dec (x, EClo (V', Shift (k)))
          | (Decl (G', BDec (n, (l, s))), 1) -> BDec (n, (l, comp (s, Shift (k))))
          | (Decl (G', _), k') -> ctxDec' (G', k'-1)
         (* ctxDec' (Null, k')  should not occur by invariant *)
      in
        ctxDec' (G, k)
      end

  (* blockDec (G, v, i) = V

     Invariant:
     If   G (v) = l[s]
     and  Sigma (l) = SOME Gsome BLOCK Lblock
     and  G |- s : Gsome
     then G |- pi (v, i) : V
  *)

  let rec blockDec (G, v as (Bidx k), i) =
    let
      let BDec (_, (l, s)) = ctxDec (G, k)
      (* G |- s : Gsome *)
      let (Gsome, Lblock) = conDecBlock (sgnLookup l)
      let rec blockDec' = function (t, D :: L, 1, j) -> decSub (D, t)
        | (t, _ :: L, n, j) -> 
            blockDec' (Dot (Exp (Root (Proj (v, j), Nil)), t),
                          L, n-1, j+1)
    in
      blockDec' (s, Lblock, i, 1)
    end


  (* EVar related functions *)

  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)
  let rec newEVar (G, V) = EVar(ref NONE, G, V, ref nil)

  (* newAVar G = new AVar (assignable variable) *)
  (* AVars carry no type, ctx, or cnstr *)
  let rec newAVar () = AVar(ref NONE)

  (* newTypeVar (G) = X, X new
     where G |- X : type
  *)
  let rec newTypeVar (G) = EVar(ref NONE, G, Uni(Type), ref nil)

  (* newLVar (l, s) = (l[s]) *)
  let rec newLVar (sk, (cid, t)) = LVar (ref NONE, sk, (cid, t))

  (* Definition related functions *)
  (* headOpt (U) = SOME(H) or NONE, U should be strict, normal *)
  let rec headOpt = function (Root (H, _)) -> SOME(H)
    | (Lam (_, U)) -> headOpt U
    | _ -> NONE

  let rec ancestor' = function (NONE) -> Anc(NONE, 0, NONE)
    | (SOME(Const(c))) -> Anc(SOME(c), 1, SOME(c))
    | (SOME(Def(d))) -> 
      (case sgnLookup(d)
         of ConDef(_, _, _, _, _, _, Anc(_, height, cOpt))
            => Anc(SOME(d), height+1, cOpt))
    | (SOME _) -> (* FgnConst possible, BVar impossible by strictness *)
      Anc(NONE, 0, NONE)
  (* ancestor(U) = ancestor info for d = U *)
  let rec ancestor (U) = ancestor' (headOpt U)

  (* defAncestor(d) = ancestor of d, d must be defined *)
  let rec defAncestor (d) =
      (case sgnLookup(d)
         of ConDef(_, _, _, _, _, _, anc) => anc)

  (* Type related functions *)

  (* targetHeadOpt (V) = SOME(H) or NONE
     where H is the head of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does not expand type definitions.
  *)
  (* should there possibly be a FgnConst case? also targetFamOpt -kw *)
  let rec targetHeadOpt = function (Root (H, _)) -> SOME(H)
    | (Pi(_, V)) -> targetHeadOpt V
    | (Redex (V, S)) -> targetHeadOpt V
    | (Lam (_, V)) -> targetHeadOpt V
    | (EVar (ref (SOME(V)),_,_,_)) -> targetHeadOpt V
    | (EClo (V, s)) -> targetHeadOpt V
    | _ -> NONE
      (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
      (* Root(Skonst _, _) can't occur *)
  (* targetHead (A) = a
     as in targetHeadOpt, except V must be a valid type
  *)
  let rec targetHead (A) = valOf (targetHeadOpt A)

  (* targetFamOpt (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does expand type definitions.
  *)
  let rec targetFamOpt = function (Root (Const(cid), _)) -> SOME(cid)
    | (Pi(_, V)) -> targetFamOpt V
    | (Root (Def(cid), _)) -> targetFamOpt (constDef cid)
    | (Redex (V, S)) -> targetFamOpt V
    | (Lam (_, V)) -> targetFamOpt V
    | (EVar (ref (SOME(V)),_,_,_)) -> targetFamOpt V
    | (EClo (V, s)) -> targetFamOpt V
    | _ -> NONE
      (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
      (* Root(Skonst _, _) can't occur *)
  (* targetFam (A) = a
     as in targetFamOpt, except V must be a valid type
  *)
  let rec targetFam (A) = valOf (targetFamOpt A)

end;; (* functor IntSyn *)

(IntSyn : INTSYN) =
  IntSyn (module Global = Global);
