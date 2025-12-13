(* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) IntSyn (structure Global : GLOBAL) :> INTSYN =
struct

  type cid = int                        (* Constant identifier        *)
  type name = string                    (* Variable name              *)
  type mid = int                        (* Structure identifier       *)
  type csid = int                       (* CS module identifier       *)


  (* Contexts *)
  datatype 'a ctx =                     (* Contexts                   *)
    Null                                (* G ::= .                    *)
  | Decl of 'a ctx * 'a                 (*     | G, D                 *)

  (* ctxPop (G) => G'
     Invariant: G = G',D
  *)
  fun ctxPop (Decl (G, D)) = G

  exception Error of string             (* raised if out of space     *)
  (* ctxLookup (G, k) = D, kth declaration in G from right to left
     Invariant: 1 <= k <= |G|, where |G| is length of G
  *)

  fun (* GEN BEGIN FUN FIRST *) ctxLookup (Decl (G', D), 1) = D (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) ctxLookup (Decl (G', _), k') = ctxLookup (G', k'-1) (* GEN END FUN BRANCH *)
(*    | ctxLookup (Null, k') = (print ("Looking up k' = " ^ Int.toString k' ^ "\n"); raise Error "Out of Bounce\n")*)
    (* ctxLookup (Null, k')  should not occur by invariant *)

  (* ctxLength G = |G|, the number of declarations in G *)
  fun ctxLength G =
      let
        fun (* GEN BEGIN FUN FIRST *) ctxLength' (Null, n) = n (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) ctxLength' (Decl(G, _), n)= ctxLength' (G, n+1) (* GEN END FUN BRANCH *)
      in
        ctxLength' (G, 0)
      end

  type fgn_exp = exn                     (* foreign expression representation *)
  exception UnexpectedFgnExp of fgn_exp
                                        (* raised by a constraint solver
                                           if passed an incorrect arg *)

  type fgn_cnstr = exn                   (* foreign unification constraint
                                           representation *)
  exception UnexpectedFgnCnstr of fgn_cnstr
                                        (* raised by a constraint solver
                                           if passed an incorrect arg *)

  datatype depend =                     (* Dependency information     *)
    No                                  (* P ::= No                   *)
  | Maybe                               (*     | Maybe                *)
  | Meta                                (*     | Meta                 *)

  (* Expressions *)

  datatype uni =                        (* Universes:                 *)
    Kind                                (* L ::= Kind                 *)
  | Type                                (*     | Type                 *)

  datatype exp =                        (* Expressions:               *)
    Uni   of uni                        (* U ::= L                    *)
  | Pi    of (dec * depend) * exp       (*     | bPi (D, P). V         *)
  | Root  of head * spine               (*     | C @ S                *)
  | Redex of exp * spine                (*     | U @ S                *)
  | Lam   of dec * exp                  (*     | lam D. U             *)
  | EVar  of exp option ref * dec ctx * exp * (cnstr ref) list ref
                                        (*     | X<I> : G|-V, Cnstr   *)

  | EClo  of exp * sub                  (*     | U[s]                 *)
  | AVar  of exp option ref             (*     | A<I>                 *)
  | NVar  of int                        (*     | n (linear, fully applied) *)
                                        (* grafting variable *)

  | FgnExp of csid * fgn_exp
                                        (*     | (foreign expression) *)

  and head =                            (* Heads:                     *)
    BVar  of int                        (* H ::= k                    *)
  | Const of cid                        (*     | c                    *)
  | Proj  of block * int                (*     | #k(b)                *)
  | Skonst of cid                       (*     | c#                   *)
  | Def   of cid                        (*     | d                    *)
  | NSDef of cid                        (*     | d (non strict)       *)
  | FVar  of name * exp * sub           (*     | F[s]                 *)
  | FgnConst of csid * con_dec           (*     | (foreign constant)   *)

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

  and fgn_unify_residual =                (* Residual of foreign unify  *)
    Assign of dec ctx * exp * exp * sub
    (* perform the assignment G |- X = U [ss] *)
  | Delay of exp * cnstr ref
    (* delay cnstr, associating it with all the rigid EVars in U  *)

  (* Global signature *)

  and con_dec =                          (* Constant declaration       *)
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
              * dec ctx * dec list

  | BlockDef of string * mid option * cid list
                                        (* %block l = (l1 | ... | ln) *)

  | SkoDec of string * mid option * int (* sa: K : kind  or           *)
              * exp * uni               (* sc: A : type               *)

  and ancestor =                        (* Ancestor of d or a         *)
    Anc of cid option * int * cid option (* head(expand(d)), height, head(expand[height](d)) *)
                                        (* NONE means expands to {x:A}B *)

  datatype str_dec =                     (* Structure declaration      *)
      StrDec of string * mid option

  (* Form of constant declaration *)
  datatype con_dec_form =
    FromCS                              (* from constraint domain *)
  | Ordinary                            (* ordinary declaration *)
  | Clause                              (* %clause declaration *)

  (* Type abbreviations *)
  type dctx = dec ctx                   (* G = . | G,D                *)
  type eclo = exp * sub                 (* Us = U[s]                  *)
  type bclo = block * sub               (* Bs = B[s]                  *)
  type cnstr = cnstr ref

(*  exception Error of string             (* raised if out of space     *) *)


  structure FgnExpStd = struct

    structure ToInternal = FgnOpnTable (type arg = unit
                                        type result = exp)

    structure Map = FgnOpnTable (type arg = exp -> exp
                                 type result = exp)

    structure App = FgnOpnTable (type arg = exp -> unit
                                 type result = unit)

    structure EqualTo = FgnOpnTable (type arg = exp
                                     type result = bool)

    structure UnifyWith = FgnOpnTable (type arg = dec ctx * exp
                                       type result = fgn_unify)



    fun fold csfe f b = let
        (* GEN BEGIN TAG OUTSIDE LET *) val r = ref b (* GEN END TAG OUTSIDE LET *)
        fun g U = r := f (U,!r)
    in
        App.apply csfe g ; !r
    end

  end

  structure FgnCnstrStd = struct

    structure ToInternal = FgnOpnTable (type arg = unit
                                        type result = (dec ctx * exp) list)

    structure Awake = FgnOpnTable (type arg = unit
                                   type result = bool)

    structure Simplify = FgnOpnTable (type arg = unit
                                      type result = bool)

  end

  fun (* GEN BEGIN FUN FIRST *) conDecName (ConDec (name, _, _, _, _, _)) = name (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) conDecName (ConDef (name, _, _, _, _, _, _)) = name (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecName (AbbrevDef (name, _, _, _, _, _)) = name (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecName (SkoDec (name, _, _, _, _)) = name (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecName (BlockDec (name, _, _, _)) = name (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecName (BlockDef (name, _, _)) = name (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) conDecParent (ConDec (_, parent, _, _, _, _)) = parent (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) conDecParent (ConDef (_, parent, _, _, _, _, _)) = parent (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecParent (AbbrevDef (_, parent, _, _, _, _)) = parent (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecParent (SkoDec (_, parent, _, _, _)) = parent (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecParent (BlockDec (_, parent, _, _)) = parent (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecParent (BlockDef (_, parent, _)) = parent (* GEN END FUN BRANCH *)


  (* conDecImp (CD) = k

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then k stands for the number of implicit elements.
  *)
  fun (* GEN BEGIN FUN FIRST *) conDecImp (ConDec (_, _, i, _, _, _)) = i (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) conDecImp (ConDef (_, _, i, _, _, _, _)) = i (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecImp (AbbrevDef (_, _, i, _, _, _)) = i (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecImp (SkoDec (_, _, i, _, _)) = i (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecImp (BlockDec (_, _,  _, _)) = 0 (* GEN END FUN BRANCH *)   (* watch out -- carsten *)

  fun (* GEN BEGIN FUN FIRST *) conDecStatus (ConDec (_, _, _, status, _, _)) = status (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) conDecStatus _ = Normal (* GEN END FUN BRANCH *)

  (* conDecType (CD) =  V

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then V is the respective type
  *)
  fun (* GEN BEGIN FUN FIRST *) conDecType (ConDec (_, _, _, _, V, _)) = V (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) conDecType (ConDef (_, _, _, _, V, _, _)) = V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecType (AbbrevDef (_, _, _, _, V, _)) = V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecType (SkoDec (_, _, _, V, _)) = V (* GEN END FUN BRANCH *)


  (* conDecBlock (CD) =  (Gsome, Lpi)

     Invariant:
     If   CD is block definition
     then Gsome is the context of some variables
     and  Lpi is the list of pi variables
  *)
  fun conDecBlock (BlockDec (_, _, Gsome, Lpi)) = (Gsome, Lpi)

  (* conDecUni (CD) =  L

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then L is the respective universe
  *)
  fun (* GEN BEGIN FUN FIRST *) conDecUni (ConDec (_, _, _, _, _, L)) = L (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) conDecUni (ConDef (_, _, _, _, _, L, _)) = L (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecUni (AbbrevDef (_, _, _, _, _, L)) = L (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) conDecUni (SkoDec (_, _, _, _, L)) = L (* GEN END FUN BRANCH *)


  fun strDecName (StrDec (name, _)) = name

  fun strDecParent (StrDec (_, parent)) = parent

  local
    (* GEN BEGIN TAG OUTSIDE LET *) val maxCid = Global.maxCid (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val dummyEntry = ConDec("", NONE, 0, Normal, Uni (Kind), Kind) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val sgnArray = Array.array (maxCid+1, dummyEntry)
      : con_dec Array.array (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val nextCid  = ref(0) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val maxMid = Global.maxMid (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val sgnStructArray = Array.array (maxMid+1, StrDec("", NONE))
      : str_dec Array.array (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val nextMid = ref (0) (* GEN END TAG OUTSIDE LET *)

  in
    (* Invariants *)
    (* Constant declarations are all well-typed *)
    (* Constant declarations are stored in beta-normal form *)
    (* All definitions are strict in all their arguments *)
    (* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
    (* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)

    fun sgnClean (i) = if i >= !nextCid then ()
                       else (Array.update (sgnArray, i, dummyEntry);
                             sgnClean (i+1))

    fun sgnReset () = ((* Fri Dec 20 12:04:24 2002 -fp *)
                       (* this circumvents a space leak *)
                       sgnClean (0);
                       nextCid := 0; nextMid := 0)
    fun sgnSize () = (!nextCid, !nextMid)

    fun sgnAdd (conDec) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val cid = !nextCid (* GEN END TAG OUTSIDE LET *)
        in
          if cid > maxCid
            then raise Error ("Global signature size " ^ Int.toString (maxCid+1) ^ " exceeded")
          else (Array.update (sgnArray, cid, conDec) ;
                nextCid := cid + 1;
                cid)
        end

    (* 0 <= cid < !nextCid *)
    fun sgnLookup (cid) = Array.sub (sgnArray, cid)

    fun sgnApp (f) =
        let
          fun sgnApp' (cid) =
              if cid = !nextCid then () else (f cid; sgnApp' (cid+1))
        in
          sgnApp' (0)
        end

    fun sgnStructAdd (strDec) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val mid = !nextMid (* GEN END TAG OUTSIDE LET *)
        in
          if mid > maxMid
            then raise Error ("Global signature size " ^ Int.toString (maxMid+1) ^ " exceeded")
          else (Array.update (sgnStructArray, mid, strDec) ;
                nextMid := mid + 1;
                mid)
        end

    (* 0 <= mid < !nextMid *)
    fun sgnStructLookup (mid) = Array.sub (sgnStructArray, mid)

    (* A hack used in Flit - jcreed 6/05 *)
    fun rename (cid, new) =
        let
            (* GEN BEGIN TAG OUTSIDE LET *) val newConDec = case sgnLookup cid of
                ConDec (n,m,i,s,e,u) => ConDec(new,m,i,s,e,u)
              | ConDef (n,m,i,e,e',u,a) => ConDef(new,m,i,e,e',u,a)
              | AbbrevDef (n,m,i,e,e',u) => AbbrevDef (new,m,i,e,e',u)
              | BlockDec (n,m,d,d') => BlockDec (new,m,d,d')
              | SkoDec (n,m,i,e,u) => SkoDec (new,m,i,e,u) (* GEN END TAG OUTSIDE LET *)
        in
            Array.update (sgnArray, cid, newConDec)
        end

  end

  fun constDef (d) =
      (case sgnLookup (d)
         of ConDef(_, _, _, U,_, _, _) => U
          | AbbrevDef (_, _, _, U,_, _) => U)

  fun constType (c) = conDecType (sgnLookup c)
  fun constImp (c) = conDecImp (sgnLookup c)
  fun constUni (c) = conDecUni (sgnLookup c)
  fun constBlock (c) = conDecBlock (sgnLookup c)

  fun constStatus (c) =
      (case sgnLookup (c)
         of ConDec (_, _, _, status, _, _) => status
          | _ => Normal)


  (* Explicit Substitutions *)

  (* id = ^0

     Invariant:
     G |- id : G        id is patsub
  *)
  (* GEN BEGIN TAG OUTSIDE LET *) val id = Shift(0) (* GEN END TAG OUTSIDE LET *)

  (* shift = ^1

     Invariant:
     G, V |- ^ : G       ^ is patsub
  *)
  (* GEN BEGIN TAG OUTSIDE LET *) val shift = Shift(1) (* GEN END TAG OUTSIDE LET *)

  (* invShift = ^-1 = _.^0
     Invariant:
     G |- ^-1 : G, V     ^-1 is patsub
  *)
  (* GEN BEGIN TAG OUTSIDE LET *) val invShift = Dot(Undef, id) (* GEN END TAG OUTSIDE LET *)


  (* comp (s1, s2) = s'

     Invariant:
     If   G'  |- s1 : G
     and  G'' |- s2 : G'
     then s'  = s1 o s2
     and  G'' |- s1 o s2 : G

     If  s1, s2 patsub
     then s' patsub
   *)
  fun (* GEN BEGIN FUN FIRST *) comp (Shift (0), s) = s (* GEN END FUN FIRST *)
    (* next line is an optimization *)
    (* roughly 15% on standard suite for Twelf 1.1 *)
    (* Sat Feb 14 10:15:16 1998 -fp *)
    | (* GEN BEGIN FUN BRANCH *) comp (s, Shift (0)) = s (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) comp (Shift (n), Dot (Ft, s)) = comp (Shift (n-1), s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) comp (Shift (n), Shift (m)) = Shift (n+m) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) comp (Dot (Ft, s), s') = Dot (frontSub (Ft, s'), comp (s, s')) (* GEN END FUN BRANCH *)

  (* bvarSub (n, s) = Ft'

      Invariant:
     If    G |- s : G'    G' |- n : V
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
       or  Ft' = ^(n+k)     if  s = Ft1 .. Ftm ^k   and m<n
     and   G |- Ft' : V [s]
  *)
  and (* GEN BEGIN FUN FIRST *) bvarSub (1, Dot(Ft, s)) = Ft (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) bvarSub (n, Dot(Ft, s)) = bvarSub (n-1, s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) bvarSub (n, Shift(k))  = Idx (n+k) (* GEN END FUN BRANCH *)

  (* blockSub (B, s) = B'

     Invariant:
     If   G |- s : G'
     and  G' |- B block
     then G |- B' block
     and  B [s] == B'
  *)
  (* in front of substitutions, first case is irrelevant *)
  (* Sun Dec  2 11:56:41 2001 -fp *)
  and (* GEN BEGIN FUN FIRST *) blockSub (Bidx k, s) =
      (case bvarSub (k, s)
         of Idx k' => Bidx k'
          | Block B => B) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) blockSub (LVar (ref (SOME B), sk, _), s) =
        blockSub (B, comp (sk, s)) (* GEN END FUN BRANCH *)
    (* -fp Sun Dec  1 21:18:30 2002 *)
    (* --cs Sun Dec  1 11:25:41 2002 *)
    (* Since always . |- t : Gsome, discard s *)
    (* where is this needed? *)
    (* Thu Dec  6 20:30:26 2001 -fp !!! *)
    | (* GEN BEGIN FUN BRANCH *) blockSub (LVar (r as ref NONE, sk, (l, t)), s) =
        LVar(r, comp(sk, s), (l, t)) (* GEN END FUN BRANCH *)
      (* was:
        LVar (r, comp(sk, s), (l, comp (t, s)))
        July 22, 2010 -fp -cs
       *)
        (* comp(^k, s) = ^k' for some k' by invariant *)
    | (* GEN BEGIN FUN BRANCH *) blockSub (L as Inst ULs, s') = Inst (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn U => EClo (U, s') (* GEN END FUNCTION EXPRESSION *)) ULs) (* GEN END FUN BRANCH *)
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
  and (* GEN BEGIN FUN FIRST *) frontSub (Idx (n), s) = bvarSub (n, s) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) frontSub (Exp (U), s) = Exp (EClo (U, s)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) frontSub (Undef, s) = Undef (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) frontSub (Block (B), s) = Block (blockSub (B, s)) (* GEN END FUN BRANCH *)

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
  fun decSub (D, Shift(0)) = D
    | decSub (Dec (x, V), s) = Dec (x, EClo (V, s))
  *)
  fun (* GEN BEGIN FUN FIRST *) decSub (Dec (x, V), s) = Dec (x, EClo (V, s)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) decSub (NDec x, s) = NDec x (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) decSub (BDec (n, (l, t)), s) = BDec (n, (l, comp (t, s))) (* GEN END FUN BRANCH *)

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
  fun (* GEN BEGIN FUN FIRST *) dot1 (s as Shift (0)) = s (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) dot1 s = Dot (Idx(1), comp(s, shift)) (* GEN END FUN BRANCH *)

  (* invDot1 (s) = s'
     invDot1 (1. s' o ^) = s'

     Invariant:
     s = 1 . s' o ^
     If G' |- s' : G
     (so G',V[s] |- s : G,V)
  *)
  fun invDot1 (s) = comp (comp(shift, s), invShift)


  (* Declaration Contexts *)

  (* ctxDec (G, k) = x:V
     Invariant:
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)
  fun ctxDec (G, k) =
      let (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
        fun (* GEN BEGIN FUN FIRST *) ctxDec' (Decl (G', Dec (x, V')), 1) = Dec (x, EClo (V', Shift (k))) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) ctxDec' (Decl (G', BDec (n, (l, s))), 1) = BDec (n, (l, comp (s, Shift (k)))) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) ctxDec' (Decl (G', _), k') = ctxDec' (G', k'-1) (* GEN END FUN BRANCH *)
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

  fun blockDec (G, v as (Bidx k), i) =
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val BDec (_, (l, s)) = ctxDec (G, k) (* GEN END TAG OUTSIDE LET *)
      (* G |- s : Gsome *)
      (* GEN BEGIN TAG OUTSIDE LET *) val (Gsome, Lblock) = conDecBlock (sgnLookup l) (* GEN END TAG OUTSIDE LET *)
      fun (* GEN BEGIN FUN FIRST *) blockDec' (t, D :: L, 1, j) = decSub (D, t) (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) blockDec' (t, _ :: L, n, j) =
            blockDec' (Dot (Exp (Root (Proj (v, j), Nil)), t),
                          L, n-1, j+1) (* GEN END FUN BRANCH *)
    in
      blockDec' (s, Lblock, i, 1)
    end


  (* EVar related functions *)

  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)
  fun newEVar (G, V) = EVar(ref NONE, G, V, ref nil)

  (* newAVar G = new AVar (assignable variable) *)
  (* AVars carry no type, ctx, or cnstr *)
  fun newAVar () = AVar(ref NONE)

  (* newTypeVar (G) = X, X new
     where G |- X : type
  *)
  fun newTypeVar (G) = EVar(ref NONE, G, Uni(Type), ref nil)

  (* newLVar (l, s) = (l[s]) *)
  fun newLVar (sk, (cid, t)) = LVar (ref NONE, sk, (cid, t))

  (* Definition related functions *)
  (* headOpt (U) = SOME(H) or NONE, U should be strict, normal *)
  fun (* GEN BEGIN FUN FIRST *) headOpt (Root (H, _)) = SOME(H) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) headOpt (Lam (_, U)) = headOpt U (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) headOpt _ = NONE (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) ancestor' (NONE) = Anc(NONE, 0, NONE) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) ancestor' (SOME(Const(c))) = Anc(SOME(c), 1, SOME(c)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) ancestor' (SOME(Def(d))) =
      (case sgnLookup(d)
         of ConDef(_, _, _, _, _, _, Anc(_, height, cOpt))
            => Anc(SOME(d), height+1, cOpt)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) ancestor' (SOME _) = (* FgnConst possible, BVar impossible by strictness *)
      Anc(NONE, 0, NONE) (* GEN END FUN BRANCH *)
  (* ancestor(U) = ancestor info for d = U *)
  fun ancestor (U) = ancestor' (headOpt U)

  (* defAncestor(d) = ancestor of d, d must be defined *)
  fun defAncestor (d) =
      (case sgnLookup(d)
         of ConDef(_, _, _, _, _, _, anc) => anc)

  (* Type related functions *)

  (* targetHeadOpt (V) = SOME(H) or NONE
     where H is the head of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does not expand type definitions.
  *)
  (* should there possibly be a FgnConst case? also targetFamOpt -kw *)
  fun (* GEN BEGIN FUN FIRST *) targetHeadOpt (Root (H, _)) = SOME(H) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) targetHeadOpt (Pi(_, V)) = targetHeadOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetHeadOpt (Redex (V, S)) = targetHeadOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetHeadOpt (Lam (_, V)) = targetHeadOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetHeadOpt (EVar (ref (SOME(V)),_,_,_)) = targetHeadOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetHeadOpt (EClo (V, s)) = targetHeadOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetHeadOpt _ = NONE (* GEN END FUN BRANCH *)
      (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
      (* Root(Skonst _, _) can't occur *)
  (* targetHead (A) = a
     as in targetHeadOpt, except V must be a valid type
  *)
  fun targetHead (A) = valOf (targetHeadOpt A)

  (* targetFamOpt (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does expand type definitions.
  *)
  fun (* GEN BEGIN FUN FIRST *) targetFamOpt (Root (Const(cid), _)) = SOME(cid) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) targetFamOpt (Pi(_, V)) = targetFamOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetFamOpt (Root (Def(cid), _)) = targetFamOpt (constDef cid) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetFamOpt (Redex (V, S)) = targetFamOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetFamOpt (Lam (_, V)) = targetFamOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetFamOpt (EVar (ref (SOME(V)),_,_,_)) = targetFamOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetFamOpt (EClo (V, s)) = targetFamOpt V (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) targetFamOpt _ = NONE (* GEN END FUN BRANCH *)
      (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
      (* Root(Skonst _, _) can't occur *)
  (* targetFam (A) = a
     as in targetFamOpt, except V must be a valid type
  *)
  fun targetFam (A) = valOf (targetFamOpt A)

end (* GEN END FUNCTOR DECL *);  (* functor IntSyn *)

structure IntSyn :> INTSYN =
  IntSyn (structure Global = Global);
