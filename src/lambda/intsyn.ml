IntSyn  Global GLOBAL     INTSYN  struct type Cid(* Constant identifier        *)
type Name(* Variable name              *)
type Mid(* Structure identifier       *)
type Csid(* CS module identifier       *)
(* Contexts *)
type Ctx(*     | G, D                 *)
(* ctxPop (G) => G'
     Invariant: G = G',D
  *)
let rec ctxPop(decl (g,  , d)) gexception (* raised if out of space     *)
(* ctxLookup (G, k) = D, kth declaration in G from right to left
     Invariant: 1 <= k <= |G|, where |G| is length of G
  *)
let rec ctxLookup(decl (g',  , d),  , 1) d ctxLookup(decl (g',  , _),  , k') ctxLookup (g',  , k' - 1)(*    | ctxLookup (Null, k') = (print ("Looking up k' = " ^ Int.toString k' ^ "\n"); raise Error "Out of Bounce\n")*)
(* ctxLookup (Null, k')  should not occur by invariant *)
(* ctxLength G = |G|, the number of declarations in G *)
let rec ctxLengthg let let rec ctxLength'(null,  , n) n ctxLength'(decl (g,  , _),  , n) ctxLength' (g,  , n + 1) in ctxLength' (g,  , 0)type FgnExp(* foreign expression representation *)
exception (* raised by a constraint solver
                                           if passed an incorrect arg *)
type FgnCnstr(* foreign unification constraint
                                           representation *)
exception (* raised by a constraint solver
                                           if passed an incorrect arg *)
type Depend(*     | Meta                 *)
(* Expressions *)
type Uni(*     | Type                 *)
type Exp(*     | (foreign expression) *)
 Head(*     | (foreign constant)   *)
 Spine(*     | S[s]                 *)
 Sub(*     | Ft.s                 *)
 Front(*     | _                    *)
 Dec Block(*     | u1, ..., Un          *)
(* Constraints *)
 Cnstr(*         | (foreign)        *)
 Status(*   is converted to foreign  *)
 FgnUnify FgnUnifyResidual(* delay cnstr, associating it with all the rigid EVars in U  *)
(* Global signature *)
 ConDec(* sc: A : type               *)
 Ancestor(* head(expand(d)), height, head(expand[height](d)) *)
(* NONE means expands to {x:A}B *)
type StrDec(* Form of constant declaration *)
type ConDecForm(* %clause declaration *)
(* Type abbreviations *)
type Dctx(* G = . | G,D                *)
type Eclo(* Us = U[s]                  *)
type Bclo(* Bs = B[s]                  *)
type Cnstr(*  exception Error of string             (* raised if out of space     *) *)
module module let rec conDecName(conDec (name,  , _,  , _,  , _,  , _,  , _)) name conDecName(conDef (name,  , _,  , _,  , _,  , _,  , _,  , _)) name conDecName(abbrevDef (name,  , _,  , _,  , _,  , _,  , _)) name conDecName(skoDec (name,  , _,  , _,  , _,  , _)) name conDecName(blockDec (name,  , _,  , _,  , _)) name conDecName(blockDef (name,  , _,  , _)) namelet rec conDecParent(conDec (_,  , parent,  , _,  , _,  , _,  , _)) parent conDecParent(conDef (_,  , parent,  , _,  , _,  , _,  , _,  , _)) parent conDecParent(abbrevDef (_,  , parent,  , _,  , _,  , _,  , _)) parent conDecParent(skoDec (_,  , parent,  , _,  , _,  , _)) parent conDecParent(blockDec (_,  , parent,  , _,  , _)) parent conDecParent(blockDef (_,  , parent,  , _)) parent(* conDecImp (CD) = k

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then k stands for the number of implicit elements.
  *)
let rec conDecImp(conDec (_,  , _,  , i,  , _,  , _,  , _)) i conDecImp(conDef (_,  , _,  , i,  , _,  , _,  , _,  , _)) i conDecImp(abbrevDef (_,  , _,  , i,  , _,  , _,  , _)) i conDecImp(skoDec (_,  , _,  , i,  , _,  , _)) i conDecImp(blockDec (_,  , _,  , _,  , _)) 0(* watch out -- carsten *)
let rec conDecStatus(conDec (_,  , _,  , _,  , status,  , _,  , _)) status conDecStatus_ normal(* conDecType (CD) =  V

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then V is the respective type
  *)
let rec conDecType(conDec (_,  , _,  , _,  , _,  , v,  , _)) v conDecType(conDef (_,  , _,  , _,  , _,  , v,  , _,  , _)) v conDecType(abbrevDef (_,  , _,  , _,  , _,  , v,  , _)) v conDecType(skoDec (_,  , _,  , _,  , v,  , _)) v(* conDecBlock (CD) =  (Gsome, Lpi)

     Invariant:
     If   CD is block definition
     then Gsome is the context of some variables
     and  Lpi is the list of pi variables
  *)
let rec conDecBlock(blockDec (_,  , _,  , gsome,  , lpi)) (gsome,  , lpi)(* conDecUni (CD) =  L

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then L is the respective universe
  *)
let rec conDecUni(conDec (_,  , _,  , _,  , _,  , _,  , l)) l conDecUni(conDef (_,  , _,  , _,  , _,  , _,  , l,  , _)) l conDecUni(abbrevDef (_,  , _,  , _,  , _,  , _,  , l)) l conDecUni(skoDec (_,  , _,  , _,  , _,  , l)) llet rec strDecName(strDec (name,  , _)) namelet rec strDecParent(strDec (_,  , parent)) parentlet  inlet  inlet  inlet  inlet  inlet  inlet  in(* Invariants *)
(* Constant declarations are all well-typed *)
(* Constant declarations are stored in beta-normal form *)
(* All definitions are strict in all their arguments *)
(* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
(* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)
let rec sgnClean(i) if i >= ! nextCid then () else (update (sgnArray,  , i,  , dummyEntry); sgnClean (i + 1))let rec sgnReset() ((* Fri Dec 20 12:04:24 2002 -fp *)
(* this circumvents a space leak *)
sgnClean (0); nextCid := 0; nextMid := 0)let rec sgnSize() (! nextCid,  , ! nextMid)let rec sgnAdd(conDec) let let  in in if cid > maxCid then raise (error ("Global signature size " ^ toString (maxCid + 1) ^ " exceeded")) else (update (sgnArray,  , cid,  , conDec); nextCid := cid + 1; cid)(* 0 <= cid < !nextCid *)
let rec sgnLookup(cid) sub (sgnArray,  , cid)let rec sgnApp(f) let let rec sgnApp'(cid) if cid = ! nextCid then () else (f cid; sgnApp' (cid + 1)) in sgnApp' (0)let rec sgnStructAdd(strDec) let let  in in if mid > maxMid then raise (error ("Global signature size " ^ toString (maxMid + 1) ^ " exceeded")) else (update (sgnStructArray,  , mid,  , strDec); nextMid := mid + 1; mid)(* 0 <= mid < !nextMid *)
let rec sgnStructLookup(mid) sub (sgnStructArray,  , mid)(* A hack used in Flit - jcreed 6/05 *)
let rec rename(cid,  , new) let let  in in update (sgnArray,  , cid,  , newConDec)let rec constDef(d) (match sgnLookup (d) with conDef (_,  , _,  , _,  , u,  , _,  , _,  , _) -> u abbrevDef (_,  , _,  , _,  , u,  , _,  , _) -> u)let rec constType(c) conDecType (sgnLookup c)let rec constImp(c) conDecImp (sgnLookup c)let rec constUni(c) conDecUni (sgnLookup c)let rec constBlock(c) conDecBlock (sgnLookup c)let rec constStatus(c) (match sgnLookup (c) with conDec (_,  , _,  , _,  , status,  , _,  , _) -> status _ -> normal)(* Explicit Substitutions *)
(* id = ^0

     Invariant:
     G |- id : G        id is patsub
  *)
let  in(* shift = ^1

     Invariant:
     G, V |- ^ : G       ^ is patsub
  *)
let  in(* invShift = ^-1 = _.^0
     Invariant:
     G |- ^-1 : G, V     ^-1 is patsub
  *)
let  in(* comp (s1, s2) = s'

     Invariant:
     If   G'  |- s1 : G
     and  G'' |- s2 : G'
     then s'  = s1 o s2
     and  G'' |- s1 o s2 : G

     If  s1, s2 patsub
     then s' patsub
   *)
let rec comp(shift (0),  , s) s comp(s,  , shift (0)) s comp(shift (n),  , dot (ft,  , s)) comp (shift (n - 1),  , s) comp(shift (n),  , shift (m)) shift (n + m) comp(dot (ft,  , s),  , s') dot (frontSub (ft,  , s'),  , comp (s,  , s'))(* bvarSub (n, s) = Ft'

      Invariant:
     If    G |- s : G'    G' |- n : V
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
       or  Ft' = ^(n+k)     if  s = Ft1 .. Ftm ^k   and m<n
     and   G |- Ft' : V [s]
  *)
 bvarSub(1,  , dot (ft,  , s)) ft bvarSub(n,  , dot (ft,  , s)) bvarSub (n - 1,  , s) bvarSub(n,  , shift (k)) idx (n + k)(* blockSub (B, s) = B'

     Invariant:
     If   G |- s : G'
     and  G' |- B block
     then G |- B' block
     and  B [s] == B'
  *)
(* in front of substitutions, first case is irrelevant *)
(* Sun Dec  2 11:56:41 2001 -fp *)
 blockSub(bidx k,  , s) (match bvarSub (k,  , s) with idx k' -> bidx k' block b -> b) blockSub(lVar (ref (sOME b),  , sk,  , _),  , s) blockSub (b,  , comp (sk,  , s)) blockSub(lVar (r as ref nONE,  , sk,  , (l,  , t)),  , s) lVar (r,  , comp (sk,  , s),  , (l,  , t)) blockSub(l as inst uLs,  , s') inst (map (fun u -> eClo (u,  , s')) uLs)(* this should be right but somebody should verify *)
(* frontSub (Ft, s) = Ft'

     Invariant:
     If   G |- s : G'     G' |- Ft : V
     then Ft' = Ft [s]
     and  G |- Ft' : V [s]

     NOTE: EClo (U, s) might be undefined, so if this is ever
     computed eagerly, we must introduce an "Undefined" exception,
     raise it in whnf and handle it here so Exp (EClo (U, s)) => Undef
  *)
 frontSub(idx (n),  , s) bvarSub (n,  , s) frontSub(exp (u),  , s) exp (eClo (u,  , s)) frontSub(undef,  , s) undef frontSub(block (b),  , s) block (blockSub (b,  , s))(* decSub (x:V, s) = D'

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
let rec decSub(dec (x,  , v),  , s) dec (x,  , eClo (v,  , s)) decSub(nDec x,  , s) nDec x decSub(bDec (n,  , (l,  , t)),  , s) bDec (n,  , (l,  , comp (t,  , s)))(* dot1 (s) = s'

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
let rec dot1(s as shift (0)) s dot1s dot (idx (1),  , comp (s,  , shift))(* invDot1 (s) = s'
     invDot1 (1. s' o ^) = s'

     Invariant:
     s = 1 . s' o ^
     If G' |- s' : G
     (so G',V[s] |- s : G,V)
  *)
let rec invDot1(s) comp (comp (shift,  , s),  , invShift)(* Declaration Contexts *)
(* ctxDec (G, k) = x:V
     Invariant:
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)
let rec ctxDec(g,  , k) let (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
let rec ctxDec'(decl (g',  , dec (x,  , v')),  , 1) dec (x,  , eClo (v',  , shift (k))) ctxDec'(decl (g',  , bDec (n,  , (l,  , s))),  , 1) bDec (n,  , (l,  , comp (s,  , shift (k)))) ctxDec'(decl (g',  , _),  , k') ctxDec' (g',  , k' - 1)(* ctxDec' (Null, k')  should not occur by invariant *)
 in ctxDec' (g,  , k)(* blockDec (G, v, i) = V

     Invariant:
     If   G (v) = l[s]
     and  Sigma (l) = SOME Gsome BLOCK Lblock
     and  G |- s : Gsome
     then G |- pi (v, i) : V
  *)
let rec blockDec(g,  , v as (bidx k),  , i) let let  in(* G |- s : Gsome *)
let  inlet rec blockDec'(t,  , d :: l,  , 1,  , j) decSub (d,  , t) blockDec'(t,  , _ :: l,  , n,  , j) blockDec' (dot (exp (root (proj (v,  , j),  , nil)),  , t),  , l,  , n - 1,  , j + 1) in blockDec' (s,  , lblock,  , i,  , 1)(* EVar related functions *)
(* newEVar (G, V) = newEVarCnstr (G, V, nil) *)
let rec newEVar(g,  , v) eVar (ref nONE,  , g,  , v,  , ref nil)(* newAVar G = new AVar (assignable variable) *)
(* AVars carry no type, ctx, or cnstr *)
let rec newAVar() aVar (ref nONE)(* newTypeVar (G) = X, X new
     where G |- X : type
  *)
let rec newTypeVar(g) eVar (ref nONE,  , g,  , uni (type),  , ref nil)(* newLVar (l, s) = (l[s]) *)
let rec newLVar(sk,  , (cid,  , t)) lVar (ref nONE,  , sk,  , (cid,  , t))(* Definition related functions *)
(* headOpt (U) = SOME(H) or NONE, U should be strict, normal *)
let rec headOpt(root (h,  , _)) sOME (h) headOpt(lam (_,  , u)) headOpt u headOpt_ nONElet rec ancestor'(nONE) anc (nONE,  , 0,  , nONE) ancestor'(sOME (const (c))) anc (sOME (c),  , 1,  , sOME (c)) ancestor'(sOME (def (d))) (match sgnLookup (d) with conDef (_,  , _,  , _,  , _,  , _,  , _,  , anc (_,  , height,  , cOpt)) -> anc (sOME (d),  , height + 1,  , cOpt)) ancestor'(sOME _) anc (nONE,  , 0,  , nONE)(* ancestor(U) = ancestor info for d = U *)
let rec ancestor(u) ancestor' (headOpt u)(* defAncestor(d) = ancestor of d, d must be defined *)
let rec defAncestor(d) (match sgnLookup (d) with conDef (_,  , _,  , _,  , _,  , _,  , _,  , anc) -> anc)(* Type related functions *)
(* targetHeadOpt (V) = SOME(H) or NONE
     where H is the head of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does not expand type definitions.
  *)
(* should there possibly be a FgnConst case? also targetFamOpt -kw *)
let rec targetHeadOpt(root (h,  , _)) sOME (h) targetHeadOpt(pi (_,  , v)) targetHeadOpt v targetHeadOpt(redex (v,  , s)) targetHeadOpt v targetHeadOpt(lam (_,  , v)) targetHeadOpt v targetHeadOpt(eVar (ref (sOME (v)),  , _,  , _,  , _)) targetHeadOpt v targetHeadOpt(eClo (v,  , s)) targetHeadOpt v targetHeadOpt_ nONE(* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
(* Root(Skonst _, _) can't occur *)
(* targetHead (A) = a
     as in targetHeadOpt, except V must be a valid type
  *)
let rec targetHead(a) valOf (targetHeadOpt a)(* targetFamOpt (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does expand type definitions.
  *)
let rec targetFamOpt(root (const (cid),  , _)) sOME (cid) targetFamOpt(pi (_,  , v)) targetFamOpt v targetFamOpt(root (def (cid),  , _)) targetFamOpt (constDef cid) targetFamOpt(redex (v,  , s)) targetFamOpt v targetFamOpt(lam (_,  , v)) targetFamOpt v targetFamOpt(eVar (ref (sOME (v)),  , _,  , _,  , _)) targetFamOpt v targetFamOpt(eClo (v,  , s)) targetFamOpt v targetFamOpt_ nONE(* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
(* Root(Skonst _, _) can't occur *)
(* targetFam (A) = a
     as in targetFamOpt, except V must be a valid type
  *)
let rec targetFam(a) valOf (targetFamOpt a)end   module