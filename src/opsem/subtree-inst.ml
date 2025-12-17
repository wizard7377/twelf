MemoTableInst  Conv CONV    Whnf WHNF    Match MATCH    Assign ASSIGN    AbstractTabled ABSTRACTTABLED    Print PRINT     MEMOTABLE  struct (*! structure IntSyn = IntSyn' !*)
(*! structure CompSyn = CompSyn' !*)
module (*! structure TableParam = TableParam !*)
(* ---------------------------------------------------------------------- *)
(* Linear substitution tree for linear terms *)
(* normalSubsts: key = int = nvar  (key, (depth, U))

   example:  \x. f( i1, a)   then i1 = (1, X) = X[x/x]

   *)
(* property: linear *)
type NormalSubststype ExSubstslet  inlet  inlet  inlet rec isIds isEmpty s(* ---------------------------------------------------------------------- *)
(* Context for existential variable *)
type Ctx(* functions for handling context for existential variables *)
let rec emptyCtx() Ctx ref []let rec copyl Ctx ref (! l)(* destructively updates L *)
let rec delete(x,  , l : Ctx) let let rec del(x,  , [],  , l) nONE del(x,  , ((h as (y,  , e)) :: l),  , l') if x = y then sOME ((y,  , e),  , (rev l') @ l) else del (x,  , l,  , h :: l') in match del (x,  , (! l),  , []) with nONE -> nONE sOME ((y,  , e),  , l') -> (l := l'; sOME ((y,  , e)))let rec member(x,  , l : Ctx) let let rec memb(x,  , []) nONE memb(x,  , (h as (y,  , e as dec (n,  , u)) :: l)) if x = y then sOME (y,  , e) else memb (x,  , l) memb(x,  , (h as (y,  , e as aDec (n,  , d)) :: l)) (if x = y then sOME ((y,  , e)) else memb (x,  , l)) in memb (x,  , (! l))let rec insertList(e,  , l) (l := (e :: (! l)))(* ---------------------------------------------------------------------- *)
(* Substitution Tree *)
(* It is only possible to distribute the evar-ctx because
     all evars occur exactly once, i.e. they are linear.
     This allows us to maintain invariant, that every occurrence of an evar is
     defined in its evar-ctx
  *)
type Treelet rec makeTree() ref (node ((emptyCtx (),  , nid ()),  , []))let rec noChildrenc (c = [])type Retrievaltype CompSub(* Index array

   All type families have their own substitution tree and all substitution trees
   are stored in an array [a1,...,an]   where ai is a substitution tree for type family ai
   *)
let  inexception module module module module module exception exception exception exception let rec emptyAnswer() emptyAnsw ()let  inlet  intype Nvar(* index for normal variables *)
type Bvar(* index for bound variables *)
type Bdepth(* depth of locally bound variables *)
(* ------------------------------------------------------ *)
(* for debugging only *)
let rec expToS(g,  , u) (try  with )let rec printSub(g,  , shift n) print ("I.Shift " ^ toString n ^ "\n") printSub(g,  , dot (idx n,  , s)) (print ("Idx " ^ toString n ^ " . "); printSub (g,  , s)) printSub(g,  , dot (exp (x as eVar (ref (sOME (u)),  , _,  , _,  , _)),  , s)) (print ("Exp ( EVar " ^ expToS (g,  , x) ^ ")."); printSub (g,  , s)) printSub(g,  , dot (exp (x as eVar (_,  , _,  , _,  , _)),  , s)) (print ("Exp ( EVar  " ^ expToS (g,  , x) ^ ")."); printSub (g,  , s)) printSub(g,  , dot (exp (aVar (_)),  , s)) (print ("Exp (AVar _ ). "); printSub (g,  , s)) printSub(g,  , dot (exp (eClo (aVar (ref (sOME (u))),  , s')),  , s)) (print ("Exp (AVar " ^ expToS (g,  , eClo (u,  , s')) ^ ")."); printSub (g,  , s)) printSub(g,  , dot (exp (x as eClo (eVar (ref (sOME (u)),  , _,  , _,  , _),  , s')),  , s)) (print ("Exp (EVarClo " ^ expToS (g,  , eClo (u,  , s')) ^ ") "); printSub (g,  , s)) printSub(g,  , dot (exp (x as eClo (u,  , s')),  , s)) (print ("Exp (EClo " ^ expToS (g,  , normalize (u,  , s')) ^ ") "); printSub (g,  , s)) printSub(g,  , dot (exp (e),  , s)) (print ("Exp ( " ^ expToS (g,  , e) ^ " ). "); printSub (g,  , s)) printSub(g,  , dot (undef,  , s)) (print ("Undef . "); printSub (g,  , s))(* auxiliary function  -- needed to dereference AVars -- expensive?*)
let rec normalizeSub(shift n) shift n normalizeSub(dot (exp (eClo (aVar (ref (sOME (u))),  , s')),  , s)) dot (exp (normalize (u,  , s')),  , normalizeSub s) normalizeSub(dot (exp (eClo (eVar (ref (sOME (u)),  , _,  , _,  , _),  , s')),  , s)) dot (exp (normalize (u,  , s')),  , normalizeSub s) normalizeSub(dot (exp (u),  , s)) dot (exp (normalize (u,  , id)),  , normalizeSub s) normalizeSub(dot (idx n,  , s)) dot (idx n,  , normalizeSub s)(* ------------------------------------------------------ *)
(* Auxiliary functions *)
(* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *)
let rec etaSpine(nil,  , n) (n = 0) etaSpine(app (root (bVar k,  , nil),  , s),  , n) (k = n && etaSpine (s,  , n - 1)) etaSpine(app (a,  , s),  , n) falselet rec cidFromHead(const c) c cidFromHead(def c) clet rec dotn(0,  , s) s dotn(i,  , s) dotn (i - 1,  , dot1 s)let rec raiseType(null,  , v) v raiseType(decl (g,  , d),  , v) raiseType (g,  , lam (d,  , v))(* compose (Decl(G',D1'), G) =   G. .... D3'. D2'.D1'
       where G' = Dn'....D3'.D2'.D1' *)
let rec compose(null,  , g) g compose(decl (g',  , d),  , g) decl (compose (g',  , g),  , d)let rec shift(null,  , s) s shift(decl (g,  , d),  , s) dot1 (shift (g,  , s))(* ---------------------------------------------------------------------- *)
(* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)
let rec ctxToEVarSub(null,  , s) s ctxToEVarSub(decl (g,  , dec (_,  , a)),  , s) let let  in in dot (exp (x),  , ctxToEVarSub (g,  , s))(* ---------------------------------------------------------------------- *)
(* Matching for linear terms based on assignment *)
(* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
let rec lowerEVar'(x,  , g,  , (pi ((d',  , _),  , v'),  , s')) let let  inlet  in in (x',  , lam (d'',  , u)) lowerEVar'(x,  , g,  , vs') let let  in in (x',  , x')(* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
 (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
lowerEVar1(x,  , eVar (r,  , g,  , _,  , _),  , (v as pi _,  , s)) let let  in in eVar (ref (sOME (u)),  , null,  , v,  , ref nil) lowerEVar1(_,  , x,  , _) x(* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
 lowerEVar(e,  , x as eVar (r,  , g,  , v,  , ref nil)) lowerEVar1 (e,  , x,  , whnf (v,  , id)) lowerEVar(e,  , eVar _) raise (error "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified")let rec ctxToAVarSub(g',  , null,  , s) s ctxToAVarSub(g',  , decl (d,  , dec (_,  , a)),  , s) let let  in in dot (exp (e),  , ctxToAVarSub (g',  , d,  , s)) ctxToAVarSub(g',  , decl (d,  , aDec (_,  , d)),  , s) let let  in in dot (exp (eClo (x,  , shift (~ d))),  , ctxToAVarSub (g',  , d,  , s))(* assign(d, Dec(n, V), X as I.Root(BVar k, S), U, asub) = ()
      Invariant:
      if D ; G |- U : V
         D ; G |- X : V
      then
         add (X, U) to asub
         where  assub is a set of substitutions for existential variables)
    *)
(* [asub]E1  = U *)
let rec assign((* total as (t, passed)*)
, d,  , dec1 as dec (n,  , v),  , e1 as root (bVar k,  , s1),  , u,  , asub) let let  inlet  inlet  in in insert asub (k - d,  , exp (x)) assign((* total as (t, passed)*)
, d,  , dec1 as aDec (n,  , d'),  , e1 as root (bVar k,  , s1),  , u,  , asub) let let  inlet  inlet  in in insert asub (k - d,  , exp (eClo (a,  , shift (~ d'))))(* terms are in normal form *)
(* exception Assignment of string *)
(* assignExp (fasub, (l, ctxTotal as (r, passed), d) (D1, U1), (D2, U2))) = fasub'

     invariant:
      G, G0 |- U1 : V1   U1 in nf
      G, G0 |- U2 : V2   U2 in nf
     and U1, U2 are linear higher-order patterns
      D1 contains all existential variables of U1
      D2 contains all existential variables of U2

      ctxTotal = (r + passed) = |G|
            where G refers to the globally bound variables
      d = |G0| where G' refers to the locally bound variables

      then fasub' is a success continuation
        which builds up a substitution s
              with domain D1 and  U1[s] = U2

      NOTE: We only allow assignment for fully applied evars --
      and we will fail otherwise. This essentially only allows first-order assignment.
      To generalize this, we would need to linearize the ctx and have more complex
      abstraction algorithm.

   *)
let rec assignExp(fasub,  , (ctxTotal as (r,  , passed),  , d),  , (d1,  , u1 as root (h1,  , s1)),  , (d2,  , u2 as root (h2,  , s2))) (match (h1,  , h2) with (const (c1),  , const (c2)) -> if (c1 = c2) then assignSpine (fasub,  , (ctxTotal,  , d),  , (d1,  , s1),  , (d2,  , s2)) else raise (assignment "Constant clash") (def (c1),  , def (c2)) -> (* we do not expand definitions here -- this is very conservative! *)
if (c1 = c2) then assignSpine (fasub,  , (ctxTotal,  , d),  , (d1,  , s1),  , (d2,  , s2)) else let let  inlet  in in assignExp (fasub,  , (ctxTotal,  , d),  , (d1,  , u1'),  , (d2,  , u2')) (def (c1),  , _) -> (* we do not expand definitions here -- this is very conservative! *)
let let  in in assignExp (fasub,  , (ctxTotal,  , d),  , (d1,  , u1'),  , (d2,  , u2)) (_,  , def (c2)) -> (* we do not expand definitions here -- this is very conservative! *)
let let  in in assignExp (fasub,  , (ctxTotal,  , d),  , (d1,  , u1),  , (d2,  , u2')) (bVar (k1),  , bVar k2) -> (if k1 <= (r + d)(* if (k1 - d) >= l *)
 then (* k1 is a globally bound variable *)
if k2 <= (r + d) then (* k2 is globally bound *)
(if k2 = k1 then fasub else raise (assignment "BVar clash")) else raise (assignment "BVar - EVar clash") else (* k1 is an existial variable *)
(match member (k1 - d + passed,  , d1) with nONE -> raise (assignment "EVar nonexistent") sOME (x,  , dec) -> if k2 <= (r + d) then (* k2 is globally bound *)
raise (assignment "EVar - BVar clash") else (if k2 = k1 then (* denote the same evar *)
(fun asub -> (fasub asub; assign ((* ctxTotal,*)
, d,  , dec,  , u1,  , u2,  , asub))) else raise (assignment "EVars are different -- outside of the allowed fragment")))) (skonst (c1),  , skonst (c2)) -> if (c1 = c2) then assignSpine (fasub,  , (ctxTotal,  , d),  , (d1,  , s1),  , (d2,  , s2)) else raise (assignment "Skolem constant clash")(* can this happen ? -- definitions should be already expanded ?*)
 _ -> (raise (assignment ("Head mismatch ")))) assignExp(fasub,  , (ctxTotal,  , d),  , (d1,  , lam (dec1,  , u1)),  , (d2,  , lam (dec2,  , u2))) assignExp (fasub,  , (ctxTotal,  , d + 1),  , (d1,  , u1),  , (d2,  , u2)) assignExp(fasub,  , (ctxTotal,  , d),  , (d1,  , pi ((dec1 as dec (_,  , v1),  , _),  , u1)),  , (d2,  , pi ((dec2 as dec (_,  , v2),  , _),  , u2))) let (* is this necessary? Tue Aug  3 11:56:17 2004 -bp *)
let  in in assignExp (fasub',  , (ctxTotal,  , d + 1),  , (d1,  , u1),  , (d2,  , u2)) assignExp(fasub,  , (ctxTotal,  , d),  , (d1,  , eClo (u,  , s' as shift (0))),  , (d2,  , u2)) assignExp (fasub,  , (ctxTotal,  , d),  , (d1,  , u),  , (d2,  , u2)) assignExp(fasub,  , (ctxTotal,  , d),  , (d1,  , u1),  , (d2,  , eClo (u,  , s as shift (0)))) assignExp (fasub,  , (ctxTotal,  , d),  , (d1,  , u1),  , (d2,  , u)) assignSpine(fasub,  , (ctxTotal,  , d),  , (d1,  , nil),  , (d2,  , nil)) fasub assignSpine(fasub,  , (ctxTotal,  , d),  , (d1,  , app (u1,  , s1)),  , (d2,  , app (u2,  , s2))) let let  in in assignSpine (fasub',  , (ctxTotal,  , d),  , (d1,  , s1),  , (d2,  , s2))(* assignCtx (fasub, ctxTotal as (r, passed), (D1, G), (D2, G')) = fasub'
      invariant
         |G| = |G'| = r
         |G0| = |G0'| = passed
         |G, G0| = |G', G0'| = (r + passed) = ctxTotal

         D1 contains all existential variables occuring in (G, G0)
         D2 contains all existential variables occuring in (G', G0')

         fasub' is a success continuation
            which builds up a substitution s
              with domain D1 and  (G, G0)[s] = (G, G0)

         NOTE : [fasub]G = G' Sun Nov 28 18:55:21 2004 -bp
    *)
let rec assignCtx(fasub,  , ctxTotal,  , (d1,  , null),  , (d2,  , null)) fasub assignCtx(fasub,  , (ctxTotal as (r,  , passed)),  , (d1,  , decl (g1,  , dec (_,  , v1))),  , (d2,  , decl (g2,  , dec (_,  , v2)))) let let  in in assignCtx (fasub',  , ((r - 1,  , passed + 1)),  , (d1,  , g1),  , (d2,  , g2))(* ------------------------------------------------------ *)
(*  Variable b    : bound variable
    Variable n    : index variable
    linear term  U ::=  Root(c, S) | Lam (D, U) | Root(b, S)
    linear Spine S ::= p ; S | NIL
    indexed term t ::= Root(n, NIL) |  Root(c, S) | Lam (D, p) | Root(b, S)
    indexed spines S_i ::= t ; S_i | NIL
    Types   A
    Context G : context for bound variables (bvars)
    (type information is stored in the context)

       G ::= . | G, x : A
       Set of all index variables:  N

    linear terms are well-typed in G:     G |- p
    indexed terms are well-typed in (N ; G) |- t

    Let s is a substitution for index variables (nvar)
    and s1 o s2 o .... o sn = s, s.t.
    forall nvar in CODOM(sk).
     exists i . nvar in DOM(si) and i > k.

    IMAGE (s) = the index variables occurring in the CODOM(s)

    Let N1 ... Nn be the path from the root N1 to the leaf Nn,
    and si the substitution associated with node Ni.

    IMAGE(sn) = empty
    s1 o s2 o ... o sn = s and IMAGE(s) = empty
    i.e. index variables are only internally used and no
         index variable is left.

    A linear term U (and an indexed term t) can be decomposed into a term t' together with
    a sequenence of substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:

    If    N  ; G |- t
    then  N' ; G |- t'
          N  ; G |- s : N' ; G
          N  ; G |- t'[s]     and t'[s] = t

   if we have a linear term then N will be empty, but the same holds.

   In addition:
   all expressions in the index are closed and linear and in normalform i.e.
   an expression is first linearized before it is inserted into the index

   *)
(* ---------------------------------------------------------------*)
(* nctr = |D| =  #index variables *)
let  inlet rec newNVar() (nctr := ! nctr + 1; nVar (! nctr))let rec equalDec(dec (_,  , u),  , dec (_,  , u')) conv ((u,  , id),  , (u',  , id)) equalDec(aDec (_,  , d),  , aDec (_,  , d')) (d = d') equalDec(_,  , _) false(* too restrictive if we require order of both eqn must be the same ?
     Sun Sep  8 20:37:48 2002 -bp *)
(* s = s' = I.id *)
let rec equalCtx(null,  , s,  , null,  , s') true equalCtx(decl (g,  , d as dec (_,  , a)),  , s,  , decl (g',  , d' as dec (_,  , a')),  , s') convDec ((d,  , s),  , (d',  , s')) && (equalCtx (g,  , dot1 s,  , g',  , dot1 s')) equalCtx(_,  , s,  , _,  , s') false(* equalEqn (e, e') = (e = e') *)
let rec equalEqn(trivial,  , trivial) true equalEqn(unify (g,  , x,  , n,  , eqn),  , (unify (g',  , x',  , n',  , eqn'))) equalCtx (g,  , id,  , g',  , id) && conv ((x,  , id),  , (x',  , id)) && conv ((n,  , id),  , (n',  , id)) && equalEqn (eqn,  , eqn') equalEqn(_,  , _) false(* equalEqn' (d, (D, e), (D', e'), asub) = (e = e')

       destructively updates asub such that all the evars occurring in D'
       will be instantiated and  D |- asub : D'

       if D |- e and D' |- e'  and d = depth of context G'
          asub partially instantiates variables from D'
       then
         D |- asub : D'

    *)
let rec equalEqn'(d,  , (d,  , trivial),  , (d',  , trivial),  , asub) true equalEqn'(d,  , (d,  , unify (g,  , x as root (bVar k,  , s),  , n, (* AVar *)
,  , eqn)),  , (d',  , unify (g',  , x',  , n', (* AVar *)
,  , eqn')),  , asub) if (equalCtx (g,  , id,  , g',  , id) && conv ((x,  , id),  , (x',  , id)) && conv ((n,  , id),  , (n',  , id))) then (let (* X is the evar in the query, X' is the evar in the index,
             potentially X' is not yet instantiated and X' in D' but X' not in asub *)
let  in in (if (k - d') > 0 then (match member (k - d',  , d') with nONE -> () sOME (x,  , dec) -> (* k refers to an evar *)
(match lookup asub (k - d') with nONE -> ((* it is not instantiated yet *)
delete (x,  , d'); insert asub (k - d',  , idx (k - d'))) sOME (_) -> ()))(* it is instantiated;
                                          since eqn were solvable, eqn' would be solvable too *)
 else (* k refers to a bound variable *)
(print "Impossible -- Found BVar instead of EVar\n"; raise (error "Impossibe -- Found BVar instead of EVar ")))equalEqn' (d,  , (d,  , eqn),  , (d',  , eqn'),  , asub)) else false equalEqn'(d,  , _,  , _,  , asub) false(* equalSub (s, s') = (s=s') *)
let rec equalSub(shift k,  , shift k') (k = k') equalSub(dot (f,  , s),  , dot (f',  , s')) equalFront (f,  , f') && equalSub (s,  , s') equalSub(dot (f,  , s),  , shift k) false equalSub(shift k,  , dot (f,  , s)) false(* equalFront (F, F') = (F=F') *)
 equalFront(idx n,  , idx n') (n = n') equalFront(exp u,  , exp v) conv ((u,  , id),  , (v,  , id)) equalFront(undef,  , undef) true(* equalCtx' (G, G') = (G=G') *)
let rec equalCtx'(null,  , null) true equalCtx'(decl (dk,  , dec (_,  , a)),  , decl (d1,  , dec (_,  , a1))) (conv ((a,  , id),  , (a1,  , id)) && equalCtx' (dk,  , d1)) equalCtx'(decl (dk,  , aDec (_,  , d')),  , decl (d1,  , aDec (_,  , d))) ((d = d') && equalCtx' (dk,  , d1)) equalCtx'(_,  , _) false(* ---------------------------------------------------------------*)
(* destructively may update asub ! *)
let rec instanceCtx(asub,  , (d1,  , g1),  , (d2,  , g2)) let let  inlet  in in if d1 = d2 then try  with  else false(* ---------------------------------------------------------------*)
(* collect EVars in sub *)
(* collectEVar (D, sq) = (D_sub, D')
     if D |- sq where D is a set of free variables
     then Dsq |- sq  and (Dsq u D') = D
          Dsq contains all the free variables occuring in sq
          D' contains all the free variables corresponding to Gsq
   *)
let rec collectEVar(d,  , nsub) let let  inlet rec collectExp(d,  , d',  , d,  , lam (_,  , u)) collectExp (d + 1,  , d',  , d,  , u) collectExp(d,  , d',  , d,  , root (const c,  , s)) collectSpine (d,  , d',  , d,  , s) collectExp(d,  , d',  , d,  , root (bVar k,  , s)) (match (member (k - d,  , d)) with nONE -> collectSpine (d,  , d',  , d,  , s) sOME (x,  , dec) -> (delete (x - d,  , d); insertList ((x - d,  , dec),  , d'))) collectExp(d,  , d',  , d,  , u as root (def k,  , s)) let let  in in collectExp (d,  , d',  , d,  , u') collectSpine(d,  , d',  , d,  , nil) () collectSpine(d,  , d',  , d,  , app (u,  , s)) (collectExp (d,  , d',  , d,  , u); collectSpine (d,  , d',  , d,  , s)) in forall nsub (fun (nv,  , (du,  , u)) -> collectExp (0,  , d',  , d,  , u))(d',  , d)(* ---------------------------------------------------------------*)
(* most specific linear common generalization *)
(* compatible (T, U) = (T', rho_u, rho_t) opt
    if T is an indexed term
       U is a linear term
       U and T share at least the top function symbol
   then
       T'[rho_u] = U and T'[rho_t] = T
   *)
let rec convAssSub'(g,  , idx_k,  , d,  , asub,  , d,  , evarsl as (evars,  , avars)) (match (lookup asub d) with nONE -> (match member (d,  , d) with nONE -> shift (evars + avars(* 0 *)
) sOME (x,  , dec (n,  , v)) -> (* Found an EVar which is not yet
                     instantiated -- must be instantiated when
                     solving residual equations! *)
let let  inlet  in in dot (exp (eClo (e,  , shift (evars + avars))),  , s) sOME (x,  , aDec (n,  , v)) -> (* should never happen -- all avars should
                     have been assigned! *)
(print ("convAssSub' -- Found an uninstantiated AVAR\n"); raise (error "Unassigned AVar -- should never happen\n"))) sOME (f as exp (e)) -> let let  in in dot (exp (e'),  , convAssSub' (g,  , idx_k + 1,  , d,  , asub,  , d + 1,  , evarsl)))let rec convAssSub(g,  , asub,  , glength,  , d',  , evarsl) convAssSub' (g,  , 0,  , d',  , asub,  , glength,  , evarsl)let rec isExists(d,  , bVar k,  , d) member (k - d,  , d)(* [s']T = U so U = query and T is in the index *)
let rec instance((d_t,  , (dt,  , t)),  , (d_u,  , (du,  , u)),  , rho_u,  , ac) let let rec instRoot(depth,  , t as root (h1 as const k,  , s1),  , u as root (const k',  , s2),  , ac) if (k = k') then instSpine (depth,  , s1,  , s2,  , ac) else raise (instance "Constant mismatch\n") instRoot(depth,  , t as root (h1 as def k,  , s1),  , u as root (def k',  , s2),  , ac) if (k = k') then instSpine (depth,  , s1,  , s2,  , ac) else let let  inlet  in in instExp (depth,  , t',  , u',  , ac) instRoot(depth,  , t as root (h1 as def k,  , s1),  , u as root (h2,  , s2),  , ac) let let  in in instExp (depth,  , t',  , u,  , ac) instRoot(d,  , t as root (h1 as bVar k,  , s1),  , u as root (bVar k',  , s2),  , ac) if (k > d) && (k' > d) then (* globally bound variable *)
let let  inlet  in in match (member (k1,  , d_t),  , member (k2,  , d_u)) with (nONE,  , nONE) -> ((* both refer to the same globally bound variable in G *)
if (k1 = k2) then instSpine (d,  , s1,  , s2,  , ac) else raise (instance "Bound variable mismatch\n")) (sOME (x,  , dec1),  , sOME (x',  , dec2)) -> (* k, k' refer to the existential *)
(if ((k1 = k2) && equalDec (dec1,  , dec2)) then (* they refer to the same existential variable *)
let (* this is unecessary *)
(* since existential variables have the same type
                             and need to be fully applied in order, S1 = S2 *)
let  inlet  in in ac'' else (* instance checking only Sun Oct 27 12:16:10 2002 -bp *)
(fun asub -> (ac asub; assign ((* ctxTotal,*)
, d,  , dec1,  , t,  , u,  , asub))))(* instance checking only Sun Oct 27 12:18:53 2002 -bp *)
 (sOME (x,  , dec1 as aDec (n,  , d')),  , nONE) -> (fun asub -> (ac asub; assign ((* ctxTotal,*)
, d,  , dec1,  , t,  , u,  , asub))) (sOME (x,  , dec1),  , nONE) -> (fun asub -> (ac asub; assign ((* ctxTotal,*)
, d,  , dec1,  , t,  , u,  , asub))) (_,  , _) -> raise (instance "Impossible\n") else (* locally bound variables *)
raise (instance "Bound variable mismatch\n") instRoot(d,  , t as root (h1 as bVar k,  , s1),  , u as root (const k',  , s2),  , ac) (match isExists (d,  , bVar k,  , d_t) with nONE -> raise (instance "Impossible\n") sOME (x,  , dec1 as aDec (_,  , _)) -> (fun asub -> (ac asub; assign ((* ctxTotal,*)
, d,  , dec1,  , t,  , u,  , asub))) sOME (x,  , dec1) -> (fun asub -> (ac asub; assign ((* ctxTotal, *)
, d,  , dec1,  , t,  , u,  , asub)))) instRoot(d,  , t as root (h1 as bVar k,  , s1),  , u as root (def k',  , s2),  , ac) (match isExists (d,  , bVar k,  , d_t) with nONE -> raise (instance "Impossible\n") sOME (x,  , dec1 as aDec (_,  , _)) -> (fun asub -> (ac asub; assign ((* ctxTotal,*)
, d,  , dec1,  , t,  , u,  , asub))) sOME (x,  , dec1) -> (fun asub -> (ac asub; assign ((* ctxTotal, *)
, d,  , dec1,  , t,  , u,  , asub)))) instRoot(depth,  , t as root (h1,  , s1),  , u as root (def k',  , s2),  , ac) let let  in in instExp (depth,  , t,  , u',  , ac) instRoot(d,  , t as root (h1,  , s1),  , u as root (h2,  , s2),  , ac) raise (instance "Other Cases impossible\n") instExp(d,  , t as nVar n,  , u as root (h,  , s),  , ac) (insert rho_u (n,  , (d,  , u)); ac) instExp(d,  , t as root (h1,  , s1),  , u as root (h2,  , s2),  , ac) instRoot (d,  , root (h1,  , s1),  , root (h2,  , s2),  , ac) instExp(d,  , lam (d1 as dec (_,  , a1),  , t1),  , lam (d2 as dec (_,  , a2),  , u2),  , ac) instExp (d + 1,  , t1,  , u2,  , ac) instExp(d,  , t,  , u,  , ac) (print "instExp -- falls through?\n"; raise (instance "Impossible\n")) instSpine(d,  , nil,  , nil,  , ac) ac instSpine(d,  , app (t,  , s1),  , app (u,  , s2),  , ac) let let  inlet  in in ac'' instSpine(d,  , nil,  , app (_,  , _),  , ac) (print ("Spines are not the same -- (first one is Nil) -- cannot happen!\n"); raise (instance "DifferentSpines\n")) instSpine(d,  , app (_,  , _),  , nil,  , ac) (print ("Spines are not the same -- second one is Nil -- cannot happen!\n"); raise (instance "DifferentSpines\n")) instSpine(d,  , sClo (_,  , _),  , _,  , ac) (print ("Spine Closure!(1) -- cannot happen!\n"); raise (instance "DifferentSpines\n")) instSpine(d,  , _,  , sClo (_,  , _),  , ac) (print ("Spine Closure! (2) -- cannot happen!\n"); raise (instance " DifferentSpines\n")) in (* by invariant dt = du *)
ac := instExp (dt,  , t,  , u,  , ! ac)(* if it succeeds then it will return a continuation which will
         instantiate the "evars" and rho_t will contain all
         nvar instantiations
         otherwise it will raise Instance *)
let rec compHeads((d_1,  , const k),  , (d_2,  , const k')) (k = k') compHeads((d_1,  , def k),  , (d_2,  , def k')) (k = k') compHeads((d_1,  , bVar k),  , (d_2,  , bVar k')) (match isExists (0,  , bVar k,  , d_1) with nONE -> (k = k') sOME (x,  , dec) -> true) compHeads((d_1,  , bVar k),  , (d_2,  , h2)) (match isExists (0,  , bVar k,  , d_1) with nONE -> false sOME (x,  , dec) -> true) compHeads((d_1,  , h1),  , (d_2,  , h2)) falselet rec compatible'((d_t,  , (dt,  , t)),  , (d_u,  , (du,  , u)),  , ds,  , rho_t,  , rho_u) let let rec genNVar((rho_t,  , t),  , (rho_u,  , u)) (insert rho_t (! nctr + 1,  , t); insert rho_u (! nctr + 1,  , u); (* by invariant dt = du *)
newNVar ())let rec genRoot(d,  , t as root (h1 as const k,  , s1),  , u as root (const k',  , s2)) if (k = k') then let let  in in root (h1,  , s') else genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u))) genRoot(d,  , t as root (h1 as def k,  , s1),  , u as root (def k',  , s2)) if (k = k') then let let  in in root (h1,  , s') else (* could expand definitions here ? -bp*)
genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u))) genRoot(d,  , t as root (h1 as bVar k,  , s1),  , u as root (bVar k',  , s2)) if (k > d) && (k' > d) then (* globally bound variable *)
let let  inlet  in in match (member (k1,  , d_t),  , member (k2,  , d_u)) with (nONE,  , nONE) -> (* should never happen *)
(if (k1 = k2) then try  with  else genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u)))) (sOME (x,  , dec1),  , sOME (x',  , dec2)) -> (* k, k' refer to the existential *)
if ((k1 = k2) && equalDec (dec1,  , dec2)) then (* they refer to the same existential variable *)
let (* this is unecessary -- since existential variables have the same type
                            and need to be fully applied in order, S1 = S2 *)
let  in in (delete (x,  , d_t); delete (x',  , d_u); insertList ((x,  , dec1),  , ds); root (h1,  , s')) else (* variant checking only *)
genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u))) (_,  , _) -> genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u))) else (* locally bound variables *)
if (k = k') then try  with  else genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u))) genRoot(d,  , t as root (h1 as bVar k,  , s1),  , u as root (const k',  , s2)) genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u))) genRoot(d,  , t as root (h1 as bVar k,  , s1),  , u as root (def k',  , s2)) genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u))) genRoot(d,  , t as root (h1,  , s1),  , u as root (h2,  , s2)) genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u))) genExp(d,  , t as nVar n,  , u as root (h,  , s)) (insert rho_u (n,  , (d,  , u)); t) genExp(d,  , t as root (h1,  , s1),  , u as root (h2,  , s2)) genRoot (d,  , root (h1,  , s1),  , root (h2,  , s2)) genExp(d,  , lam (d1 as dec (_,  , a1),  , t1),  , lam (d2 as dec (_,  , a2),  , u2)) let let  in in lam (d1,  , e) genExp(d,  , t,  , u) (print "genExp -- falls through?\n"; genNVar ((rho_t,  , (d,  , t)),  , (rho_u,  , (d,  , u)))) genSpine(d,  , nil,  , nil) nil genSpine(d,  , app (t,  , s1),  , app (u,  , s2)) let let  inlet  in in app (e,  , s') genSpine(d,  , nil,  , app (_,  , _)) raise (differentSpines) genSpine(d,  , app (_,  , _),  , nil) raise (differentSpines) genSpine(d,  , sClo (_,  , _),  , _) raise (differentSpines) genSpine(d,  , _,  , sClo (_,  , _)) raise (differentSpines) in (* by invariant dt = du *)
variant (dt,  , genExp (dt,  , t,  , u))let rec compatible((d_t,  , t as (d1,  , root (h1,  , s1))),  , (d_u,  , u as (d2,  , root (h2,  , s2))),  , ds,  , rho_t,  , rho_u) if compHeads ((d_t,  , h1),  , (d_u,  , h2)) then compatible' ((d_t,  , t),  , (d_u,  , u),  , ds,  , rho_t,  , rho_u) else notCompatible compatible((d_t,  , t),  , (d_u,  , u),  , ds,  , rho_t,  , rho_u) compatible' ((d_t,  , t),  , (d_u,  , u),  , ds,  , rho_t,  , rho_u)(* compatibleCtx (asub, (Dsq, Gsq, eqn_sq), GR) = option

    if Dsq is a subset of Dsq_complete
       where Dsq_complete encompasses all evars and avars in the original query
       Dsq |- Gsq ctx
       Dsq, Gsq |- eqn_sq
       there exists (_, D', G', eqn', ansRef', _, status') in GR
       s.t.
       Gsq is an instance of G'
       (andalso eqn_sq = eqn')
    then
      SOME((D', G', eqn'), answRef', status)
      and asub is destructively updated s.t. Dsq_complete |- Gsq = [asub]G'

    else
      NONE
   *)
let rec compatibleCtx(asub,  , (dsq,  , gsq,  , eqn_sq),  , []) nONE compatibleCtx(asub,  , (dsq,  , gsq,  , eqn_sq),  , ((_,  , delta',  , g',  , eqn',  , answRef',  , _,  , status') :: gRlist)) if instanceCtx (asub,  , (dsq,  , gsq),  , (delta',  , g')) then sOME ((delta',  , g',  , eqn'),  , answRef',  , status') else compatibleCtx (asub,  , (dsq,  , gsq,  , eqn_sq),  , gRlist)(* ---------------------------------------------------------------*)
(* instanceSub(nsub_t, squery) = (rho_u, asub)

   if DOM(nsub_t) <= DOM(nsub_u)
      CODOM(nsub_t) : index terms
      CODOM(nsub_u) : linear terms
        G_u, Glocal_u |- nsub_u
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have "approximately" the same type)
    l_g = |Glocal_u|


    [asub]nsub_t = squery
   *)
let rec instanceSub((d_t,  , nsub_t),  , (dsq,  , squery),  , asub) let let  inlet  inlet  in(* by invariant rho_t = empty, since nsub_t <= squery *)
 in try  with (* [asub]nsub_t = sq  where sq is the query substitution *)
let rec instChild(n as leaf ((d_t,  , nsub_t),  , gList),  , (d_sq,  , sq),  , asub) instanceSub ((d_t,  , nsub_t),  , (d_sq,  , sq),  , asub) instChild(n as node ((d_t,  , nsub_t),  , children'),  , (d_sq,  , sq),  , asub) instanceSub ((d_t,  , nsub_t),  , (d_sq,  , sq),  , asub)let rec findAllInst(g_r,  , children,  , ds,  , asub) let let rec findAllCands(g_r,  , nil,  , (dsq,  , sub_u),  , asub,  , iList) iList findAllCands(g_r,  , (x :: l),  , (dsq,  , sub_u),  , asub,  , iList) let let  in in match instChild (! x,  , (dsq,  , sub_u),  , asub)(* will update asub *)
 with noCompatibleSub -> findAllCands (g_r,  , l,  , (dsq,  , sub_u),  , asub',  , iList) instanceSub (asub,  , drho2) -> findAllCands (g_r,  , l,  , (dsq,  , sub_u),  , asub',  , ((x,  , drho2,  , asub) :: iList)) in findAllCands (g_r,  , children,  , ds,  , asub,  , nil)(* Solving  variable definitions *)
(* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
let rec solveEqn((trivial,  , s),  , g) true solveEqn((unify (g',  , e1,  , n, (* evar *)
,  , eqns),  , s),  , g) let let  inlet  in in unifiable (g'',  , (n,  , s'),  , (e1,  , s')) && solveEqn ((eqns,  , s),  , g)(* Mon Dec 27 11:57:35 2004 -bp *)
(* solveEqn' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
let rec solveEqn'((trivial,  , s),  , g) true solveEqn'((unify (g',  , e1,  , n, (* evar *)
,  , eqns),  , s),  , g) let let  inlet  in in unifiable (g'',  , (n,  , s'),  , (e1,  , s')) && solveEqn' ((eqns,  , s),  , g)(* Mon Dec 27 12:20:45 2004 -bp
 (* solveEqn' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  fun solveEqn' (T.Trivial, s) = true
    | solveEqn' (T.Unify(G',e1, N (* evar *), eqns), s) =
      let
        val s' = shift (G', s)
      in
        Assign.unifiable (G', (N, s'),(e1, s'))
        andalso solveEqn' (eqns, s)
     end

 (* solveEqnI' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  fun solveEqnI' (T.Trivial, s) = true
    | solveEqnI' (T.Unify(G',e1, N (* evar *), eqns), s) =
      let
        val s' = shift (G', s)
        (* note: we check whether N[s'] is an instance of e1[s'] !!! *)
        (* at this point all AVars have been instantiated, and we could use Match.instance directly *)
      in
        Assign.instance (G', (e1, s'), (N, s'))
        andalso solveEqnI' (eqns, s)
     end
 Mon Dec 27 11:58:21 2004 -bp *)
(* solveEqnI' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
let rec solveEqnI'((trivial,  , s),  , g) true solveEqnI'((unify (g',  , e1,  , n, (* evar *)
,  , eqns),  , s),  , g) let let  inlet  in(* note: we check whether N[s'] is an instance of e1[s'] !!! *)
(* at this point all AVars have been instantiated, and we could use Match.instance directly *)
 in instance (g'',  , (e1,  , s'),  , (n,  , s')) && solveEqnI' ((eqns,  , s),  , g)(* retrieve all Instances from substitution tree *)
(* retreiveInst (Nref, (Dq, sq), s', GR) = callCheckResult

      Invariant:

      If there exists a path r1 ... rn = p
         in the substitution tree with root Nref
         and there exists an assignable substitution s' (D
         s.t. [r']
      then
         return RepeatedEntry
      else raises exception instance
    *)
let rec retrieveInst(nref,  , (dq,  , sq),  , asub,  , gR) let let rec retrieve'(n as leaf ((d,  , s),  , gRlistRef),  , (dq,  , sq),  , asubst,  , gR' as (dAEVars as (dEVars,  , dAVars),  , g_r,  , eqn,  , stage,  , status)) let let  in(* Dq = (Dsq' u Dg) where Dsq' = evars occurring in sq
                                      D_G = evars occuring in G_sq or only in eqn_sq

               and Dsq = D since there exists a path s1 ... sn from the root to the leaf (D,s)
                 s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
             *)
 in (match compatibleCtx (asubst,  , (d_G,  , g_r,  , eqn),  , (! gRlistRef))(* compatibleCtx may destructively update asub ! *)
 with nONE -> ((* compatible path -- but different ctx *)
raise (instance "Compatible path -- different ctx\n")) sOME ((d',  , g',  , eqn'),  , answRef',  , status') -> (* compatible path -- SAME ctx *)
((* note: previously we checked eqn' = eqn! -- this is too restrictive
                 now - Dec  6 2004 -bp we check whether eqn is an instance of eqn'
                 note: this is very delicate code.
               *)
let let  in(* Since there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
                   D1', ...., Dn', D, D' = D*
                   and          G' |- esub' : DAEVars, G'        and       .   |- esub : DAEVars
                        DAEVars, G |- asub' : D*, G'                   DAEVars |- asub : D*

                  note: asub' may refer to free variables which denote evars in D*
                        which only occur in eqn' and hence have not yet been instantiated
                        however: all avars in D* have been instantiated!
                 *)
let  inlet  in(* Residual equation of query:
                   DAEVars, G' |- eqn  hence we solve : G' |= [esub']eqn *)
let  in(*              val _ = if solveEqn' (eqn, esub)
                          then () else print " failed to solve eqn_query\n"  *)
let  in(* Residual equations in index:
                   D*, G' |- eqn'    where eqn' = AVar1 = E1 .... AVarn = En
                                      and  Ei may contain free variables
                      G'  |= [esub](asub) (eqn')

                      solve eqn' from path in index using instance or matching ONLY
                      to instantiate the free variables Ei

                   remark: DAEVars, G' |= [asub]eqn'   should work in theory too,
                           if the free variables in asub are created in such a way that they may depend on DAVars.
                           otherwise unification or instance checking will fail or the resulting instantiation
                           for the free variables in asub is too restrictive, s.t. retrieval fails
                   *)
 in if solveEqnI' ((eqn',  , shift (g',  , easub)),  , g')(*              if solveEqnI' (eqn', easub) *)
(* solve residual equations using higher-order matching Wed Dec 22 2004 -bp *)
 then repeatedEntry ((esub,  , asub),  , answRef',  , status') else raise (instance "Compatible path -- resdidual equ. not solvable\n"))) retrieve'(n as node ((d,  , sub),  , children),  , (dq,  , sq),  , asub,  , gR as (dAEVars,  , g_r,  , eqn,  , stage,  , status)) let let  inlet rec checkCandidatesnil raise (instance "No compatible child\n") checkCandidates((childRef,  , drho2,  , asub) :: iCands) try  with  in checkCandidates instCand in (fun () -> (),  , retrieve' (! nref,  , (dq,  , sq),  , asub,  , gR))(*---------------------------------------------------------------------------*)
(* insert new entry into substitution tree *)
(* assuming there is no compatible entry already *)
(* compatibleSub(nsub_t, squery) = (sigma, rho_t, rho_u) opt

   if DOM(nsub_t) <= DOM(squery)
      CODOM(nsub_t) : index terms
      CODOM(squery) : linear terms
        G_u, Glocal_u |- squery
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have "approximately" the same type)

   *)
let rec compatibleSub((d_t,  , nsub_t),  , (dsq,  , squery)) let let  inlet  inlet  inlet  inlet  in(* by invariant rho_t = empty, since nsub_t <= squery *)
let  in in if isId (rho_t) then (* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
((! choose) true; variantSub (d_r2,  , rho_u)) else ((* split -- asub is unchanged *)
(! choose) false; if isId (sigma) then noCompatibleSub else splitSub ((dsigma,  , sigma),  , (d_r1,  , rho_t),  , (d_r2,  , rho_u)))(* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
(* ---------------------------------------------------------------------- *)
(*  fun mkLeaf (Ds, GR, n) = Leaf (Ds, GR)*)
let rec mkNode(node (_,  , children),  , dsigma as (ds,  , sigma),  , drho1 as (d1,  , rho1),  , gR as ((evarl,  , l),  , dp,  , eqn,  , answRef,  , stage,  , status),  , drho2 as (d2,  , rho2)) let let  inlet  inlet  in in node (dsigma,  , [ref (leaf ((d_rho2,  , rho2),  , ref [gR'])); ref (node (drho1,  , children))]) mkNode(leaf (c,  , gRlist),  , dsigma as (ds,  , sigma),  , drho1 as (d1,  , rho1),  , gR2 as ((evarl,  , l),  , dp,  , eqn,  , answRef,  , stage,  , status),  , drho2 as (d2,  , rho2)) let let  inlet  in in node (dsigma,  , [ref (leaf ((d_rho2,  , rho2),  , ref [gR2'])); ref (leaf (drho1,  , gRlist))])(* ---------------------------------------------------------------------- *)
let rec compChild(n as leaf ((d_t,  , nsub_t),  , gList),  , (d_e,  , nsub_e)) compatibleSub ((d_t,  , nsub_t),  , (d_e,  , nsub_e)) compChild(n as node ((d_t,  , nsub_t),  , children'),  , (d_e,  , nsub_e)) compatibleSub ((d_t,  , nsub_t),  , (d_e,  , nsub_e))let rec findAllCandidates(g_r,  , children,  , ds) let let rec findAllCands(g_r,  , nil,  , (dsq,  , sub_u),  , vList,  , sList) (vList,  , sList) findAllCands(g_r,  , (x :: l),  , (dsq,  , sub_u),  , vList,  , sList) match compChild (! x,  , (dsq,  , sub_u)) with noCompatibleSub -> findAllCands (g_r,  , l,  , (dsq,  , sub_u),  , vList,  , sList) splitSub (dsigma,  , drho1,  , drho2) -> findAllCands (g_r,  , l,  , (dsq,  , sub_u),  , vList,  , ((x,  , (dsigma,  , drho1,  , drho2)) :: sList)) variantSub (drho2 as (d_r2,  , rho2)) -> findAllCands (g_r,  , l,  , (dsq,  , sub_u),  , ((x,  , drho2,  , id) :: vList),  , sList) in findAllCands (g_r,  , children,  , ds,  , nil,  , nil)(* ---------------------------------------------------------------------- *)
let rec divergingCtx(stage,  , g,  , gRlistRef) let let  in(* this 3 is arbitrary -- lockstep *)
 in exists (fun ((_,  , l),  , d,  , g',  , _,  , _,  , stage',  , _) -> (stage = stage' && (l > (ctxLength (g'))))) (! gRlistRef)let rec eqHeads(const k,  , const k') (k = k') eqHeads(bVar k,  , bVar k') (k = k') eqHeads(def k,  , def k') (k = k') eqHeads(_,  , _) false(* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1]
  t2 is a linear term which may not contain any nvars!
  t may contain nvars
 *)
let rec eqTerm(root (h2,  , s2),  , (t as root (h,  , s),  , rho1)) if eqHeads (h2,  , h) then eqSpine (s2,  , (s,  , rho1)) else false eqTerm(t2,  , (nVar n,  , rho1)) (match (lookup rho1 n) with nONE -> false sOME ((dt1,  , t1)) -> eqTerm (t2,  , (t1,  , nid ()))) eqTerm(lam (d2,  , t2),  , (lam (d,  , t),  , rho1)) eqTerm (t2,  , (t,  , rho1)) eqTerm(_,  , (_,  , _)) false eqSpine(nil,  , (nil,  , rho1)) true eqSpine(app (t2,  , s2),  , (app (t,  , s),  , rho1)) eqTerm (t2,  , (t,  , rho1)) && eqSpine (s2,  , (s,  , rho1))let rec divergingSub((ds,  , sigma),  , (dr1,  , rho1),  , (dr2,  , rho2)) exists rho2 (fun (n2,  , (dt2,  , t2)) -> exists sigma (fun (_,  , (d,  , t)) -> eqTerm (t2,  , (t,  , rho1))))(* ---------------------------------------------------------------------- *)
(* Insert via variant checking *)
let rec variantCtx((g,  , eqn),  , []) nONE variantCtx((g,  , eqn),  , ((l',  , d_G,  , g',  , eqn',  , answRef',  , _,  , status') :: gRlist)) (if (equalCtx' (g,  , g') && equalEqn (eqn,  , eqn')) then sOME (l',  , answRef',  , status') else variantCtx ((g,  , eqn),  , gRlist))(* insert (Nref, (Dq, sq), GR) = TableResult *)
let rec insert(nref,  , (dsq,  , sq),  , gR) let let rec insert'(n as leaf (_,  , gRlistRef),  , (dsq,  , sq),  , gR as (l,  , g_r,  , eqn,  , answRef,  , stage,  , status)) (match variantCtx ((g_r,  , eqn),  , (! gRlistRef)) with nONE -> ((* compatible path -- but different ctx! *)
let let  in(* D_G contains evars occurring only in eqn or G
                        D_nsub contains evars occurring only in sq
                        furthermore: D_nsub = D where Leaf((D,s), GRlistRef)
                     *)
let  in in (fun () -> (gRlistRef := (gR' :: (! gRlistRef)); answList := (answRef :: (! answList))),  , newEntry (answRef))) sOME (_,  , answRef',  , status') -> ((* compatible path -- SAME ctx and SAME eqn!
                                          this implies: SAME D_G *)
((fun () -> ()),  , repeatedEntry ((id,  , id),  , answRef',  , status')))) insert'(n as node ((d,  , sub),  , children),  , (dsq,  , sq),  , gR as (l,  , g_r,  , eqn,  , answRef,  , stage,  , status)) let let  inlet  inlet  inlet rec checkCandidates(nil,  , nil) (fun () -> (nref := node ((d,  , sub),  , (ref (leaf ((d_nsub,  , sq),  , ref [gR']))) :: children); answList := (answRef :: (! answList))),  , newEntry (answRef)) checkCandidates(nil,  , ((childRef,  , (dsigma,  , drho1,  , drho2)) :: _)) if ((! divHeuristic) && divergingSub (dsigma,  , drho1,  , drho2)) then ((* substree diverging -- splitting node *)
(fun () -> (childRef := mkNode ((! childRef),  , dsigma,  , drho1,  , gR,  , drho2); answList := (answRef :: (! answList))),  , divergingEntry (id,  , answRef))) else ((* split existing node *)
(fun () -> (childRef := mkNode ((! childRef),  , dsigma,  , drho1,  , gR,  , drho2); answList := (answRef :: (! answList))),  , newEntry (answRef))) checkCandidates(((childRef,  , drho2,  , asub) :: nil),  , _) insert (childRef,  , drho2,  , gR) checkCandidates(((childRef,  , drho2,  , asub) :: l),  , sCands) (match (insert (childRef,  , drho2,  , gR)) with (_,  , newEntry (answRef)) -> checkCandidates (l,  , sCands) (f,  , repeatedEntry (asub,  , answRef,  , status)) -> ((f,  , repeatedEntry (asub,  , answRef,  , status))) (f,  , divergingEntry (asub,  , answRef)) -> ((f,  , divergingEntry (asub,  , answRef)))) in checkCandidates (variantCand,  , splitCand) in insert' (! nref,  , (dsq,  , sq),  , gR)(* ---------------------------------------------------------------------- *)
(* answer check and insert

     Invariant:
        D |- Pi G.U
          |- (Pi G.U)[s]
       .  |- s : D
       {{K}} are all the free variables in s
        D_k is the linear context of all free variables in {{K}}
        D_k |- s_k : D  and eqn
        D_k |- (Pi G.U)[s_k] and eqn

      answerCheck (G, s, answRef, 0) = repeated
         if (D_k, s_k, eqn)  already occurs in answRef
      answerCheck (G,s, answRef, O) = new
         if (D_k, s_k, eqn) did not occur in answRef
         Sideeffect: update answer list for U
     *)
let rec answCheckVariant(s',  , answRef,  , o) let let rec member((d,  , sk),  , []) false member((d,  , sk),  , (((d1,  , s1),  , _) :: s)) if equalSub (sk,  , s1) && equalCtx' (d,  , d1) then true else member ((d,  , sk),  , s)let  in in if member ((dEVars,  , sk),  , solutions answRef) then repeated else (addSolution (((dEVars,  , sk),  , o),  , answRef); new)(* ---------------------------------------------------------------------- *)
let rec reset() (nctr := 1; (* Reset Subsitution Tree *)
modify (fun (n,  , tree) -> (n := 0; tree := ! (makeTree ()); answList := []; added := false; (n,  , tree))) indexArray)(* makeCtx (n, G, G') =  unit
     if G LF ctx
     then
      G' is a set
      where (i,Di) corresponds to the i-th declaration in G

    note: G' is destructively updated
    *)
let rec makeCtx(n,  , null,  , dEVars : Ctx) () makeCtx(n,  , decl (g,  , d),  , dEVars : Ctx) (insertList ((n,  , d),  , dEVars); makeCtx (n + 1,  , g,  , dEVars))(* callCheck (a, DAVars, DEVars, G, U, eqn, status) = TableResult
    if
      U is atomic (or base type) i.e. U = a S

      DAVars, DEVars, G |- U
      DAVars, DEVars, G |- eqn

      Tree is the substitution trie associated with type family a

   then
      if there exists a path r1 o r2 o ... o rn = p in Tree
         together with some (G',eqn', answRef') at the leaf
         and DAVars', DEVars', G' |- p
      and there exists a substitution s' s.t.

          DAVars, DEVars |- s' : DAVars', DEVars'
          [s']G' = G and [s']p = U

      and moreover
          there exists a substitution r' s.t.  G |- r' : DAVars, DEVars, G
          (which re-instantiates evars)

      and
            G |= [r']eqn    and [s']G' |= [r'][s']eqn'
     then
       TableResult = RepeatedEntry(s', answRef')

     otherwise

       TableResult = NewEntry (answRef')
       and there exists a path r1 o r2 o ... o rk = U in Tree
           together with (G,eqn, answRef) at the leaf

   *)
let rec callCheck(a,  , dAVars,  , dEVars,  , g,  , u,  , eqn,  , status) let let  inlet  inlet  inlet  inlet  in(* n = |G| *)
let  in(* Dq = DAVars, DEVars *)
let  in(* l = |D| *)
let  inlet  inlet  inlet  in in match result with (sf,  , newEntry (answRef)) -> (sf (); added := true; newEntry (answRef)) (_,  , repeatedEntry (asub,  , answRef,  , status)) -> repeatedEntry (asub,  , answRef,  , status) (sf,  , divergingEntry (asub,  , answRef)) -> (sf (); added := true; divergingEntry (asub,  , answRef))(* we assume we alsways insert new things into the tree *)
let rec insertIntoTree(a,  , dAVars,  , dEVars,  , g,  , u,  , eqn,  , answRef,  , status) let let  inlet  in(* sq = query substitution *)
let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in match result with (sf,  , newEntry (answRef)) -> (sf (); added := true; newEntry (answRef)) (_,  , repeatedEntry (asub,  , answRef,  , status)) -> repeatedEntry (asub,  , answRef,  , status) (sf,  , divergingEntry (asub,  , answRef)) -> (sf (); added := true; divergingEntry (asub,  , answRef))let rec answCheck(s',  , answRef,  , o) answCheckVariant (s',  , answRef,  , o)let rec updateTable() let let rec update[]flag flag update(answRef :: aList)flag (let let  in in if (l = lookup (answRef)) then (* no new solutions were added in the previous stage *)
update aList flag else (* new solutions were added *)
(updateAnswLookup (l,  , answRef); update aList true))let  inlet  in in added := falserlet  inlet  inlet  inlet  inlet  inlet  in(* memberCtxS ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t.  V'[^n]  is an instance of V
       then return true
         otherwise false
    *)
let rec memberCtx((g,  , v),  , g') let let rec instanceCtx'((g,  , v),  , null,  , n) nONE instanceCtx'((g,  , v),  , decl (g',  , d' as dec (_,  , v')),  , n) if instance (g,  , (v,  , id),  , (v',  , shift n)) then sOME (d') else instanceCtx' ((g,  , v),  , g',  , n + 1) in instanceCtx' ((g,  , v),  , g',  , 1)(* local *)
end