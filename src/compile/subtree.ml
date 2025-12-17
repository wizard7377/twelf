SubTree  Whnf WHNF    Unify UNIFY    Print PRINT    CPrint CPRINT    Formatter FORMATTER    Names NAMES    CSManager CS_MANAGER     SUBTREE  struct (*!  structure IntSyn = IntSyn' !*)
(*!  structure CompSyn = CompSyn' !*)
(*!  structure RBSet = RBSet !*)
type Nvar(* index for normal variables *)
type Bvar(* index for bound variables *)
type Bdepth(* depth of locally bound variables *)
(* A substitution tree is defined as follows:
     Node := Leaf (ns, G, sgoal) | Node(ns, Set of Nodes)
     normal linear modal substitutions ns := . | R/n, ns

   For each node we have the following invariant:
        S |- ns : S'    i.e. ns substitutes for internal variables
        G'|- as : G     i.e. as substitutes for assignable variables
        G |- qs : G     i.e. qs substitutes for modal variables
                             occuring in the query term

  NOTE: Since lambda-abstraction carries a type-label, we must generalize
   the type-label, and hence perform indexing on type-labels. -- On
   the other hand during unification or assignment an instantiation of
   the existential variables occurring in the type-label is not
   necessary. They must have been instantiated already. However, we
   must still instantiate internal nvars.

  Example: given the following two terms:
   hilnd ((A imp (B imp C)) imp ((A imp B) imp (A imp C))) (s) (impi [u:nd (A imp B imp C)]
                     impi [v:nd (A imp B)]
                     impi [w:nd A] impe (impe u w) (impe v w)).

   hilnd (A imp (B imp A)) (s) (impi [u:nd A]
                     impi [v:nd B]
                     impi [w:nd A] impe (impe u w) (impe v w)).


  if we generalize (A imp B imp C) then we must obtain

  hilnd (n1 imp (n2 imp n3)) (s) (impi [u:nd n4]
             impi [v:nd n5]
             impi [w:nd A] impe (impe u w) (impe v w)).

  otherwise we could obtain a term which is not well-typed.

  *)
(* typeLabel distinguish between declarations (=type labels)
   which are subject to indexing, but only the internal nvars will
   be instantiated during asssignment and Body which are subject to
   indexing and existential variables and nvars will be instantiated
   during assignment
 *)
type TypeLabeltype NormalSubsts(* key = int = bvar *)
type AssSubtype AssSubsts(* key = int = bvar *)
type QuerySubststype Cnstrtype CnstrSubsts(* key = int = bvar *)
type CGoal(* cid of clause *)
type GenTypetype Treetype Candidate(* Initialization of substitutions *)
let  inlet  inlet  inlet  in(* Identity substitution *)
let rec isIds isEmpty s(* Initialize substitution tree *)
let rec makeTree() ref (node (nid (),  , new ()))(* Test if node has any children *)
let rec noChildrenc isEmpty c(* Index array

   Invariant:
   For all type families  a  indexArray = [a1,...,an]
   where a1,...,an is a substitution tree consisting of all constants
   for target family ai

   *)
let  inmodule module module exception exception exception (* Auxiliary functions *)
let rec cidFromHead(const c) c cidFromHead(def c) clet rec dotn(0,  , s) s dotn(i,  , s) dotn (i - 1,  , dot1 s)let rec compose'(null,  , g) g compose'(decl (g,  , d),  , g') decl (compose' (g,  , g'),  , d)let rec shift(null,  , s) s shift(decl (g,  , d),  , s) dot1 (shift (g,  , s))let rec raiseType(null,  , v) v raiseType(decl (g,  , d),  , v) raiseType (g,  , lam (d,  , v))let rec printSub(shift n) print ("Shift " ^ toString n ^ "\n") printSub(dot (idx n,  , s)) (print ("Idx " ^ toString n ^ " . "); printSub s) printSub(dot (exp (eVar (_,  , _,  , _,  , _)),  , s)) (print ("Exp (EVar _ ). "); printSub s) printSub(dot (exp (aVar (_)),  , s)) (print ("Exp (AVar _ ). "); printSub s) printSub(dot (exp (eClo (aVar (_),  , _)),  , s)) (print ("Exp (AVar _ ). "); printSub s) printSub(dot (exp (eClo (_,  , _)),  , s)) (print ("Exp (EClo _ ). "); printSub s) printSub(dot (exp (_),  , s)) (print ("Exp (_ ). "); printSub s) printSub(dot (undef,  , s)) (print ("Undef . "); printSub s)(*
     Linear normal higher-order patterns
           p ::= n | Root(c, S) | Root(b, S) | Lam (D, p)

                 where n is a linear bound "normalized" variable

          SP ::= p ; S | NIL

     Context
        G : context for bound variables (bvars)
            (type information is stored in the context)
        G ::= . | G, x : A

        S : context for linear normalized bound variables (nvars)
            (no type information is stored in the context)
            (these are the types of the variables definitions)
        S ::= . | S, n

     Templates: G ; S |- p
     Substitutions: G ; S |- nsub : S'

    Let s is a substitution for normalized bound variables (nvars)
    and nsub1 o nsub2 o .... o nsubn = s, s.t.
     G, S_2|- nsub1 : S_1
     G, S_3|- nsub2 : S_2
      ....
     G |- nsubn : S_n
      . ; G |- s : G, S_1

    A term U can be decomposed into a term p together with a sequenence of
    substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:

    If    G |- U

    then

       G, S |- p

        G |- s : G, S

        G |- p[s]     and p[s] = U

   In addition:
   all expressions in the index are linear, i.e.
   an expression is first linearized before it is inserted into the index
   (this makes retrieving all axpressions from the index which unify with
    a given expression simpler, because we can omit the occurs check)

   *)
(* ---------------------------------------------------------------*)
(* nctr = |D| =  #normal variables *)
let  inlet rec newNVar() (nctr := ! nctr + 1; nVar (! nctr))let rec eqHeads(const k,  , const k') (k = k') eqHeads(bVar k,  , bVar k') (k = k') eqHeads(def k,  , def k') (k = k') eqHeads(_,  , _) false(* most specific linear common generalization *)
(* compatible (T, U) = (C, rho_u', rho_t') opt
    if
       U, T are both in normal form
       U and T share at least the top function symbol
   then
     C[rho_u'] = U and C[rho_t'] = T
   *)
let rec compatible(label,  , t,  , u,  , rho_t,  , rho_u) let let rec genExp(label,  , b,  , t as nVar n,  , u as root (h,  , s)) (insert rho_u (n,  , (label,  , u)); t) genExp(label,  , b,  , t as root (h1,  , s1),  , u as root (h2,  , s2)) if eqHeads (h1,  , h2) then root (h1,  , genSpine (label,  , b,  , s1,  , s2)) else (match b with regular -> (insert rho_t (! nctr + 1,  , (label,  , t)); insert rho_u (! nctr + 1,  , (label,  , u)); newNVar ()) _ -> raise (generalization "Should never happen!")) genExp(label,  , b,  , lam (d1 as dec (n,  , a1),  , t1),  , lam (d2 as dec (_,  , a2),  , u2)) lam (dec (n,  , genExp (typeLabel,  , regular,  , a1,  , a2)),  , genExp (label,  , b,  , t1,  , u2)) genExp(label,  , b,  , pi (dD1 as (d1,  , no),  , e1),  , pi (dD2 as (d2,  , no),  , e2)) pi ((genDec (typeLabel,  , regular,  , d1,  , d2),  , no),  , genExp (label,  , b,  , e1,  , e2)) genExp(label,  , b,  , pi (dD1 as (d1,  , maybe),  , e1),  , pi (dD2 as (d2,  , maybe),  , e2)) pi ((genDec (typeLabel,  , regular,  , d1,  , d2),  , maybe),  , genExp (label,  , b,  , e1,  , e2)) genExp(label,  , b,  , pi (dD1 as (d1,  , meta),  , e1),  , pi (dD2 as (d2,  , meta),  , e2)) pi ((genDec (typeLabel,  , regular,  , d1,  , d2),  , meta),  , genExp (label,  , b,  , e1,  , e2)) genExp(label,  , b,  , t,  , u) raise (generalization "Cases where U= EVar or EClo should never happen!") genSpine(label,  , b,  , nil,  , nil) nil genSpine(label,  , b,  , app (t,  , s1),  , app (u,  , s2)) app (genExp (label,  , b,  , t,  , u),  , genSpine (label,  , b,  , s1,  , s2)) genDec(label,  , b,  , dec (n,  , e1),  , dec (n',  , e2)) dec (n,  , genExp (label,  , b,  , e1,  , e2))let rec genTop(label,  , t as root (h1,  , s1),  , u as root (h2,  , s2)) if eqHeads (h1,  , h2) then root (h1,  , genSpine (label,  , regular,  , s1,  , s2)) else raise (generalization "Top-level function symbol not shared") genTop(label,  , lam (d1 as dec (n,  , a1),  , t1),  , lam (d2 as dec (_,  , a2),  , u2)) lam (dec (n,  , genExp (label,  , regular,  , a1,  , a2)),  , genTop (label,  , t1,  , u2)) genTop(_,  , _,  , _) raise (generalization "Top-level function symbol not shared") in try  with (* compatibleSub(nsub_t, nsub_e) = (sg, rho_t, rho_e) opt

   if dom(nsub_t) <= dom(nsub_e)
      codom(nsub_t) : linear hop in normal form (may contain normal vars)
      codom(nsub_e) : linear hop in normal form (does not contain normal vars)
   then
     nsub_t = [rho_t]sg
     nsub_e = [rho_e]sg

    G_e, Glocal_e |- nsub_e : Sigma
    G_t, Glocal_t |- nsub_t : Sigma'
    Sigma' <= Sigma

    Glocal_e ~ Glocal_t  (have approximately the same type)

   *)
let rec compatibleSub(nsub_t,  , nsub_e) let let  in(* by invariant rho_t = empty, since nsub_t <= nsub_e *)
let  in in if isId (sg) then nONE else sOME (sg,  , rho_t,  , rho_e)(* mkNode (N, sg, r1, (G, RC), r2) = N'    *)
let rec mkNode(node (_,  , children),  , sg,  , rho1,  , gR as (g,  , rC),  , rho2) let let  in in insertList c [(1,  , node (rho1,  , children)); (2,  , leaf (rho2,  , g,  , rC))]node (sg,  , c) mkNode(leaf (_,  , g1,  , rC1),  , sg,  , rho1,  , gR as (g2,  , rC2),  , rho2) let let  in in insertList c [(1,  , leaf (rho1,  , g1,  , rC1)); (2,  , leaf (rho2,  , g2,  , rC2))]node (sg,  , c)(* Insertion *)
(* compareChild (children, (n, child), n, n', (G, R)) = ()

   *)
let rec compareChild(children,  , (n,  , child),  , nsub_t,  , nsub_e,  , gR as (g_clause2,  , res_clause2)) (match compatibleSub (nsub_t,  , nsub_e) with nONE -> (insert children (n + 1,  , leaf (nsub_e,  , g_clause2,  , res_clause2))) sOME (sg,  , rho1,  , rho2) -> (if isId rho1 then if isId rho2 then (* sg = nsub_t = nsub_e *)
(insertShadow children (n,  , mkNode (child,  , sg,  , rho1,  , gR,  , rho2))) else (* sg = nsub_t and nsub_e = sg o rho2 *)
(insertShadow children (n,  , insert (child,  , rho2,  , gR))) else (insertShadow children (n,  , mkNode (child,  , sg,  , rho1,  , gR,  , rho2)))))(* insert (N, nsub_e, (G, R2)) = N'

     if s is the substitution in node N
        G |- nsub_e : S and
    G, S' |- s : S
    then
     N' contains a path n_1 .... n_n s.t.
     [n_n] ...[n_1] s = nsub_e
  *)
 insert(n as leaf (nsub_t,  , g_clause1,  , r1),  , nsub_e,  , gR as (g_clause2,  , r2)) (match compatibleSub (nsub_t,  , nsub_e) with nONE -> raise (error "Leaf is not compatible substitution r") sOME (sg,  , rho1,  , rho2) -> mkNode (n,  , sg,  , rho1,  , gR,  , rho2)) insert(n as node (_,  , children),  , nsub_e,  , gR as (g_clause2,  , rC)) if noChildren children then (* initial *)
(insert children (1,  , (leaf (nsub_e,  , g_clause2,  , rC))); n) else (match (last children) with (n,  , child as node (nsub_t,  , children')) -> (compareChild (children,  , (n,  , child),  , nsub_t,  , nsub_e,  , gR); n) (n,  , child as leaf (nsub_t,  , g1,  , rC1)) -> (compareChild (children,  , (n,  , child),  , nsub_t,  , nsub_e,  , gR); n))(* retrieval (U,s)
     retrieves all clauses which unify with (U,s)

     backtracking implemented via SML failure continuation

   *)
let rec normalizeNExp(nVar n,  , csub) let let  in in insert csub (n,  , a)a normalizeNExp(root (h,  , s),  , nsub) root (h,  , normalizeNSpine (s,  , nsub)) normalizeNExp(lam (d,  , u),  , nsub) lam (normalizeNDec (d,  , nsub),  , normalizeNExp (u,  , nsub)) normalizeNExp(pi ((d,  , p),  , u),  , nsub) pi ((normalizeNDec (d,  , nsub),  , p),  , normalizeNExp (u,  , nsub)) normalizeNSpine(nil,  , _) nil normalizeNSpine(app (u,  , s),  , nsub) app (normalizeNExp (u,  , nsub),  , normalizeNSpine (s,  , nsub)) normalizeNDec(dec (n,  , e),  , nsub) dec (n,  , normalizeNExp (e,  , nsub))(* assign (G, Us1, U2, nsub_goal, asub, csub, cnstr) = cnstr
   if G = local assumptions, G' context of query
      G1 |- U1 : V1
     G', G  |- s1 : G1
     G', G  |- U1[s1]     and s1 is an explicit substitution

      G2 |- U2 : V2
  G', G  |- asub' : G2 and asub is a assignable substitution

      U2 is eta-expanded
   then
   G2, N |- cnstr
      G2 |- csub : N
      G2 |- cnstr[csub]

      G  |- nsub_goal : N
     *)
let rec assign(nvaronly,  , glocal_u1,  , us1,  , u2,  , nsub_goal,  , asub,  , csub,  , cnstr) let let  inlet rec assignHead(nvaronly,  , depth,  , glocal_u1,  , us1 as (root (h1,  , s1),  , s1),  , u2 as root (h2,  , s2),  , cnstr) (match (h1,  , h2) with (const (c1),  , const (c2)) -> if (c1 = c2) then assignSpine (nvaronly,  , depth,  , glocal_u1,  , (s1,  , s1),  , s2,  , cnstr) else raise (assignment "Constant clash") (skonst (c1),  , skonst (c2)) -> if (c1 = c2) then assignSpine (nvaronly,  , depth,  , glocal_u1,  , (s1,  , s1),  , s2,  , cnstr) else raise (assignment "Skolem constant clash") (def d1,  , _) -> assignExp (nvaronly,  , depth,  , glocal_u1,  , expandDef us1,  , u2,  , cnstr) (fgnConst (cs1,  , conDec (n1,  , _,  , _,  , _,  , _,  , _)),  , fgnConst (cs2,  , conDec (n2,  , _,  , _,  , _,  , _,  , _))) -> (* we require unique string representation of external constants *)
if (cs1 = cs2) && (n1 = n2) then cnstr else raise (assignment "Foreign Constant clash") (fgnConst (cs1,  , conDef (n1,  , _,  , _,  , w1,  , _,  , _,  , _)),  , fgnConst (cs2,  , conDef (n2,  , _,  , _,  , v,  , w2,  , _,  , _))) -> (if (cs1 = cs2) && (n1 = n2) then cnstr else assignExp (nvaronly,  , depth,  , glocal_u1,  , (w1,  , s1),  , w2,  , cnstr)) (fgnConst (_,  , conDef (_,  , _,  , _,  , w1,  , _,  , _,  , _)),  , _) -> assignExp (nvaronly,  , depth,  , glocal_u1,  , (w1,  , s1),  , u2,  , cnstr) (_,  , fgnConst (_,  , conDef (_,  , _,  , _,  , w2,  , _,  , _,  , _))) -> assignExp (nvaronly,  , depth,  , glocal_u1,  , us1,  , w2,  , cnstr) (_,  , _) -> (raise (assignment ("Head mismatch ")))) assignExpW(nvaronly,  , depth,  , glocal_u1,  , (uni l1,  , s1),  , uni l2,  , cnstr) cnstr assignExpW(nvaronly,  , depth,  , glocal_u1,  , us1,  , nVar n,  , cnstr) (insert nsub_goal (n,  , (glocal_u1,  , (nvaronly,  , eClo (us1)))); cnstr) assignExpW(body,  , depth,  , glocal_u1,  , us1 as (root (h1,  , s1),  , s1),  , u2 as root (h2,  , s2),  , cnstr) (match h2 with bVar (k2) -> if (k2 > depth) then (* BVar(k2) stands for an existential variable *)
(* S2 is an etaSpine by invariant *)
(insert asub ((k2 - ctxLength (glocal_u1)),  , assign (glocal_u1,  , eClo (us1))); cnstr) else (match h1 with bVar (k1) -> if (k1 = k2) then assignSpine (body,  , depth,  , glocal_u1,  , (s1,  , s1),  , s2,  , cnstr) else raise (assignment "Bound variable clash") _ -> raise (assignment "Head mismatch")) _ -> assignHead (body,  , depth,  , glocal_u1,  , us1,  , u2,  , cnstr)) assignExpW(typeLabel,  , depth,  , glocal_u1,  , us1 as (root (h1,  , s1),  , s1),  , u2 as root (h2,  , s2),  , cnstr) (match h2 with bVar (k2) -> if (k2 > depth) then (* BVar(k2) stands for an existential variable *)
(* then by invariant, it must have been already instantiated *)
cnstr else (match h1 with bVar (k1) -> if (k1 = k2) then assignSpine (typeLabel,  , depth,  , glocal_u1,  , (s1,  , s1),  , s2,  , cnstr) else raise (assignment "Bound variable clash") _ -> raise (assignment "Head mismatch")) _ -> assignHead (typeLabel,  , depth,  , glocal_u1,  , us1,  , u2,  , cnstr)) assignExpW(nvaronly,  , depth,  , glocal_u1,  , us1,  , u2 as root (bVar k2,  , s),  , cnstr) if (k2 > depth) then (* BVar(k2) stands for an existential variable *)
(* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *)
(* Glocal_u1 |- Us1 *)
(match nvaronly with typeLabel -> cnstr body -> (insert asub ((k2 - depth),  , assign (glocal_u1,  , eClo (us1))); cnstr)) else (match nvaronly with typeLabel -> cnstr body -> (match us1 with (eVar (r,  , _,  , v,  , cnstr),  , s) -> let let  in in (eqn (glocal_u1,  , eClo (us1),  , u2') :: cnstr) (eClo (u,  , s'),  , s) -> assignExp (body,  , depth,  , glocal_u1,  , (u,  , comp (s',  , s)),  , u2,  , cnstr) (fgnExp (_,  , ops),  , _) -> let let  in in (eqn (glocal_u1,  , eClo (us1),  , u2') :: cnstr))) assignExpW(nvaronly,  , depth,  , glocal_u1,  , (lam (d1 as dec (_,  , a1),  , u1),  , s1),  , lam (d2 as dec (_,  , a2),  , u2),  , cnstr) let let  in(* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
             *)
 in assignExp (nvaronly,  , depth + 1,  , decl (glocal_u1,  , decSub (d1,  , s1)),  , (u1,  , dot1 s1),  , u2,  , cnstr') assignExpW(nvaronly,  , depth,  , glocal_u1,  , (pi ((d1 as dec (_,  , a1),  , _),  , u1),  , s1),  , pi ((d2 as dec (_,  , a2),  , _),  , u2),  , cnstr) let let  in(* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
            *)
 in assignExp (nvaronly,  , depth + 1,  , decl (glocal_u1,  , decSub (d1,  , s1)),  , (u1,  , dot1 s1),  , u2,  , cnstr') assignExpW(nvaronly,  , depth,  , glocal_u1,  , us1 as (eVar (r,  , _,  , v,  , cnstr),  , s),  , u2,  , cnstr) let let  in in (eqn (glocal_u1,  , eClo (us1),  , u2') :: cnstr) assignExpW(nvaronly,  , depth,  , glocal_u1,  , us1 as (eClo (u,  , s'),  , s),  , u2,  , cnstr) assignExp (nvaronly,  , depth,  , glocal_u1,  , (u,  , comp (s',  , s)),  , u2,  , cnstr) assignExpW(nvaronly,  , depth,  , glocal_u1,  , us1 as (fgnExp (_,  , ops),  , _),  , u2,  , cnstr) let let  in in (eqn (glocal_u1,  , eClo (us1),  , u2') :: cnstr) assignExpW(nvaronly,  , depth,  , glocal_u1,  , us1,  , u2 as fgnExp (_,  , ops),  , cnstr) (eqn (glocal_u1,  , eClo (us1),  , u2) :: cnstr)(*      | assignExpW (nvaronly, depth, Glocal_u1, (U1, s1), I.Lam (D2, U2), cnstr) =
          (* Cannot occur if expressions are eta expanded *)
          raise Assignment "Cannot occur if expressions in clause heads are eta-expanded"*)
(*      | assignExpW (nvaronly, depth, Glocal_u1, (I.Lam (D1, U1), s1), U2, cnstr) =
      (* ETA: can't occur if eta expanded *)
            raise Assignment "Cannot occur if expressions in query are eta-expanded"
*)
(* same reasoning holds as above *)
 assignSpine(nvaronly,  , depth,  , glocal_u1,  , (nil,  , _),  , nil,  , cnstr) cnstr assignSpine(nvaronly,  , depth,  , glocal_u1,  , (sClo (s1,  , s1'),  , s1),  , s,  , cnstr) assignSpine (nvaronly,  , depth,  , glocal_u1,  , (s1,  , comp (s1',  , s1)),  , s,  , cnstr) assignSpine(nvaronly,  , depth,  , glocal_u1,  , (app (u1,  , s1),  , s1),  , app (u2,  , s2),  , cnstr) let let  in(* nsub_goal, asub may be destructively updated *)
 in assignSpine (nvaronly,  , depth,  , glocal_u1,  , (s1,  , s1),  , s2,  , cnstr') assignExp(nvaronly,  , depth,  , glocal_u1,  , us1,  , u2,  , cnstr) assignExpW (nvaronly,  , depth,  , glocal_u1,  , whnf us1,  , u2,  , cnstr) in assignExp (nvaronly,  , depth,  , glocal_u1,  , us1,  , u2,  , cnstr)(* assignable (g, nsub, nsub_goal, asub, csub, cnstr) = (nsub_goal', csub, cnstr') option

    nsub, nsub_goal, nsub_goal' are  well-formed normal substitutions
    asub is a well-formed assignable substitution
    csub is maps normal variables to avars

        G  |- nsub_goal
        G' |- nsub : N
        G  |- asub : G'

    G'     |- csub : N'
    G', N' |- cnstr
    G'     |- cnstr[csub]

   *)
let rec assignableLazy(nsub,  , nsub_query,  , assignSub,  , (nsub_left,  , cnstrSub),  , cnstr) let let  inlet  inlet rec assign'(nsub_query,  , nsub) let let  inlet  in in (sOME (union nsub_query_left nsub_query',  , (union nsub_left nsub_left',  , cnstrSub),  , ! cref)) in try  with let rec assignableEager(nsub,  , nsub_query,  , assignSub,  , cnstrSub,  , cnstr) let let  inlet  inlet rec assign'(nsub_query,  , nsub) let let  in(* normalize nsub_left (or require that it is normalized
             collect all left-over nsubs and later combine it with cnstrsub
           *)
let  in in (* cnstr[rsub] *)
(* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *)
(sOME (union nsub_query_left nsub_query',  , cnstrSub,  , ! cref)) in try  with (* Unification *)
let rec unifyW(g,  , (x as aVar (r as ref nONE),  , shift 0),  , us2) (r := sOME (eClo (us2))) unifyW(g,  , (x as aVar (r as ref nONE),  , s),  , us2 as (u,  , s2)) (print "unifyW -- not s = Id\n"; print ("Us2 = " ^ expToString (g,  , eClo (us2)) ^ "\n"); r := sOME (eClo (us2))) unifyW(g,  , xs1,  , us2) unifyW (g,  , xs1,  , us2)let rec unify(g,  , xs1,  , us2) unifyW (g,  , whnf xs1,  , whnf us2)let rec unifiable(g,  , us1,  , us2) try  with (* Convert context G into explicit substitution *)
(* ctxToEVarSub (i, G, G', asub, s) = s' *)
let rec ctxToExplicitSub(i,  , gquery,  , null,  , asub) id ctxToExplicitSub(i,  , gquery,  , decl (gclause,  , dec (_,  , a)),  , asub) let let  inlet  in in match lookup asub i with nONE -> () sOME (assign (glocal_u,  , u)) -> x' := sOME (raiseType (glocal_u,  , u))dot (exp (u'),  , s) ctxToExplicitSub(i,  , gquery,  , decl (gclause,  , aDec (_,  , d)),  , asub) let let  in in (match lookup asub i with nONE -> () sOME (assign (glocal_u,  , u)) -> x' := sOME (u))dot (exp (eClo (u',  , shift (~ d))),  , ctxToExplicitSub (i + 1,  , gquery,  , gclause,  , asub))(* d = I.ctxLength Glocal_u *)
let rec solveAuxG(trivial,  , s,  , gquery) true solveAuxG(unifyEq (glocal,  , e1,  , n,  , eqns),  , s,  , gquery) let let  inlet  in in if unifiable (g,  , (n,  , s'),  , (e1,  , s')) then solveAuxG (eqns,  , s,  , gquery) else falselet rec solveCnstr(gquery,  , gclause,  , nil,  , s) true solveCnstr(gquery,  , gclause,  , eqn (glocal,  , u1,  , u2) :: cnstr,  , s) (unifiable (compose' (gquery,  , glocal),  , (u1,  , id),  , (u2,  , shift (glocal,  , s))) && solveCnstr (gquery,  , gclause,  , cnstr,  , s))let rec solveResiduals(gquery,  , gclause,  , cGoals (auxG,  , cid,  , conjGoals,  , i),  , asub,  , cnstr',  , sc) let let  inlet  in in if success then (sc ((conjGoals,  , s),  , cid, (* B *)
)) else ()let rec ithChild(cGoals (_,  , _,  , _,  , i),  , n) (i = n)let rec retrieveChild(num,  , child,  , nsub_query,  , assignSub,  , cnstr,  , gquery,  , sc) let let rec retrieve(leaf (nsub,  , gclause,  , residuals),  , nsub_query,  , assignSub,  , cnstrSub,  , cnstr) (match assignableEager (nsub,  , nsub_query,  , assignSub,  , cnstrSub,  , cnstr)(* destructively updates assignSub, might initiate backtracking  *)
 with nONE -> () sOME (nsub_query',  , cnstrSub',  , cnstr') -> (if (isId nsub_query')(* cnstrSub' = empty? by invariant *)
 then (* LCO optimization *)
if ithChild (residuals,  , ! num) then solveResiduals (gquery,  , gclause,  , residuals,  , assignSub,  , cnstr',  , sc) else trail (fun () -> solveResiduals (gquery,  , gclause,  , residuals,  , assignSub,  , cnstr',  , sc)) else raise (error "Left-over normal substitutions!"))) retrieve(node (nsub,  , children),  , nsub_query,  , assignSub,  , cnstrSub,  , cnstr) (match assignableEager (nsub,  , nsub_query,  , assignSub,  , cnstrSub,  , cnstr)(* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
(* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
 with nONE -> () sOME (nsub_query',  , cnstrSub',  , cnstr') -> (forall children (fun (n,  , child) -> retrieve (child,  , nsub_query',  , copy assignSub,  , copy cnstrSub',  , cnstr')))) in retrieve (child,  , nsub_query,  , assignSub,  , cnstrSubId (),  , cnstr)let rec retrieval(n,  , sTree as node (s,  , children),  , g,  , r,  , sc) let let  in in insert nsub_query (1,  , (null,  , (body,  , r)))forall children (fun (_,  , c) -> retrieveChild (n,  , c,  , nsub_query,  , assignSub,  , nil,  , g,  , sc))(*----------------------------------------------------------------------------*)
(* Retrieval via set of candidates *)
let rec retrieveAll(num,  , child,  , nsub_query,  , assignSub,  , cnstr,  , candSet) let let  inlet rec retrieve(leaf (nsub,  , gclause,  , residuals),  , nsub_query,  , assignSub,  , (nsub_left,  , cnstrSub),  , cnstr) (match assignableLazy (nsub,  , nsub_query,  , assignSub,  , (nsub_left,  , cnstrSub),  , cnstr)(* destructively updates assignSub, might initiate backtracking  *)
 with nONE -> () sOME (nsub_query',  , (nsub_left',  , cnstrSub'),  , cnstr') -> (if (isId nsub_query') then (* LCO optimization *)
(i := ! i + 1; insert candSet (! i,  , (assignSub,  , nsub_left',  , cnstrSub',  , cnstr',  , gclause,  , residuals)); ()) else raise (error "Left-over normal substitutions!"))) retrieve(node (nsub,  , children),  , nsub_query,  , assignSub,  , (nsub_left,  , cnstrSub),  , cnstr) (match assignableLazy (nsub,  , nsub_query,  , assignSub,  , (nsub_left,  , cnstrSub),  , cnstr)(* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
(* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
 with nONE -> () sOME (nsub_query',  , (nsub_left',  , cnstrSub'),  , cnstr') -> (forall children (fun (n,  , child) -> retrieve (child,  , nsub_query',  , copy assignSub,  , (copy nsub_left',  , copy cnstrSub'),  , cnstr')))) in retrieve (child,  , nsub_query,  , assignSub,  , (nid (),  , cnstrSubId ()),  , cnstr)let rec retrieveCandidates(n,  , sTree as node (s,  , children),  , gquery,  , r,  , sc) let let  inlet  inlet rec solveCandidate(i,  , candSet) match (lookup candSet i) with nONE -> ((* print "No candidate left anymore\n" ;*)
()) sOME (assignSub,  , nsub_left,  , cnstrSub,  , cnstr,  , gclause,  , residuals, (* CGoals(AuxG, cid, ConjGoals, i) *)
) -> (trail (fun () -> (forall nsub_left (fun (nv,  , (l,  , u)) -> match (lookup cnstrSub nv) with nONE -> raise (error "Left-over nsubstitution") sOME (aVar a) -> a := sOME (u)); solveResiduals (gquery,  , gclause,  , residuals,  , assignSub,  , cnstr,  , sc))); solveCandidate (i + 1,  , candSet, (* sc = (fn S => (O::S)) *)
)) in insert nsub_query (1,  , (null,  , (body,  , r)))forall children (fun (_,  , c) -> retrieveAll (n,  , c,  , nsub_query,  , assignSub,  , nil,  , candSet))(* execute one by one all candidates : here ! *)
solveCandidate (1,  , candSet)let rec matchSig(a,  , g,  , ps as (root (ha,  , s),  , s),  , sc) let let  in in (* retrieval (n, !Tree, G, I.EClo(ps), sc)   *)
retrieveCandidates (n,  , ! tree,  , g,  , eClo (ps),  , sc)let rec matchSigIt(a,  , g,  , ps as (root (ha,  , s),  , s),  , sc) let let  in in retrieval (n,  , ! tree,  , g,  , eClo (ps),  , sc)let rec sProgReset() (nctr := 1; modify (fun (n,  , tree) -> (n := 0; tree := ! (makeTree ()); (n,  , tree))) indexArray)let rec sProgInstall(a,  , head (e,  , g,  , eqs,  , cid),  , r) let let  inlet  in in insert nsub_goal (1,  , (body,  , e))tree := insert (! tree,  , nsub_goal,  , (g,  , cGoals (eqs,  , cid,  , r,  , ! n + 1)))n := ! n + 1let  inlet  inlet  in(* local *)
end