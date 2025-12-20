(* Substitution Tree indexing *)


(* Author: Brigitte Pientka *)


module SubTree (Whnf : WHNF) (Unify : UNIFY) (Print : PRINT) (CPrint : CPRINT) (Formatter : FORMATTER) (Names : NAMES) (CSManager : CS_MANAGER) : SUBTREE = struct (*!  structure IntSyn = IntSyn' !*)

(*!  structure CompSyn = CompSyn' !*)

(*!  structure RBSet = RBSet !*)

type nvar = int
(* index for_sml normal variables *)

type bvar = int
(* index for_sml bound variables *)

type bdepth = int
(* depth of locally bound variables *)

(* A substitution tree is follows:
     Node := Leaf (ns, G, sgoal) | Node(ns, Set of Nodes)
     normal linear modal substitutions ns := . | R/n, ns

   For each node we have the following invariant:
        S |- ns : S'    i.e. ns substitutes for_sml internal variables
        G'|- as : G     i.e. as substitutes for_sml assignable variables
        G |- qs : G     i.e. qs substitutes for_sml modal variables
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

type typeLabel = TypeLabel | Body
type normalSubsts = typeLabel * IntSyn.exp RBSet.ordSet
(* key = int = bvar *)

type assSub = Assign of (IntSyn.dec IntSyn.ctx * IntSyn.exp)
type assSubsts = assSub RBSet.ordSet
(* key = int = bvar *)

type querySubsts = IntSyn.dec IntSyn.ctx * (typeLabel * IntSyn.exp) RBSet.ordSet
type cnstr = Eqn of IntSyn.dec IntSyn.ctx * IntSyn.exp * IntSyn.exp
type cnstrSubsts = IntSyn.exp RBSet.ordSet
(* key = int = bvar *)

type cGoal = CGoals of CompSyn.auxGoal * IntSyn.cid * CompSyn.conjunction * int
(* cid of clause *)

type genType = Top | Regular
type tree = Leaf of normalSubsts * IntSyn.dec IntSyn.ctx * cGoal | Node of normalSubsts * tree RBSet.ordSet
type candidate = (assSubsts * normalSubsts * cnstrSubsts * cnstr * IntSyn.dec IntSyn.ctx * cGoal)
(* Initialization of substitutions *)

let nid : unit -> normalSubsts = RBSet.new_
let assignSubId : unit -> assSubsts = RBSet.new_
let cnstrSubId : unit -> cnstrSubsts = RBSet.new_
let querySubId : unit -> querySubsts = RBSet.new_
(* Identity substitution *)

let rec isId s  = RBSet.isEmpty s
(* Initialize substitution tree *)

let rec makeTree ()  = ref (Node (nid (), RBSet.new_ ()))
(* Test if node has any children *)

let rec noChildren C  = RBSet.isEmpty C
(* Index array

   Invariant:
   For all type families  a  indexArray = [a1,...,an]
   where a1,...,an is a substitution tree consisting of all constants
   for_sml target family ai

   *)

let indexArray = Array.tabulate (Global.maxCid, (fun i -> (ref 0, makeTree ())))
module I = IntSyn
module C = CompSyn
module S = RBSet
exception Error of string
exception Assignment of string
exception Generalization of string
(* Auxiliary functions *)

let rec cidFromHead = function (I.Const c) -> c | (I.Def c) -> c
let rec dotn = function (0, s) -> s | (i, s) -> dotn (i - 1, I.dot1 s)
let rec compose' = function (IntSyn.Null, G) -> G | (IntSyn.Decl (G, D), G') -> IntSyn.Decl (compose' (G, G'), D)
let rec shift = function (IntSyn.Null, s) -> s | (IntSyn.Decl (G, D), s) -> I.dot1 (shift (G, s))
let rec raiseType = function (I.Null, V) -> V | (I.Decl (G, D), V) -> raiseType (G, I.Lam (D, V))
let rec printSub = function (IntSyn.Shift n) -> print ("Shift " ^ Int.toString n ^ "\n") | (IntSyn.Dot (IntSyn.Idx n, s)) -> (print ("Idx " ^ Int.toString n ^ " . "); printSub s) | (IntSyn.Dot (IntSyn.Exp (IntSyn.EVar (_, _, _, _)), s)) -> (print ("Exp (EVar _ ). "); printSub s) | (IntSyn.Dot (IntSyn.Exp (IntSyn.AVar (_)), s)) -> (print ("Exp (AVar _ ). "); printSub s) | (IntSyn.Dot (IntSyn.Exp (IntSyn.EClo (IntSyn.AVar (_), _)), s)) -> (print ("Exp (AVar _ ). "); printSub s) | (IntSyn.Dot (IntSyn.Exp (IntSyn.EClo (_, _)), s)) -> (print ("Exp (EClo _ ). "); printSub s) | (IntSyn.Dot (IntSyn.Exp (_), s)) -> (print ("Exp (_ ). "); printSub s) | (IntSyn.Dot (IntSyn.Undef, s)) -> (print ("Undef . "); printSub s)
(*
     Linear normal higher-order patterns
           p ::= n | Root(c, S) | Root(b, S) | Lam (D, p)

                 where n is a linear bound "normalized" variable

          SP ::= p ; S | NIL

     Context
        G : context for_sml bound variables (bvars)
            (type information is stored in the context)
        G ::= . | G, x : A

        S : context for_sml linear normalized bound variables (nvars)
            (no type information is stored in the context)
            (these are the types of the variables definitions)
        S ::= . | S, n

     Templates: G ; S |- p
     Substitutions: G ; S |- nsub : S'

    Let s is a substitution for_sml normalized bound variables (nvars)
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

let nctr = ref 1
let rec newNVar ()  = (nctr := ! nctr + 1; I.NVar (! nctr))
let rec eqHeads = function (I.Const k, I.Const k') -> (k = k') | (I.BVar k, I.BVar k') -> (k = k') | (I.Def k, I.Def k') -> (k = k') | (_, _) -> false
(* most specific linear common generalization *)

(* compatible (T, U) = (C, rho_u', rho_t') opt
    if
       U, T are both in normal form
       U and T share at least the top function symbol
   then
     C[rho_u'] = U and C[rho_t'] = T
   *)

let rec compatible (label, T, U, rho_t, rho_u)  = ( let rec genExp = function (label, b, T, U) -> (S.insert rho_u (n, (label, U)); T) | (label, b, T, U) -> if eqHeads (H1, H2) then I.Root (H1, genSpine (label, b, S1, S2)) else (match b with Regular -> (S.insert rho_t (! nctr + 1, (label, T)); S.insert rho_u (! nctr + 1, (label, U)); newNVar ()) | _ -> raise (Generalization "Should never happen!")) | (label, b, I.Lam (D1, T1), I.Lam (D2, U2)) -> I.Lam (I.Dec (N, genExp (TypeLabel, Regular, A1, A2)), genExp (label, b, T1, U2)) | (label, b, I.Pi (DD1, E1), I.Pi (DD2, E2)) -> I.Pi ((genDec (TypeLabel, Regular, D1, D2), I.No), genExp (label, b, E1, E2)) | (label, b, I.Pi (DD1, E1), I.Pi (DD2, E2)) -> I.Pi ((genDec (TypeLabel, Regular, D1, D2), I.Maybe), genExp (label, b, E1, E2)) | (label, b, I.Pi (DD1, E1), I.Pi (DD2, E2)) -> I.Pi ((genDec (TypeLabel, Regular, D1, D2), I.Meta), genExp (label, b, E1, E2)) | (label, b, T, U) -> raise (Generalization "Cases where U= EVar or EClo should never happen!")
and genSpine = function (label, b, I.Nil, I.Nil) -> I.Nil | (label, b, I.App (T, S1), I.App (U, S2)) -> I.App (genExp (label, b, T, U), genSpine (label, b, S1, S2))
and genDec (label, b, I.Dec (N, E1), I.Dec (N', E2))  = I.Dec (N, genExp (label, b, E1, E2)) in let rec genTop = function (label, T, U) -> if eqHeads (H1, H2) then I.Root (H1, genSpine (label, Regular, S1, S2)) else raise (Generalization "Top-level function symbol not shared") | (label, I.Lam (D1, T1), I.Lam (D2, U2)) -> I.Lam (I.Dec (N, genExp (label, Regular, A1, A2)), genTop (label, T1, U2)) | (_, _, _) -> raise (Generalization "Top-level function symbol not shared") in  try Some (genTop (label, T, U)) with Generalization msg -> None )
(* compatibleSub(nsub_t, nsub_e) = (sg, rho_t, rho_e) opt

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

let rec compatibleSub (nsub_t, nsub_e)  = ( (* by invariant rho_t = empty, since nsub_t <= nsub_e *)
let (sg, rho_t, rho_e) = (nid (), nid (), nid ()) in let _ = S.forall nsub_e (fun (nv, (l', E)) -> (match (S.lookup nsub_t nv) with Some (l, T) -> (* by invariant d = d'
                                     therefore T and E have the same approximate type A *)
(if l = l' then (match compatible (l, T, E, rho_t, rho_e) with None -> (S.insert rho_t (nv, (l, T)); S.insert rho_e (nv, (l, E))) | Some (T') -> S.insert sg (nv, (l, T'))) else raise (Generalization "Labels don't agree\n")) | None -> S.insert rho_e (nv, (l', E)))) in  if isId (sg) then None else Some (sg, rho_t, rho_e) )
(* mkNode (N, sg, r1, (G, RC), r2) = N'    *)

let rec mkNode = function (Node (_, Children), sg, rho1, GR, rho2) -> ( let c = S.new_ () in  S.insertList c [(1, Node (rho1, Children)); (2, Leaf (rho2, G, RC))]; Node (sg, c) ) | (Leaf (_, G1, RC1), sg, rho1, GR, rho2) -> ( let c = S.new_ () in  S.insertList c [(1, Leaf (rho1, G1, RC1)); (2, Leaf (rho2, G2, RC2))]; Node (sg, c) )
(* Insertion *)

(* compareChild (children, (n, child), n, n', (G, R)) = ()

   *)

let rec compareChild (children, (n, child), nsub_t, nsub_e, GR)  = (match compatibleSub (nsub_t, nsub_e) with None -> (S.insert children (n + 1, Leaf (nsub_e, G_clause2, Res_clause2))) | Some (sg, rho1, rho2) -> (if isId rho1 then if isId rho2 then (* sg = nsub_t = nsub_e *)
(S.insertShadow children (n, mkNode (child, sg, rho1, GR, rho2))) else (* sg = nsub_t and nsub_e = sg o rho2 *)
(S.insertShadow children (n, insert (child, rho2, GR))) else (S.insertShadow children (n, mkNode (child, sg, rho1, GR, rho2)))))
and insert = function (N, nsub_e, GR) -> (match compatibleSub (nsub_t, nsub_e) with None -> raise (Error "Leaf is not compatible substitution r") | Some (sg, rho1, rho2) -> mkNode (N, sg, rho1, GR, rho2)) | (N, nsub_e, GR) -> if noChildren children then (* initial *)
(S.insert children (1, (Leaf (nsub_e, G_clause2, RC))); N) else (match (S.last children) with (n, child) -> (compareChild (children, (n, child), nsub_t, nsub_e, GR); N) | (n, child) -> (compareChild (children, (n, child), nsub_t, nsub_e, GR); N))
(* retrieval (U,s)
     retrieves all clauses which unify with (U,s)

     backtracking implemented via SML failure continuation

   *)

let rec normalizeNExp = function (I.NVar n, csub) -> ( let A = I.newAVar () in  S.insert csub (n, A); A ) | (I.Root (H, S), nsub) -> I.Root (H, normalizeNSpine (S, nsub)) | (I.Lam (D, U), nsub) -> I.Lam (normalizeNDec (D, nsub), normalizeNExp (U, nsub)) | (I.Pi ((D, P), U), nsub) -> I.Pi ((normalizeNDec (D, nsub), P), normalizeNExp (U, nsub))
and normalizeNSpine = function (I.Nil, _) -> I.Nil | (I.App (U, S), nsub) -> I.App (normalizeNExp (U, nsub), normalizeNSpine (S, nsub))
and normalizeNDec (I.Dec (N, E), nsub)  = I.Dec (N, normalizeNExp (E, nsub))
(* assign (G, Us1, U2, nsub_goal, asub, csub, cnstr) = cnstr
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

let rec assign (nvaronly, Glocal_u1, Us1, U2, nsub_goal, asub, csub, cnstr)  = ( let depth = I.ctxLength Glocal_u1 in let rec assignHead (nvaronly, depth, Glocal_u1, Us1, U2, cnstr)  = (match (H1, H2) with (I.Const (c1), I.Const (c2)) -> if (c1 = c2) then assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr) else raise (Assignment "Constant clash") | (I.Skonst (c1), I.Skonst (c2)) -> if (c1 = c2) then assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr) else raise (Assignment "Skolem constant clash") | (I.Def d1, _) -> assignExp (nvaronly, depth, Glocal_u1, Whnf.expandDef Us1, U2, cnstr) | (I.FgnConst (cs1, I.ConDec (n1, _, _, _, _, _)), I.FgnConst (cs2, I.ConDec (n2, _, _, _, _, _))) -> (* we require unique string representation of external constants *)
if (cs1 = cs2) && (n1 = n2) then cnstr else raise (Assignment "Foreign Constant clash") | (I.FgnConst (cs1, I.ConDef (n1, _, _, W1, _, _, _)), I.FgnConst (cs2, I.ConDef (n2, _, _, V, W2, _, _))) -> (if (cs1 = cs2) && (n1 = n2) then cnstr else assignExp (nvaronly, depth, Glocal_u1, (W1, s1), W2, cnstr)) | (I.FgnConst (_, I.ConDef (_, _, _, W1, _, _, _)), _) -> assignExp (nvaronly, depth, Glocal_u1, (W1, s1), U2, cnstr) | (_, I.FgnConst (_, I.ConDef (_, _, _, W2, _, _, _))) -> assignExp (nvaronly, depth, Glocal_u1, Us1, W2, cnstr) | (_, _) -> (raise (Assignment ("Head mismatch "))))
and assignExpW = function (nvaronly, depth, Glocal_u1, (I.Uni L1, s1), I.Uni L2, cnstr) -> cnstr | (nvaronly, depth, Glocal_u1, Us1, I.NVar n, cnstr) -> (S.insert nsub_goal (n, (Glocal_u1, (nvaronly, I.EClo (Us1)))); cnstr) | (Body, depth, Glocal_u1, Us1, U2, cnstr) -> (match H2 with I.BVar (k2) -> if (k2 > depth) then (* BVar(k2) stands for_sml an existential variable *)
(* S2 is an etaSpine by invariant *)
(S.insert asub ((k2 - I.ctxLength (Glocal_u1)), Assign (Glocal_u1, I.EClo (Us1))); cnstr) else (match H1 with I.BVar (k1) -> if (k1 = k2) then assignSpine (Body, depth, Glocal_u1, (S1, s1), S2, cnstr) else raise (Assignment "Bound variable clash") | _ -> raise (Assignment "Head mismatch")) | _ -> assignHead (Body, depth, Glocal_u1, Us1, U2, cnstr)) | (TypeLabel, depth, Glocal_u1, Us1, U2, cnstr) -> (match H2 with I.BVar (k2) -> if (k2 > depth) then (* BVar(k2) stands for_sml an existential variable *)
(* then by invariant, it must have been already instantiated *)
cnstr else (match H1 with I.BVar (k1) -> if (k1 = k2) then assignSpine (TypeLabel, depth, Glocal_u1, (S1, s1), S2, cnstr) else raise (Assignment "Bound variable clash") | _ -> raise (Assignment "Head mismatch")) | _ -> assignHead (TypeLabel, depth, Glocal_u1, Us1, U2, cnstr)) | (nvaronly, depth, Glocal_u1, Us1, U2, cnstr) -> if (k2 > depth) then (* BVar(k2) stands for_sml an existential variable *)
(* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *)
(* Glocal_u1 |- Us1 *)
(match nvaronly with TypeLabel -> cnstr | Body -> (S.insert asub ((k2 - depth), Assign (Glocal_u1, I.EClo (Us1))); cnstr)) else (match nvaronly with TypeLabel -> cnstr | Body -> (match Us1 with (I.EVar (r, _, V, Cnstr), s) -> ( let U2' = normalizeNExp (U2, csub) in  (Eqn (Glocal_u1, I.EClo (Us1), U2') :: cnstr) ) | (I.EClo (U, s'), s) -> assignExp (Body, depth, Glocal_u1, (U, I.comp (s', s)), U2, cnstr) | (I.FgnExp (_, ops), _) -> ( let U2' = normalizeNExp (U2, csub) in  (Eqn (Glocal_u1, I.EClo (Us1), U2') :: cnstr) ))) | (nvaronly, depth, Glocal_u1, (I.Lam (D1, U1), s1), I.Lam (D2, U2), cnstr) -> ( (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
             *)
let cnstr' = assignExp (TypeLabel, depth, Glocal_u1, (A1, s1), A2, cnstr) in  assignExp (nvaronly, depth + 1, I.Decl (Glocal_u1, I.decSub (D1, s1)), (U1, I.dot1 s1), U2, cnstr') ) | (nvaronly, depth, Glocal_u1, (I.Pi ((D1, _), U1), s1), I.Pi ((D2, _), U2), cnstr) -> ( (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
            *)
let cnstr' = assignExp (TypeLabel, depth, Glocal_u1, (A1, s1), A2, cnstr) in  assignExp (nvaronly, depth + 1, I.Decl (Glocal_u1, I.decSub (D1, s1)), (U1, I.dot1 s1), U2, cnstr') ) | (nvaronly, depth, Glocal_u1, Us1, U2, cnstr) -> ( let U2' = normalizeNExp (U2, csub) in  (Eqn (Glocal_u1, I.EClo (Us1), U2') :: cnstr) ) | (nvaronly, depth, Glocal_u1, Us1, U2, cnstr) -> assignExp (nvaronly, depth, Glocal_u1, (U, I.comp (s', s)), U2, cnstr) | (nvaronly, depth, Glocal_u1, Us1, U2, cnstr) -> ( let U2' = normalizeNExp (U2, csub) in  (Eqn (Glocal_u1, I.EClo (Us1), U2') :: cnstr) ) | (nvaronly, depth, Glocal_u1, Us1, U2, cnstr) -> (Eqn (Glocal_u1, I.EClo (Us1), U2) :: cnstr)
and assignSpine = function (nvaronly, depth, Glocal_u1, (I.Nil, _), I.Nil, cnstr) -> cnstr | (nvaronly, depth, Glocal_u1, (I.SClo (S1, s1'), s1), S, cnstr) -> assignSpine (nvaronly, depth, Glocal_u1, (S1, I.comp (s1', s1)), S, cnstr) | (nvaronly, depth, Glocal_u1, (I.App (U1, S1), s1), I.App (U2, S2), cnstr) -> ( (* nsub_goal, asub may be destructively updated *)
let cnstr' = assignExp (nvaronly, depth, Glocal_u1, (U1, s1), U2, cnstr) in  assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr') )
and assignExp (nvaronly, depth, Glocal_u1, Us1, U2, cnstr)  = assignExpW (nvaronly, depth, Glocal_u1, Whnf.whnf Us1, U2, cnstr) in  assignExp (nvaronly, depth, Glocal_u1, Us1, U2, cnstr) )
(* assignable (g, nsub, nsub_goal, asub, csub, cnstr) = (nsub_goal', csub, cnstr') option

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

let rec assignableLazy (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr)  = ( let nsub_query' = querySubId () in let cref = ref cnstr in let rec assign' (nsub_query, nsub)  = ( let (nsub_query_left, nsub_left1) = S.differenceModulo nsub_query nsub (fun (Glocal_u, (l, U)) -> fun (l', T) -> cref := assign (l(* = l' *)
, Glocal_u, (U, I.id), T, nsub_query', assignSub, cnstrSub, ! cref)) in let nsub_left' = S.update nsub_left1 (fun (l, U) -> (l, normalizeNExp (U, cnstrSub))) in  (Some (S.union nsub_query_left nsub_query', (S.union nsub_left nsub_left', cnstrSub), ! cref)) ) in  try assign' (nsub_query, nsub) with Assignment msg -> None )
let rec assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr)  = ( let nsub_query' = querySubId () in let cref = ref cnstr in let rec assign' (nsub_query, nsub)  = ( (* normalize nsub_left (or require that it is normalized
             collect all left-over nsubs and later combine it with cnstrsub
           *)
let (nsub_query_left, nsub_left) = S.differenceModulo nsub_query nsub (fun (Glocal_u, (l, U)) -> fun (l', T) -> cref := assign (l'(* = l *)
, Glocal_u, (U, I.id), T, nsub_query', assignSub, cnstrSub, ! cref)) in let _ = S.forall nsub_left (fun (nv, (nvaronly, U)) -> match (S.lookup cnstrSub nv) with None -> raise (Error "Left-over nsubstitution") | Some (I.AVar A) -> A := Some (normalizeNExp (U, cnstrSub))) in  (* cnstr[rsub] *)
(* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *)
(Some (S.union nsub_query_left nsub_query', cnstrSub, ! cref)) ) in  try assign' (nsub_query, nsub) with Assignment msg -> None )
(* Unification *)

let rec unifyW = function (G, (X, I.Shift 0), Us2) -> (r := Some (I.EClo (Us2))) | (G, (X, s), Us2) -> (print "unifyW -- not s = Id\n"; print ("Us2 = " ^ Print.expToString (G, I.EClo (Us2)) ^ "\n"); r := Some (I.EClo (Us2))) | (G, Xs1, Us2) -> Unify.unifyW (G, Xs1, Us2)
let rec unify (G, Xs1, Us2)  = unifyW (G, Whnf.whnf Xs1, Whnf.whnf Us2)
let rec unifiable (G, Us1, Us2)  = try (unify (G, Us1, Us2); true) with Unify.Unify msg -> false
(* Convert context G into explicit substitution *)

(* ctxToEVarSub (i, G, G', asub, s) = s' *)

let rec ctxToExplicitSub = function (i, Gquery, I.Null, asub) -> I.id | (i, Gquery, I.Decl (Gclause, I.Dec (_, A)), asub) -> ( let s = ctxToExplicitSub (i + 1, Gquery, Gclause, asub) in let (U') = I.newEVar (Gquery, I.EClo (A, s)) in  match S.lookup asub i with None -> () | Some (Assign (Glocal_u, U)) -> X' := Some (raiseType (Glocal_u, U)); I.Dot (I.Exp (U'), s) ) | (i, Gquery, I.Decl (Gclause, I.ADec (_, d)), asub) -> ( let (U') = I.newAVar () in  (match S.lookup asub i with None -> () | Some (Assign (Glocal_u, U)) -> X' := Some (U)); I.Dot (I.Exp (I.EClo (U', I.Shift (~ d))), ctxToExplicitSub (i + 1, Gquery, Gclause, asub))(* d = I.ctxLength Glocal_u *)
 )
let rec solveAuxG = function (C.Trivial, s, Gquery) -> true | (C.UnifyEq (Glocal, e1, N, eqns), s, Gquery) -> ( let G = compose' (Glocal, Gquery) in let s' = shift (Glocal, s) in  if unifiable (G, (N, s'), (e1, s')) then solveAuxG (eqns, s, Gquery) else false )
let rec solveCnstr = function (Gquery, Gclause, [], s) -> true | (Gquery, Gclause, Eqn (Glocal, U1, U2) :: Cnstr, s) -> (Unify.unifiable (compose' (Gquery, Glocal), (U1, I.id), (U2, shift (Glocal, s))) && solveCnstr (Gquery, Gclause, Cnstr, s))
let rec solveResiduals (Gquery, Gclause, CGoals (AuxG, cid, ConjGoals, i), asub, cnstr', sc)  = ( let s = ctxToExplicitSub (1, Gquery, Gclause, asub) in let success = solveAuxG (AuxG, s, Gquery) && solveCnstr (Gquery, Gclause, cnstr', s) in  if success then (sc ((ConjGoals, s), cid(* B *)
)) else () )
let rec ithChild (CGoals (_, _, _, i), n)  = (i = n)
let rec retrieveChild (num, Child, nsub_query, assignSub, cnstr, Gquery, sc)  = ( let rec retrieve = function (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub, cnstrSub, cnstr) -> (match assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr)(* destructively updates assignSub, might initiate backtracking  *)
 with None -> () | Some (nsub_query', cnstrSub', cnstr') -> (if (isId nsub_query')(* cnstrSub' = empty? by invariant *)
 then (* LCO optimization *)
if ithChild (Residuals, ! num) then solveResiduals (Gquery, Gclause, Residuals, assignSub, cnstr', sc) else CSManager.trail (fun () -> solveResiduals (Gquery, Gclause, Residuals, assignSub, cnstr', sc)) else raise (Error "Left-over normal substitutions!"))) | (Node (nsub, Children), nsub_query, assignSub, cnstrSub, cnstr) -> (match assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr)(* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
(* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
 with None -> () | Some (nsub_query', cnstrSub', cnstr') -> (S.forall Children (fun (n, Child) -> retrieve (Child, nsub_query', S.copy assignSub, S.copy cnstrSub', cnstr')))) in  retrieve (Child, nsub_query, assignSub, cnstrSubId (), cnstr) )
let rec retrieval (n, STree, G, r, sc)  = (* s = id *)
 ( let (nsub_query, assignSub) = (querySubId (), assignSubId ()) in  S.insert nsub_query (1, (I.Null, (Body, r))); S.forall Children (fun (_, C) -> retrieveChild (n, C, nsub_query, assignSub, [], G, sc)) )
(*----------------------------------------------------------------------------*)

(* Retrieval via set of candidates *)

let rec retrieveAll (num, Child, nsub_query, assignSub, cnstr, candSet)  = ( let i = ref 0 in let rec retrieve = function (Leaf (nsub, Gclause, Residuals), nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) -> (match assignableLazy (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr)(* destructively updates assignSub, might initiate backtracking  *)
 with None -> () | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') -> (if (isId nsub_query') then (* LCO optimization *)
(i := ! i + 1; S.insert candSet (! i, (assignSub, nsub_left', cnstrSub', cnstr', Gclause, Residuals)); ()) else raise (Error "Left-over normal substitutions!"))) | (Node (nsub, Children), nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) -> (match assignableLazy (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr)(* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
(* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
 with None -> () | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') -> (S.forall Children (fun (n, Child) -> retrieve (Child, nsub_query', S.copy assignSub, (S.copy nsub_left', S.copy cnstrSub'), cnstr')))) in  retrieve (Child, nsub_query, assignSub, (nid (), cnstrSubId ()), cnstr) )
let rec retrieveCandidates (n, STree, Gquery, r, sc)  = (* s = id *)
 ( let (nsub_query, assignSub) = (querySubId (), assignSubId ()) in let candSet = S.new_ () in let rec solveCandidate (i, candSet)  = match (S.lookup candSet i) with None -> ((* print "No candidate left anymore\n" ;*)
()) | Some (assignSub, nsub_left, cnstrSub, cnstr, Gclause, Residuals(* CGoals(AuxG, cid, ConjGoals, i) *)
) -> (CSManager.trail (fun () -> (S.forall nsub_left (fun (nv, (l, U)) -> match (S.lookup cnstrSub nv) with None -> raise (Error "Left-over nsubstitution") | Some (I.AVar A) -> A := Some (U)); solveResiduals (Gquery, Gclause, Residuals, assignSub, cnstr, sc))); solveCandidate (i + 1, candSet(* sc = (fn S => (O::S)) *)
)) in  S.insert nsub_query (1, (I.Null, (Body, r))); S.forall Children (fun (_, C) -> retrieveAll (n, C, nsub_query, assignSub, [], candSet)); (* execute one by one all candidates : here ! *)
solveCandidate (1, candSet) )
let rec matchSig (a, G, ps, sc)  = ( let (n, Tree) = Array.sub (indexArray, a) in  (* retrieval (n, !Tree, G, I.EClo(ps), sc)   *)
retrieveCandidates (n, ! Tree, G, I.EClo (ps), sc) )
let rec matchSigIt (a, G, ps, sc)  = ( let (n, Tree) = Array.sub (indexArray, a) in  retrieval (n, ! Tree, G, I.EClo (ps), sc) )
let rec sProgReset ()  = (nctr := 1; Array.modify (fun (n, Tree) -> (n := 0; Tree := ! (makeTree ()); (n, Tree))) indexArray)
let rec sProgInstall (a, C.Head (E, G, Eqs, cid), R)  = ( let (n, Tree) = Array.sub (indexArray, a) in let nsub_goal = S.new_ () in  S.insert nsub_goal (1, (Body, E)); Tree := insert (! Tree, nsub_goal, (G, CGoals (Eqs, cid, R, ! n + 1))); n := ! n + 1 )
let sProgReset = sProgReset
let sProgInstall = sProgInstall
let matchSig = matchSigIt
(* local *)

 end


(* functor SubTree *)

