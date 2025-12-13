(* Substitution Tree indexing *)
(* Author: Brigitte Pientka *)
functor (* GEN BEGIN FUNCTOR DECL *) SubTree ((*! structure IntSyn' : INTSYN !*)
                 (*!structure CompSyn' : COMPSYN !*)
                 (*!  sharing CompSyn'.IntSyn = IntSyn' !*)
                 structure Whnf : WHNF
                 (*!  sharing Whnf.IntSyn = IntSyn' !*)
                 structure Unify : UNIFY
                 (*!  sharing Unify.IntSyn = IntSyn'!*)
                 structure Print : PRINT
                 (*!  sharing Print.IntSyn = IntSyn' !*)
                    (* CPrint currently unused *)
                 structure CPrint : CPRINT
                 (*!  sharing CPrint.IntSyn = IntSyn' !*)
                 (*!  sharing CPrint.CompSyn = CompSyn' !*)
                     (* unused *)
                structure Formatter : FORMATTER
                (*!  sharing Print.Formatter = Formatter !*)
                     (* unused *)
                structure Names: NAMES
                (*!  sharing Names.IntSyn = IntSyn' !*)
                structure CSManager : CS_MANAGER
                 (*!  sharing CSManager.IntSyn = IntSyn'!*)
                 (*! structure RBSet : RBSET !*))
  : SUBTREE =
struct
(*!  structure IntSyn = IntSyn' !*)
(*!  structure CompSyn = CompSyn' !*)
(*!  structure RBSet = RBSet !*)

  type nvar = int      (* index for normal variables *)
  type bvar = int      (* index for bound variables *)
  type bdepth = int    (* depth of locally bound variables *)

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
  datatype type_label = TypeLabel | Body

  type normal_substs =  (type_label * IntSyn.exp) RBSet.ord_set  (* key = int = bvar *)

  datatype ass_sub = Assign of (IntSyn.dec IntSyn.ctx * IntSyn.exp)
  type ass_substs = ass_sub RBSet.ord_set          (* key = int = bvar *)

  type query_substs = (IntSyn.dec IntSyn.ctx * (type_label * IntSyn.exp)) RBSet.ord_set

  datatype cnstr = Eqn of IntSyn.dec IntSyn.ctx * IntSyn.exp * IntSyn.exp
  type cnstr_substs = IntSyn.exp RBSet.ord_set    (* key = int = bvar *)

  datatype c_goal = CGoals of CompSyn.aux_goal * IntSyn.cid * CompSyn.conjunction * int (* cid of clause *)

  datatype gen_type  = Top | Regular

  datatype tree =
    Leaf of normal_substs  * IntSyn.dec IntSyn.ctx * c_goal
  | Node of normal_substs  * tree RBSet.ord_set

   type candidate = (ass_substs * normal_substs * cnstr_substs * cnstr * IntSyn.dec IntSyn.ctx * c_goal)

   (* Initialization of substitutions *)
   (* GEN BEGIN TAG OUTSIDE LET *) val nid         : unit -> normal_substs = RBSet.new (* GEN END TAG OUTSIDE LET *)
   (* GEN BEGIN TAG OUTSIDE LET *) val assignSubId : unit -> ass_substs = RBSet.new (* GEN END TAG OUTSIDE LET *)
   (* GEN BEGIN TAG OUTSIDE LET *) val cnstrSubId  : unit -> cnstr_substs = RBSet.new (* GEN END TAG OUTSIDE LET *)
   (* GEN BEGIN TAG OUTSIDE LET *) val querySubId  : unit -> query_substs = RBSet.new (* GEN END TAG OUTSIDE LET *)

   (* Identity substitution *)
   fun isId s = RBSet.isEmpty s

   (* Initialize substitution tree *)
   fun makeTree () = ref (Node (nid (), RBSet.new()))

   (* Test if node has any children *)
   fun noChildren C = RBSet.isEmpty C


  (* Index array

   Invariant:
   For all type families  a  indexArray = [a1,...,an]
   where a1,...,an is a substitution tree consisting of all constants
   for target family ai

   *)
  (* GEN BEGIN TAG OUTSIDE LET *) val indexArray = Array.tabulate (Global.maxCid, ((* GEN BEGIN FUNCTION EXPRESSION *) fn i => (ref 0, makeTree ()) (* GEN END FUNCTION EXPRESSION *))) (* GEN END TAG OUTSIDE LET *);

  local

    structure I = IntSyn
    structure C = CompSyn
    structure S = RBSet

    exception Error of string

    exception Assignment of string

    exception Generalization of string

    (* Auxiliary functions *)
    fun (* GEN BEGIN FUN FIRST *) cidFromHead (I.Const c) = c (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) cidFromHead (I.Def c) = c (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) dotn (0, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) dotn (i, s) = dotn (i-1, I.dot1 s) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) compose'(IntSyn.Null, G) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) compose'(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose'(G, G'), D) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) shift (IntSyn.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) raiseType (I.Null, V) = V (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) raiseType (I.Decl (G, D), V) = raiseType (G, I.Lam (D, V)) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) printSub (IntSyn.Shift n) = print ("Shift " ^ Int.toString n ^ "\n") (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot(IntSyn.Idx n, s)) = (print ("Idx " ^ Int.toString n ^ " . "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(IntSyn.EVar (_, _, _, _)), s)) = (print ("Exp (EVar _ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(IntSyn.AVar (_)), s)) = (print ("Exp (AVar _ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(IntSyn.EClo (IntSyn.AVar (_), _)), s)) = (print ("Exp (AVar _ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(IntSyn.EClo (_, _)), s)) = (print ("Exp (EClo _ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(_), s)) = (print ("Exp (_ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Undef, s)) = (print ("Undef . "); printSub s) (* GEN END FUN BRANCH *)

   (*
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
   (* GEN BEGIN TAG OUTSIDE LET *) val nctr = ref 1 (* GEN END TAG OUTSIDE LET *)

   fun newNVar () =
     (nctr := !nctr + 1;
      I.NVar(!nctr))



   fun (* GEN BEGIN FUN FIRST *) eqHeads (I.Const k, I.Const k') =  (k = k') (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) eqHeads (I.BVar k, I.BVar k') =  (k  = k') (* GEN END FUN BRANCH *)
     | (* GEN BEGIN FUN BRANCH *) eqHeads (I.Def k, I.Def k') = (k = k') (* GEN END FUN BRANCH *)
     | (* GEN BEGIN FUN BRANCH *) eqHeads ( _, _) = false (* GEN END FUN BRANCH *)

   (* most specific linear common generalization *)

   (* compatible (T, U) = (C, rho_u', rho_t') opt
    if
       U, T are both in normal form
       U and T share at least the top function symbol
   then
     C[rho_u'] = U and C[rho_t'] = T
   *)
   fun compatible (label, T, U, rho_t, rho_u) =
     let
       fun (* GEN BEGIN FUN FIRST *) genExp (label, b, T as I.NVar n, U as I.Root(H, S)) =
           (S.insert rho_u (n, (label, U)); T) (* GEN END FUN FIRST *)
         | (* GEN BEGIN FUN BRANCH *) genExp (label, b, T as I.Root(H1, S1), U as I.Root(H2, S2)) =
           if eqHeads(H1, H2)
             then
               I.Root(H1, genSpine(label, b, S1, S2))
           else
             (case b
                of Regular => (S.insert rho_t (!nctr+1,  (label, T));
                               S.insert rho_u (!nctr+1, (label, U));
                               newNVar())
                 | _ => raise Generalization "Should never happen!" ) (* GEN END FUN BRANCH *)
                         (* = S.existsOpt (fn U' => equalTerm (U, U')) *)
            (* find *i in rho_t and rho_u such that T/*i in rho_t and U/*i in rho_u *)
         | (* GEN BEGIN FUN BRANCH *) genExp (label, b, I.Lam(D1 as I.Dec(N,A1), T1), I.Lam(D2 as I.Dec(_, A2), U2)) =
           (* NOTE: by invariant A1 =/= A2 *)
             I.Lam(I.Dec(N, genExp (TypeLabel, Regular, A1, A2)), genExp (label, b, T1,  U2)) (* GEN END FUN BRANCH *)
   
         | (* GEN BEGIN FUN BRANCH *) genExp (label, b, I.Pi(DD1 as (D1,I.No), E1), I.Pi(DD2 as (D2, I.No), E2)) =
             I.Pi((genDec(TypeLabel, Regular, D1, D2), I.No), genExp(label, b, E1, E2)) (* GEN END FUN BRANCH *)
   
         | (* GEN BEGIN FUN BRANCH *) genExp (label, b, I.Pi(DD1 as (D1,I.Maybe), E1), I.Pi(DD2 as (D2, I.Maybe), E2)) =
             I.Pi((genDec(TypeLabel, Regular, D1, D2), I.Maybe), genExp(label, b, E1, E2)) (* GEN END FUN BRANCH *)
   
         | (* GEN BEGIN FUN BRANCH *) genExp (label, b, I.Pi(DD1 as (D1,I.Meta), E1), I.Pi(DD2 as (D2, I.Meta), E2)) =
             I.Pi((genDec(TypeLabel, Regular, D1, D2), I.Meta), genExp(label, b, E1, E2)) (* GEN END FUN BRANCH *)
         | (* GEN BEGIN FUN BRANCH *) genExp (label, b, T, U) =
             raise Generalization "Cases where U= EVar or EClo should never happen!" (* GEN END FUN BRANCH *)
   
       and (* GEN BEGIN FUN FIRST *) genSpine (label, b, I.Nil, I.Nil) = I.Nil (* GEN END FUN FIRST *)
         | (* GEN BEGIN FUN BRANCH *) genSpine (label, b, I.App(T, S1), I.App(U, S2)) =
         I.App(genExp (label, b, T, U), genSpine (label, b, S1, S2)) (* GEN END FUN BRANCH *)
   
       and genDec (label, b, I.Dec(N, E1), I.Dec(N', E2)) =
                   I.Dec(N, genExp(label, b, E1, E2))
   
       fun (* GEN BEGIN FUN FIRST *) genTop (label, T as I.Root(H1, S1), U as I.Root(H2, S2)) =
         if eqHeads(H1, H2)
           then I.Root(H1, genSpine(label, Regular, S1, S2))
         else
           raise Generalization "Top-level function symbol not shared" (* GEN END FUN FIRST *)
         | (* GEN BEGIN FUN BRANCH *) genTop (label, I.Lam(D1 as I.Dec(N,A1), T1), I.Lam(D2 as I.Dec(_, A2), U2)) =
           (* by invariant A1 =/= A2 *)
             I.Lam(I.Dec(N, genExp (label, Regular, A1, A2)), genTop (label, T1,  U2)) (* GEN END FUN BRANCH *)
         | (* GEN BEGIN FUN BRANCH *) genTop (_, _, _) = raise Generalization "Top-level function symbol not shared" (* GEN END FUN BRANCH *)
    in
      SOME(genTop (label, T, U))
      handle Generalization msg => NONE
    end

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
  fun compatibleSub (nsub_t, nsub_e) =
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val (sg, rho_t, rho_e) = (nid(), nid (), nid ()) (* GEN END TAG OUTSIDE LET *)
     (* by invariant rho_t = empty, since nsub_t <= nsub_e *)
      (* GEN BEGIN TAG OUTSIDE LET *) val _ =  S.forall nsub_e
        ((* GEN BEGIN FUNCTION EXPRESSION *) fn (nv, (l',E)) =>
         (case (S.lookup nsub_t nv)
            of SOME (l,T) =>     (* by invariant d = d'
                                     therefore T and E have the same approximate type A *)
              (if l = l' then
                 (case compatible (l, T, E, rho_t, rho_e)
                 of NONE => (S.insert rho_t (nv, (l,  T));
                             S.insert rho_e (nv, (l, E)))
               | SOME(T') => S.insert sg (nv, (l,  T')))
               else raise Generalization "Labels don't agree\n")
          | NONE => S.insert rho_e (nv, (l', E))) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    in
      if isId(sg)
        then NONE
      else
         SOME(sg, rho_t, rho_e)
    end

  (* mkNode (N, sg, r1, (G, RC), r2) = N'    *)
  fun (* GEN BEGIN FUN FIRST *) mkNode (Node(_, Children), sg, rho1, GR as (G, RC), rho2) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val c = S.new() (* GEN END TAG OUTSIDE LET *)
      in
        S.insertList c [(1, Node(rho1, Children)),
                                (2, Leaf(rho2, G, RC))];
       Node(sg, c)
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) mkNode (Leaf(_, G1, RC1), sg, rho1, GR as (G2, RC2), rho2) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val c = S.new() (* GEN END TAG OUTSIDE LET *)
      in
        S.insertList c [(1, Leaf(rho1, G1, RC1)),
                        (2, Leaf(rho2, G2, RC2))];
        Node(sg, c)
      end (* GEN END FUN BRANCH *)


  (* Insertion *)
  (* compareChild (children, (n, child), n, n', (G, R)) = ()

   *)
  fun compareChild (children, (n, child), nsub_t, nsub_e, GR as (G_clause2, Res_clause2)) =
    (case compatibleSub (nsub_t, nsub_e) of
       NONE => (S.insert children (n+1, Leaf(nsub_e, G_clause2, Res_clause2)))
     | SOME(sg, rho1, rho2) =>
         (if isId rho1 then
           if isId rho2
             then (* sg = nsub_t = nsub_e *)
               (S.insertShadow children (n, mkNode(child, sg, rho1, GR, rho2)))
           else
             (* sg = nsub_t and nsub_e = sg o rho2 *)
             (S.insertShadow children (n, insert (child, rho2, GR)))
         else
           (S.insertShadow children (n, mkNode(child, sg, rho1, GR, rho2)))))

  (* insert (N, nsub_e, (G, R2)) = N'

     if s is the substitution in node N
        G |- nsub_e : S and
    G, S' |- s : S
    then
     N' contains a path n_1 .... n_n s.t.
     [n_n] ...[n_1] s = nsub_e
  *)
  and (* GEN BEGIN FUN FIRST *) insert (N as Leaf (nsub_t, G_clause1, R1), nsub_e, GR as (G_clause2, R2)) =
    (case compatibleSub(nsub_t, nsub_e) of
       NONE => raise Error "Leaf is not compatible substitution r"
     | SOME(sg, rho1, rho2) => mkNode (N, sg, rho1, GR, rho2)) (* GEN END FUN FIRST *)

    | (* GEN BEGIN FUN BRANCH *) insert (N as Node(_, children), nsub_e, GR as (G_clause2, RC)) =
       if noChildren children
         then
           (* initial *)
           (S.insert children (1, (Leaf (nsub_e, G_clause2, RC))); N)
       else
         (case (S.last children)
            of (n, child as Node(nsub_t, children')) =>
              (compareChild (children, (n, child), nsub_t, nsub_e, GR); N)
          | (n, child as Leaf(nsub_t, G1, RC1)) =>
              (compareChild (children, (n, child), nsub_t,  nsub_e, GR); N)) (* GEN END FUN BRANCH *)


  (* retrieval (U,s)
     retrieves all clauses which unify with (U,s)

     backtracking implemented via SML failure continuation

   *)
  fun (* GEN BEGIN FUN FIRST *) normalizeNExp (I.NVar n, csub) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val A = I.newAVar () (* GEN END TAG OUTSIDE LET *)
      in
        S.insert csub (n, A);
        A
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) normalizeNExp (I.Root (H, S), nsub) =
         I.Root(H, normalizeNSpine (S, nsub)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) normalizeNExp (I.Lam (D, U), nsub) =
         I.Lam (normalizeNDec(D, nsub), normalizeNExp (U, nsub)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) normalizeNExp (I.Pi((D, P), U), nsub) =
         (* cannot happen -bp *)
         I.Pi ((normalizeNDec(D, nsub), P), normalizeNExp (U, nsub)) (* GEN END FUN BRANCH *)

  and (* GEN BEGIN FUN FIRST *) normalizeNSpine (I.Nil, _) = I.Nil (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) normalizeNSpine (I.App (U, S), nsub) =
    I.App(normalizeNExp (U, nsub), normalizeNSpine (S, nsub)) (* GEN END FUN BRANCH *)

  and normalizeNDec (I.Dec(N, E), nsub) = I.Dec(N, normalizeNExp(E, nsub))

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

  fun assign (nvaronly, Glocal_u1, Us1, U2, nsub_goal, asub, csub, cnstr) =
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val depth = I.ctxLength Glocal_u1 (* GEN END TAG OUTSIDE LET *)
      fun assignHead (nvaronly, depth, Glocal_u1, Us1 as (I.Root (H1, S1), s1), U2 as I.Root (H2, S2), cnstr) =
          (case (H1, H2)
             of (I.Const(c1), I.Const(c2)) =>
                if (c1 = c2)
                  then assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr)
                else raise Assignment "Constant clash"
             | (I.Skonst(c1), I.Skonst(c2)) =>
               if (c1 = c2)
                 then assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr)
               else raise Assignment "Skolem constant clash"
             | (I.Def d1, _) => assignExp (nvaronly, depth, Glocal_u1, Whnf.expandDef Us1, U2, cnstr)
             | (I.FgnConst (cs1, I.ConDec (n1, _, _, _, _, _)), I.FgnConst (cs2, I.ConDec (n2, _, _, _, _, _))) =>
               (* we require unique string representation of external constants *)
               if (cs1 = cs2) andalso (n1 = n2) then cnstr
               else raise Assignment "Foreign Constant clash"
             | (I.FgnConst (cs1, I.ConDef (n1, _, _, W1, _, _,_)), I.FgnConst (cs2, I.ConDef (n2, _, _, V, W2, _,_))) =>
               (if (cs1 = cs2) andalso (n1 = n2) then cnstr
                else assignExp (nvaronly, depth, Glocal_u1, (W1, s1), W2, cnstr))
             | (I.FgnConst (_, I.ConDef (_, _, _, W1, _, _,_)), _) => assignExp (nvaronly, depth, Glocal_u1, (W1, s1), U2, cnstr)
             | (_, I.FgnConst (_, I.ConDef (_, _, _, W2, _, _,_))) => assignExp (nvaronly, depth, Glocal_u1, Us1, W2, cnstr)
             | (_, _) => (raise Assignment ("Head mismatch ")))
  
      and (* GEN BEGIN FUN FIRST *) assignExpW (nvaronly, depth, Glocal_u1, (I.Uni L1, s1), I.Uni L2, cnstr) = cnstr (* GEN END FUN FIRST *) (* L1 = L2 by invariant *)
        | (* GEN BEGIN FUN BRANCH *) assignExpW (nvaronly, depth, Glocal_u1, Us1, I.NVar n, cnstr) =
          (S.insert nsub_goal (n, (Glocal_u1, (nvaronly, I.EClo(Us1))));
           cnstr) (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) assignExpW (Body, depth, Glocal_u1, Us1 as (I.Root (H1, S1), s1), U2 as I.Root (H2, S2), cnstr) =
          (case H2
             of I.BVar(k2) =>
               if (k2 > depth)
                 then
                   (* BVar(k2) stands for an existential variable *)
                   (* S2 is an etaSpine by invariant *)
                    (S.insert asub ((k2 - I.ctxLength(Glocal_u1)), Assign(Glocal_u1, I.EClo(Us1)));
                     cnstr)
               else
                 (case H1
                    of I.BVar(k1) => if (k1 = k2)
                                       then assignSpine (Body, depth, Glocal_u1, (S1, s1), S2, cnstr)
                                     else raise Assignment "Bound variable clash"
                  | _ => raise Assignment "Head mismatch")
           | _ => assignHead (Body, depth, Glocal_u1, Us1, U2, cnstr)) (* GEN END FUN BRANCH *)
  
        | (* GEN BEGIN FUN BRANCH *) assignExpW (TypeLabel, depth, Glocal_u1, Us1 as (I.Root (H1, S1), s1), U2 as I.Root (H2, S2), cnstr) =
          (case H2
             of I.BVar(k2) =>
               if (k2 > depth)
                 then
                   (* BVar(k2) stands for an existential variable *)
                   (* then by invariant, it must have been already instantiated *)
                    cnstr
               else
                 (case H1
                    of I.BVar(k1) => if (k1 = k2)
                                       then assignSpine (TypeLabel, depth, Glocal_u1, (S1, s1), S2, cnstr)
                                     else raise Assignment "Bound variable clash"
                  | _ => raise Assignment "Head mismatch")
           | _ => assignHead (TypeLabel, depth, Glocal_u1, Us1, U2, cnstr)) (* GEN END FUN BRANCH *)
            (* here spine associated with k2 might not be Nil ? *)
        | (* GEN BEGIN FUN BRANCH *) assignExpW (nvaronly, depth, Glocal_u1, Us1, U2 as I.Root(I.BVar k2, S), cnstr) =
           if (k2 > depth)
             then
               (* BVar(k2) stands for an existential variable *)
               (* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *)
               (* Glocal_u1 |- Us1 *)
               (case nvaronly
                  of TypeLabel => cnstr
                   | Body => (S.insert asub ((k2 - depth), Assign(Glocal_u1, I.EClo(Us1)));
                             cnstr))
           else
             (case nvaronly
                of TypeLabel => cnstr
                | Body =>
                  (case Us1
                     of (I.EVar(r, _, V, Cnstr), s) =>
                       let
                         (* GEN BEGIN TAG OUTSIDE LET *) val U2' = normalizeNExp (U2, csub) (* GEN END TAG OUTSIDE LET *)
                       in
                         (Eqn(Glocal_u1, I.EClo(Us1), U2')::cnstr)
                       end
                   | (I.EClo(U,s'), s) => assignExp(Body, depth, Glocal_u1, (U, I.comp(s', s)), U2, cnstr)
                   | (I.FgnExp (_, ops), _) =>
                       let
                         (* GEN BEGIN TAG OUTSIDE LET *) val U2' = normalizeNExp (U2, csub) (* GEN END TAG OUTSIDE LET *)
                       in
                         (Eqn(Glocal_u1, I.EClo(Us1), U2')::cnstr)
                       end)) (* GEN END FUN BRANCH *)
        (* by invariant Us2 cannot contain any FgnExp *)
        | (* GEN BEGIN FUN BRANCH *) assignExpW (nvaronly, depth, Glocal_u1, (I.Lam (D1 as I.Dec(_, A1), U1), s1), I.Lam (D2 as I.Dec(_, A2), U2), cnstr) =
          (* D1[s1] = D2[s2]  by invariant *)
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val cnstr' = assignExp (TypeLabel, depth, Glocal_u1, (A1, s1), A2, cnstr) (* GEN END TAG OUTSIDE LET *)
            (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
             *)
          in
          assignExp (nvaronly, depth+1, I.Decl (Glocal_u1, I.decSub (D1, s1)), (U1, I.dot1 s1), U2, cnstr')
          end (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) assignExpW (nvaronly, depth, Glocal_u1, (I.Pi ((D1 as I.Dec(_, A1), _), U1), s1), I.Pi ((D2 as I.Dec(_, A2), _), U2), cnstr) =
          (* D1[s1] = D2[s2]  by invariant *)
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val cnstr' = assignExp (TypeLabel, depth, Glocal_u1, (A1, s1), A2, cnstr) (* GEN END TAG OUTSIDE LET *)
            (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
            *)
          in
          assignExp (nvaronly, depth+1, I.Decl (Glocal_u1, I.decSub (D1, s1)), (U1, I.dot1 s1), U2, cnstr')
          end (* GEN END FUN BRANCH *)
  
          (* it does matter what we put in Glocal_u1! since D2 will only be approximately the same as D1 at this point! *)
          (* assignExp (nvaronly, depth+1, I.Decl (Glocal_u1, D2), (U1, I.dot1 s1), U2, cnstr) *)
  
        | (* GEN BEGIN FUN BRANCH *) assignExpW (nvaronly, depth, Glocal_u1, Us1 as (I.EVar(r, _, V, Cnstr), s), U2, cnstr) =
          (* generate cnstr substitution for all nvars occurring in U2 *)
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val U2' = normalizeNExp (U2, csub) (* GEN END TAG OUTSIDE LET *)
          in
            (Eqn(Glocal_u1, I.EClo(Us1), U2')::cnstr)
          end (* GEN END FUN BRANCH *)
  
        | (* GEN BEGIN FUN BRANCH *) assignExpW (nvaronly, depth, Glocal_u1, Us1 as (I.EClo(U,s'), s), U2, cnstr) =
          assignExp(nvaronly, depth, Glocal_u1, (U, I.comp(s', s)), U2, cnstr) (* GEN END FUN BRANCH *)
  
        | (* GEN BEGIN FUN BRANCH *) assignExpW (nvaronly, depth, Glocal_u1, Us1 as (I.FgnExp (_, ops), _), U2, cnstr) =
          (* by invariant Us2 cannot contain any FgnExp *)
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val U2' = normalizeNExp (U2, csub) (* GEN END TAG OUTSIDE LET *)
          in
            (Eqn(Glocal_u1, I.EClo(Us1), U2')::cnstr)
          end (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) assignExpW (nvaronly, depth, Glocal_u1, Us1, U2 as I.FgnExp (_, ops), cnstr) =
          (Eqn(Glocal_u1, I.EClo(Us1), U2)::cnstr) (* GEN END FUN BRANCH *)
  (*      | assignExpW (nvaronly, depth, Glocal_u1, (U1, s1), I.Lam (D2, U2), cnstr) =
          (* Cannot occur if expressions are eta expanded *)
          raise Assignment "Cannot occur if expressions in clause heads are eta-expanded"*)
  (*      | assignExpW (nvaronly, depth, Glocal_u1, (I.Lam (D1, U1), s1), U2, cnstr) =
      (* ETA: can't occur if eta expanded *)
            raise Assignment "Cannot occur if expressions in query are eta-expanded"
  *)
           (* same reasoning holds as above *)
  
      and (* GEN BEGIN FUN FIRST *) assignSpine (nvaronly, depth, Glocal_u1, (I.Nil, _), I.Nil, cnstr) = cnstr (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) assignSpine (nvaronly, depth, Glocal_u1, (I.SClo (S1, s1'), s1), S, cnstr) =
        assignSpine (nvaronly, depth, Glocal_u1, (S1, I.comp (s1', s1)), S, cnstr) (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) assignSpine (nvaronly, depth, Glocal_u1, (I.App (U1, S1), s1), I.App (U2, S2), cnstr) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val cnstr' = assignExp (nvaronly, depth, Glocal_u1, (U1, s1), U2, cnstr) (* GEN END TAG OUTSIDE LET *)
        (* nsub_goal, asub may be destructively updated *)
        in
          assignSpine (nvaronly, depth, Glocal_u1, (S1, s1), S2, cnstr')
        end (* GEN END FUN BRANCH *)
  
      and assignExp (nvaronly, depth, Glocal_u1, Us1, U2, cnstr) =
          assignExpW (nvaronly, depth, Glocal_u1, Whnf.whnf Us1, U2, cnstr)
    in
      assignExp (nvaronly, depth, Glocal_u1, Us1, U2, cnstr)
    end

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
  fun assignableLazy (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) =
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val nsub_query' = querySubId () (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val cref = ref cnstr (* GEN END TAG OUTSIDE LET *)
      fun assign' (nsub_query, nsub) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (nsub_query_left, nsub_left1) = S.differenceModulo nsub_query nsub
                                ((* GEN BEGIN FUNCTION EXPRESSION *) fn (Glocal_u, (l, U)) => (* GEN BEGIN FUNCTION EXPRESSION *) fn  (l', T) =>
                                 cref := assign (l (* = l' *), Glocal_u, (U, I.id), T, nsub_query', assignSub, cnstrSub, !cref) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val nsub_left' = S.update nsub_left1 ((* GEN BEGIN FUNCTION EXPRESSION *) fn (l,U) => (l, normalizeNExp (U, cnstrSub)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          (SOME(S.union nsub_query_left nsub_query', (S.union nsub_left nsub_left', cnstrSub), !cref))
        end
    in
      assign' (nsub_query, nsub)
      handle Assignment msg =>  NONE
    end


  fun assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr) =
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val nsub_query' = querySubId () (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val cref = ref cnstr (* GEN END TAG OUTSIDE LET *)
      fun assign' (nsub_query, nsub) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (nsub_query_left, nsub_left) = S.differenceModulo nsub_query nsub
                                ((* GEN BEGIN FUNCTION EXPRESSION *) fn (Glocal_u, (l, U)) => (* GEN BEGIN FUNCTION EXPRESSION *) fn  (l', T) =>
                                 cref := assign (l' (* = l *), Glocal_u, (U, I.id), T, nsub_query', assignSub, cnstrSub, !cref) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
          (* normalize nsub_left (or require that it is normalized
             collect all left-over nsubs and later combine it with cnstrsub
           *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = S.forall nsub_left ((* GEN BEGIN FUNCTION EXPRESSION *) fn (nv, (nvaronly, U)) => case (S.lookup cnstrSub nv)
                                                         of NONE =>  raise Error "Left-over nsubstitution"
                                                       | SOME(I.AVar A) => A := SOME(normalizeNExp (U, cnstrSub)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in (* cnstr[rsub] *)
          (* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *)
          (SOME(S.union nsub_query_left nsub_query', cnstrSub, !cref))
        end
    in
      assign' (nsub_query, nsub)
      handle Assignment msg =>  NONE
    end

  (* Unification *)
  fun (* GEN BEGIN FUN FIRST *) unifyW (G, (X as I.AVar(r as ref NONE), I.Shift 0), Us2) =
      (r := SOME(I.EClo(Us2))) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) unifyW (G, (X as I.AVar(r as ref NONE), s), Us2 as (U, s2)) =
      (print "unifyW -- not s = Id\n";
       print ("Us2 = " ^ Print.expToString (G, I.EClo(Us2)) ^ "\n");
       r := SOME(I.EClo(Us2))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) unifyW (G, Xs1, Us2) =
    (* Xs1 should not contain any uninstantiated AVar anymore *)
      Unify.unifyW(G, Xs1, Us2) (* GEN END FUN BRANCH *)

  fun unify(G, Xs1, Us2) = unifyW(G, Whnf.whnf Xs1, Whnf.whnf Us2)

  fun unifiable (G, Us1, Us2) =
      (unify(G, Us1, Us2); true)
      handle Unify.Unify msg => false

  (* Convert context G into explicit substitution *)
  (* ctxToEVarSub (i, G, G', asub, s) = s' *)
  fun (* GEN BEGIN FUN FIRST *) ctxToExplicitSub (i, Gquery, I.Null, asub) = I.id (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) ctxToExplicitSub (i, Gquery, I.Decl(Gclause, I.Dec(_, A)), asub) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val s = ctxToExplicitSub (i+1, Gquery, Gclause, asub) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (U' as I.EVar(X',_,_, _)) = I.newEVar (Gquery, I.EClo(A, s)) (* GEN END TAG OUTSIDE LET *)
      in
        case S.lookup asub i
          of NONE => ()
        | SOME(Assign(Glocal_u, U)) =>
            X' := SOME(raiseType(Glocal_u, U));
        I.Dot(I.Exp(U'), s)
      end (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) ctxToExplicitSub (i, Gquery, I.Decl(Gclause, I.ADec(_, d)), asub) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (U' as (I.AVar X')) = I.newAVar () (* GEN END TAG OUTSIDE LET *)
      in
        (case S.lookup asub i
           of NONE => ()
         | SOME(Assign(Glocal_u, U)) =>
            X' := SOME(U));
        I.Dot(I.Exp(I.EClo(U', I.Shift(~d))), ctxToExplicitSub (i+1, Gquery, Gclause, asub))
         (* d = I.ctxLength Glocal_u *)
      end (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) solveAuxG (C.Trivial, s, Gquery) =  true (* GEN END FUN FIRST *) (* succeed *)
    | (* GEN BEGIN FUN BRANCH *) solveAuxG (C.UnifyEq(Glocal,e1, N, eqns), s, Gquery) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val G = compose' (Glocal, Gquery) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = shift (Glocal, s) (* GEN END TAG OUTSIDE LET *)
      in
        if unifiable (G, (N, s'), (e1, s'))
          then   solveAuxG (eqns, s, Gquery)
        else false
      end (* GEN END FUN BRANCH *)



  fun (* GEN BEGIN FUN FIRST *) solveCnstr (Gquery, Gclause, nil, s) = true (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) solveCnstr (Gquery, Gclause, Eqn(Glocal, U1, U2)::Cnstr, s) =
      (Unify.unifiable(compose'(Gquery, Glocal), (U1, I.id), (U2, shift(Glocal, s))) andalso
       solveCnstr (Gquery, Gclause, Cnstr, s)) (* GEN END FUN BRANCH *)


  fun solveResiduals (Gquery, Gclause, CGoals(AuxG, cid, ConjGoals, i), asub, cnstr', sc) =
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val s = ctxToExplicitSub (1, Gquery, Gclause, asub) (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val success =  solveAuxG (AuxG, s, Gquery) andalso solveCnstr (Gquery, Gclause, cnstr', s) (* GEN END TAG OUTSIDE LET *)
    in
      if success
        then
          (sc ((ConjGoals, s), cid (* B *)))
      else ()
    end


  fun ithChild (CGoals(_, _, _, i), n) = (i = n)

  fun retrieveChild (num, Child, nsub_query, assignSub, cnstr, Gquery, sc) =
    let
      fun (* GEN BEGIN FUN FIRST *) retrieve (Leaf(nsub, Gclause, Residuals), nsub_query, assignSub, cnstrSub, cnstr) =
         (case assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr)
          (* destructively updates assignSub, might initiate backtracking  *)
          of NONE => ()
          | SOME(nsub_query', cnstrSub', cnstr') =>
            (if (isId nsub_query') (* cnstrSub' = empty? by invariant *)
               then
                 (* LCO optimization *)
                 if ithChild(Residuals, !num) then
                    solveResiduals (Gquery, Gclause, Residuals, assignSub, cnstr', sc)
                 else
                   CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => solveResiduals (Gquery, Gclause, Residuals, assignSub, cnstr', sc) (* GEN END FUNCTION EXPRESSION *))
             else
              raise Error "Left-over normal substitutions!")) (* GEN END FUN FIRST *)
  
        | (* GEN BEGIN FUN BRANCH *) retrieve (Node(nsub, Children), nsub_query, assignSub, cnstrSub, cnstr) =
         (case assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr)
          (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
          (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
            of NONE => ()
             | SOME (nsub_query', cnstrSub', cnstr') =>
               (S.forall Children
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn (n, Child) => retrieve (Child, nsub_query', S.copy assignSub, S.copy cnstrSub', cnstr') (* GEN END FUNCTION EXPRESSION *)))) (* GEN END FUN BRANCH *)
    in
      retrieve (Child, nsub_query, assignSub, cnstrSubId (), cnstr)
    end

  fun retrieval (n, STree as Node(s, Children), G, r, sc) =
    (* s = id *)
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val (nsub_query, assignSub) = (querySubId (), assignSubId ()) (* GEN END TAG OUTSIDE LET *)
    in
      S.insert nsub_query (1, (I.Null, (Body, r)));
      S.forall Children ((* GEN BEGIN FUNCTION EXPRESSION *) fn (_, C) => retrieveChild (n, C, nsub_query, assignSub, nil, G, sc) (* GEN END FUNCTION EXPRESSION *))
    end

 (*----------------------------------------------------------------------------*)
 (* Retrieval via set of candidates *)
 fun retrieveAll (num, Child, nsub_query, assignSub, cnstr, candSet) =
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val i = ref 0 (* GEN END TAG OUTSIDE LET *)
      fun (* GEN BEGIN FUN FIRST *) retrieve (Leaf(nsub, Gclause, Residuals), nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) =
         (case assignableLazy (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr)
          (* destructively updates assignSub, might initiate backtracking  *)
          of NONE => ()
          | SOME(nsub_query', (nsub_left', cnstrSub'), cnstr') =>
            (if (isId nsub_query')
               then
                 (* LCO optimization *)
                 (i := !i+1;
                  S.insert candSet (!i, (assignSub, nsub_left', cnstrSub', cnstr', Gclause, Residuals));())
             else
              raise Error "Left-over normal substitutions!")) (* GEN END FUN FIRST *)
 
        | (* GEN BEGIN FUN BRANCH *) retrieve (Node(nsub, Children), nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) =
         (case assignableLazy (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr)
          (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
          (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
            of NONE => ()
             | SOME (nsub_query', (nsub_left', cnstrSub'), cnstr') =>
               (S.forall Children
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn (n, Child) => retrieve (Child, nsub_query', S.copy assignSub, (S.copy nsub_left', S.copy cnstrSub'), cnstr') (* GEN END FUNCTION EXPRESSION *)))) (* GEN END FUN BRANCH *)
    in
      retrieve (Child, nsub_query, assignSub, (nid(), cnstrSubId ()), cnstr)
    end

 fun retrieveCandidates (n, STree as Node(s, Children), Gquery, r, sc) =
    (* s = id *)
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val (nsub_query, assignSub) = (querySubId (), assignSubId ()) (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val candSet = S.new() (* GEN END TAG OUTSIDE LET *)
      fun solveCandidate (i, candSet) =
        case (S.lookup candSet i)
          of NONE => ((* print "No candidate left anymore\n" ;*) () )
           | SOME(assignSub, nsub_left, cnstrSub, cnstr, Gclause, Residuals
             (* CGoals(AuxG, cid, ConjGoals, i) *)) =>
             (CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
               (S.forall nsub_left ((* GEN BEGIN FUNCTION EXPRESSION *) fn (nv, (l, U)) => case (S.lookup cnstrSub nv)
                                                         of NONE =>  raise Error "Left-over nsubstitution"
                                                       | SOME(I.AVar A) => A := SOME(U) (* GEN END FUNCTION EXPRESSION *));
              solveResiduals (Gquery, Gclause, Residuals, assignSub, cnstr, sc)) (* GEN END FUNCTION EXPRESSION *));
                solveCandidate (i+1, candSet (* sc = (fn S => (O::S)) *) ))
    in
      S.insert nsub_query (1, (I.Null, (Body, r)));
      S.forall Children ((* GEN BEGIN FUNCTION EXPRESSION *) fn (_, C) => retrieveAll (n, C, nsub_query, assignSub, nil, candSet) (* GEN END FUNCTION EXPRESSION *));
      (* execute one by one all candidates : here ! *)
      solveCandidate (1, candSet)
    end

 fun matchSig (a, G, ps as (I.Root(Ha,S),s), sc) =
     let
       (* GEN BEGIN TAG OUTSIDE LET *) val (n, Tree) = Array.sub (indexArray, a) (* GEN END TAG OUTSIDE LET *)
     in
       (* retrieval (n, !Tree, G, I.EClo(ps), sc)   *)
       retrieveCandidates (n, !Tree, G, I.EClo(ps), sc)
     end


 fun matchSigIt (a, G, ps as (I.Root(Ha,S),s), sc) =
     let
       (* GEN BEGIN TAG OUTSIDE LET *) val (n, Tree) = Array.sub (indexArray, a) (* GEN END TAG OUTSIDE LET *)
     in
       retrieval (n, !Tree, G, I.EClo(ps), sc)
     end

 fun sProgReset () =
   (nctr := 1;
     Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn (n, Tree) => (n := 0; Tree := !(makeTree ());
                                   (n, Tree)) (* GEN END FUNCTION EXPRESSION *)) indexArray)


 fun sProgInstall (a, C.Head(E, G, Eqs, cid), R) =
   let
     (* GEN BEGIN TAG OUTSIDE LET *) val (n, Tree) = Array.sub (indexArray, a) (* GEN END TAG OUTSIDE LET *)
     (* GEN BEGIN TAG OUTSIDE LET *) val nsub_goal = S.new() (* GEN END TAG OUTSIDE LET *)
   in
      S.insert nsub_goal (1, (Body, E));
      Tree := insert (!Tree, nsub_goal, (G, CGoals(Eqs, cid, R, !n+1)));
      n := !n+1
 
   end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val sProgReset = sProgReset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val sProgInstall = sProgInstall (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val matchSig = matchSigIt (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor SubTree *)













