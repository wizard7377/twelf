(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform *)
(* Variant Checking *)
(* Author: Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) MemoTable ((*! structure IntSyn' : INTSYN !*)
                   (*! structure CompSyn' : COMPSYN !*)
                   (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                   structure Conv: CONV
                   (*! sharing Conv.IntSyn = IntSyn' !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn' !*)
                   (*! structure RBSet : RBSET !*)
                   (*! structure TableParam : TABLEPARAM !*)
                   (*! sharing TableParam.IntSyn = IntSyn' !*)
                   (*! sharing TableParam.CompSyn = CompSyn' !*)
                   (*! sharing TableParam.RBSet = RBSet !*)
                   structure AbstractTabled : ABSTRACTTABLED
                   (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = IntSyn'!*))
  : MEMOTABLE =
  struct
    (*! structure IntSyn = IntSyn' !*)
    (*! structure CompSyn = CompSyn' !*)
    structure AbstractTabled = AbstractTabled
    (*! structure TableParam = TableParam !*)

    (* ---------------------------------------------------------------------- *)

    (* Linear substitution tree for linear terms *)

    (* normalSubsts: key = int = nvar *)
    (* property: linear *)

    type normal_substs  = IntSyn.exp RBSet.ord_set

    type ex_substs  = IntSyn.exp RBSet.ord_set

    (* GEN BEGIN TAG OUTSIDE LET *) val nid : unit -> normal_substs = RBSet.new (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val aid = TableParam.aid (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val existId : unit -> normal_substs = RBSet.new (* GEN END TAG OUTSIDE LET *)


    fun isId s = RBSet.isEmpty s

    (* ---------------------------------------------------------------------- *)
    type ctx = ((int * IntSyn.dec) list) ref

    fun emptyCtx () :  ctx = ref []

    fun copy L : ctx = ref (!L)

    (* destructively updates L *)
    fun delete (x, L : ctx ) =
      let
        fun (* GEN BEGIN FUN FIRST *) del (x, [], L) = NONE (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) del (x, ((H as (y,E))::L), L') =
            if x = y then SOME((y,E), (rev L')@ L)
            else del(x, L, H::L') (* GEN END FUN BRANCH *)
      in
        case del (x, (!L), [])
          of NONE => NONE
        | SOME((y,E), L') => (L := L'; SOME((y,E)))
      end

    fun member (x, L:ctx) =
      let
        fun (* GEN BEGIN FUN FIRST *) memb (x, []) = NONE (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) memb (x, (H as (y,E)::L)) =
            if x = y then SOME((y,E)) else memb(x, L) (* GEN END FUN BRANCH *)
      in
        memb (x, (!L))
      end

    fun insertList (E, L) = (L := (E::(!L)); L)

    (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)

    fun (* GEN BEGIN FUN FIRST *) ctxToEVarSub (IntSyn.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxToEVarSub (IntSyn.Decl(G,IntSyn.Dec(_,A)), s) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = ctxToEVarSub (G, s) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X = IntSyn.newEVar (IntSyn.Null, IntSyn.EClo(A,s')) (* GEN END TAG OUTSIDE LET *)
      in
        IntSyn.Dot(IntSyn.Exp(X), s')
      end (* GEN END FUN BRANCH *)

    (* ---------------------------------------------------------------------- *)
    (* Substitution Tree *)
    (* it is only possible to distribute the evar-ctx because
     all evars occur exactly once! -- linear
     this allows us to maintain invariant, that every occurrence of an evar is
     defined in its evar-ctx
     *)
    datatype tree =
      Leaf of (ctx *  normal_substs) *
      (((int (* #EVar *)* int (* #G *)) * IntSyn.dctx * (* G *)
        TableParam.res_eqn * TableParam.answer *
        int * TableParam.status) list) ref

      | Node of (ctx *  normal_substs) * (tree ref) list

    fun makeTree () = ref (Node ((emptyCtx(), nid ()), []))

    fun noChildren C = (C=[])

    datatype retrieval =
      Variant of IntSyn.exp
      | NotCompatible

    datatype comp_sub =
      SplitSub of ((ctx * normal_substs (* sigma *)) *
                   (ctx * normal_substs (* rho1 *)) *
                   (ctx * normal_substs (* rho2 *)))
      | VariantSub of  ( (* normalSubsts * *) (ctx * normal_substs (* rho2 *)))
      | NoCompatibleSub

    (* Index array

     All type families have their own substitution tree and all substitution trees
     are stored in an array [a1,...,an]   where ai is a substitution tree for type family ai
     *)

    (* GEN BEGIN TAG OUTSIDE LET *) val indexArray = Array.tabulate (Global.maxCid, ((* GEN BEGIN FUNCTION EXPRESSION *) fn i => (ref 0, makeTree ()) (* GEN END FUNCTION EXPRESSION *))) (* GEN END TAG OUTSIDE LET *);

    exception Error of string

    local

      structure I   = IntSyn
      structure C   = CompSyn
      structure S   = RBSet
      structure A   = AbstractTabled
      structure T   = TableParam


      exception Assignment of string

      exception Generalization of string
      exception DifferentSpines

      fun emptyAnswer () = T.emptyAnsw ()


      (* GEN BEGIN TAG OUTSIDE LET *) val answList : (TableParam.answer list) ref = ref [] (* GEN END TAG OUTSIDE LET *);

      (* GEN BEGIN TAG OUTSIDE LET *) val added = ref false (* GEN END TAG OUTSIDE LET *);

      type nvar = int      (* index for normal variables *)
      type bvar = int      (* index for bound variables *)
      type bdepth = int    (* depth of locally bound variables *)


      (* ------------------------------------------------------ *)
      (* Auxiliary functions *)

      fun (* GEN BEGIN FUN FIRST *) cidFromHead (I.Const c) = c (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) cidFromHead (I.Def c) = c (* GEN END FUN BRANCH *)

      fun (* GEN BEGIN FUN FIRST *) dotn (0, s) = s (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) dotn (i, s) = dotn (i-1, I.dot1 s) (* GEN END FUN BRANCH *)

      fun (* GEN BEGIN FUN FIRST *) compose(IntSyn.Null, G) = G (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) compose(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose(G, G'), D) (* GEN END FUN BRANCH *)

      fun (* GEN BEGIN FUN FIRST *) shift (IntSyn.Null, s) = s (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s)) (* GEN END FUN BRANCH *)

      fun (* GEN BEGIN FUN FIRST *) raiseType (I.Null, U) = U (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) raiseType (I.Decl(G, D), U) = raiseType (G, I.Lam(D, U)) (* GEN END FUN BRANCH *)



    fun (* GEN BEGIN FUN FIRST *) ctxToAVarSub (G', I.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxToAVarSub (G', I.Decl(D,I.Dec(_,A)), s) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val E as I.EVar (r, _, _, cnstr) = I.newEVar (I.Null, A) (* GEN END TAG OUTSIDE LET *)
      in
        I.Dot(I.Exp(E), ctxToAVarSub (G', D, s))
      end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) ctxToAVarSub (G', I.Decl(D,I.ADec(_,d)), s) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newAVar () (* GEN END TAG OUTSIDE LET *)
      in
        I.Dot(I.Exp(I.EClo(X, I.Shift(~d))), ctxToAVarSub (G', D, s))
      end (* GEN END FUN BRANCH *)

    (* solveEqn' ((VarDef, s), G) = bool

     if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
      return true, if VarDefs are solvable
      false otherwise
      *)
    fun (* GEN BEGIN FUN FIRST *) solveEqn' ((T.Trivial, s), G) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) solveEqn' ((T.Unify(G',e1, N (* evar *), eqns), s), G) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val G'' = compose (G', G) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = shift (G', s) (* GEN END TAG OUTSIDE LET *)
      in
        Assign.unifiable (G'', (N, s'),(e1, s'))
        andalso solveEqn' ((eqns, s), G)
      end (* GEN END FUN BRANCH *)

    (* ------------------------------------------------------ *)

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

        linear terms are approximately well-typed in G:  G |- p
        after erasing all typing dependencies.


        Let s be a path in the substitution tree such that
        s1 o s2 o .... o sn = s,



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
      all expressions in the index are closed and linear, i.e.
      an expression is first linearized before it is inserted into the index
      (this makes retrieving all axpressions from the index which unify with
      a given expression simpler, because we can omit the occurs check)

   *)


  (* ---------------------------------------------------------------*)

  (* nctr = |D| =  #index variables *)
   (* GEN BEGIN TAG OUTSIDE LET *) val nctr = ref 1 (* GEN END TAG OUTSIDE LET *)

   fun newNVar () =
     (nctr := !nctr + 1;
      I.NVar(!nctr))

   fun (* GEN BEGIN FUN FIRST *) equalDec (I.Dec(_, U), I.Dec(_, U')) = Conv.conv ((U, I.id), (U', I.id)) (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) equalDec (I.ADec(_, d), I.ADec(_, d')) = (d = d') (* GEN END FUN BRANCH *)
     | (* GEN BEGIN FUN BRANCH *) equalDec (_,_ ) = false (* GEN END FUN BRANCH *)

    (* We require order of both eqn must be the same Sun Sep  8 20:37:48 2002 -bp *)
    (* s = s' = I.id *)
    fun (* GEN BEGIN FUN FIRST *) equalCtx (I.Null, s, I.Null, s') = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalCtx (I.Decl(G, D), s, I.Decl(G', D'), s') =
        Conv.convDec((D, s), (D', s')) andalso (equalCtx (G, I.dot1 s, G', I.dot1 s')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalCtx (_, _, _, _) = false (* GEN END FUN BRANCH *)

    (* in general, we need to carry around and build up a substitution *)
    fun (* GEN BEGIN FUN FIRST *) equalEqn (T.Trivial, T.Trivial) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalEqn (T.Unify(G, X, N, eqn), (T.Unify(G', X', N', eqn'))) =
        equalCtx (G, I.id, G', I.id) andalso Conv.conv ((X, I.id), (X', I.id))
        andalso Conv.conv ((N, I.id), (N', I.id)) andalso equalEqn(eqn, eqn') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalEqn (_, _) = false (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) equalSub (I.Shift k, I.Shift k') = (k = k') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalSub (I.Dot(F, S), I.Dot(F', S')) =
        equalFront (F, F') andalso equalSub (S, S') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalSub (I.Dot(F,S), I.Shift k) = false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalSub (I.Shift k, I.Dot(F,S)) = false (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) equalFront (I.Idx n, I.Idx n') = (n = n') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalFront (I.Exp U, I.Exp V) = Conv.conv ((U, I.id), (V, I.id)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalFront (I.Undef, I.Undef) = true (* GEN END FUN BRANCH *)

    fun equalSub1 (I.Dot(ms, s), I.Dot(ms', s')) =
          equalSub (s, s')

    fun (* GEN BEGIN FUN FIRST *) equalCtx' (I.Null, I.Null) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalCtx' (I.Decl(Dk, I.Dec(_, A)), I.Decl(D1, I.Dec(_, A1))) =
      (Conv.conv ((A, I.id), (A1, I.id)) andalso equalCtx'(Dk, D1)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalCtx' (I.Decl(Dk, I.ADec(_, d')), I.Decl(D1, I.ADec(_, d))) =
        ((d = d') andalso equalCtx'(Dk, D1)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalCtx' (_, _) = false (* GEN END FUN BRANCH *)


   (* ---------------------------------------------------------------*)

    fun compareCtx (G, G') = equalCtx' (G, G')

   (* ---------------------------------------------------------------*)
   (* most specific linear common generalization *)

   (* compatible (T, U) = (T', rho_u, rho_t) opt
    if T is an indexed term
       U is a linear term
       U and T share at least the top function symbol
   then
       T'[rho_u] = U and T'[rho_t] = T
   *)

   fun isExists (d, I.BVar k, D) = member (k-d, D)

   fun (* GEN BEGIN FUN FIRST *) compHeads ((D_1, I.Const k), (D_2, I.Const k')) = (k = k') (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) compHeads ((D_1, I.Def k), (D_2, I.Def k')) = (k = k') (* GEN END FUN BRANCH *)
     | (* GEN BEGIN FUN BRANCH *) compHeads ((D_1, I.BVar k), (D_2, I.BVar k')) =
       (case isExists (0, I.BVar k, D_1)
          of NONE => (k = k')
        | SOME(x,Dec) => true) (* GEN END FUN BRANCH *)
     | (* GEN BEGIN FUN BRANCH *) compHeads ((D_1, I.BVar k), (D_2, H2)) =
        (case isExists (0, I.BVar k, D_1)
          of NONE => false
        | SOME(x,Dec) => true) (* GEN END FUN BRANCH *)
     | (* GEN BEGIN FUN BRANCH *) compHeads ((D_1, H1), (D_2, H2)) = false (* GEN END FUN BRANCH *)


   fun compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u) =
     let
       fun genNVar ((rho_t, T), (rho_u, U)) =
         (S.insert rho_t (!nctr+1, T);
          S.insert rho_u (!nctr+1, U);
          newNVar())
   
       fun (* GEN BEGIN FUN FIRST *) genRoot (depth, T as I.Root(H1 as I.Const k, S1), U as I.Root(I.Const k', S2)) =
         if (k = k') then
           let
             (* GEN BEGIN TAG OUTSIDE LET *) val S' = genSpine(depth, S1, S2) (* GEN END TAG OUTSIDE LET *)
           in
             I.Root(H1, S')
           end
         else
           genNVar ((rho_t, T), (rho_u, U)) (* GEN END FUN FIRST *)
         | (* GEN BEGIN FUN BRANCH *) genRoot (depth, T as I.Root(H1 as I.Def k, S1), U as I.Root(I.Def k', S2)) =
         if (k = k') then
           let
             (* GEN BEGIN TAG OUTSIDE LET *) val S' = genSpine(depth, S1, S2) (* GEN END TAG OUTSIDE LET *)
           in
             I.Root(H1, S')
           end
         else
            
           genNVar ((rho_t, T), (rho_u, U)) (* GEN END FUN BRANCH *)
         | (* GEN BEGIN FUN BRANCH *) genRoot (d,  T as I.Root(H1 as I.BVar k, S1), U as I.Root(I.BVar k', S2)) =
           if (k > d) andalso (k' > d)
             then (* globally bound variable *)
               let
                 (* GEN BEGIN TAG OUTSIDE LET *) val k1 = (k - d) (* GEN END TAG OUTSIDE LET *)
                 (* GEN BEGIN TAG OUTSIDE LET *) val k2 = (k' - d) (* GEN END TAG OUTSIDE LET *)
               in
                 case (member (k1, D_t), member(k2, D_u))
                   of (NONE, NONE) =>
                     if (k1 = k2)
                       then
                         (let
                            (* GEN BEGIN TAG OUTSIDE LET *) val S' = genSpine(d, S1, S2) (* GEN END TAG OUTSIDE LET *)
                          in
                            I.Root(H1, S')
                          end)  handle DifferentSpine => genNVar ((rho_t, T), (rho_u, U))
                     else
                       genNVar ((rho_t, T), (rho_u, U))
                        | (SOME(x, Dec1), SOME(x', Dec2)) =>
                       (* k, k' refer to the existential *)
                       if ((k1 = k2) andalso equalDec(Dec1, Dec2))
                         then (* they refer to the same existential variable *)
                           let
                             (* this is unecessary -- since existential variables have the same type
                                and need to be fully applied in order, S1 = S2 *)
                             (* GEN BEGIN TAG OUTSIDE LET *) val S' = genSpine(d, S1, S2) (* GEN END TAG OUTSIDE LET *)
                           in
                             (delete (x, D_t) ;
                              delete (x', D_u);
                              insertList ((x, Dec1), Ds);
                              I.Root(H1, S'))
                           end
                       else
                         (* variant checking only *)
                         genNVar ((rho_t, T), (rho_u, U))
            
                        | (_, _) =>
                         genNVar ((rho_t, T), (rho_u, U))
               end
           else (* locally bound variables *)
             if (k = k') then
               (let
                  (* GEN BEGIN TAG OUTSIDE LET *) val S' = genSpine(d, S1, S2) (* GEN END TAG OUTSIDE LET *)
                in
                  I.Root(H1, S')
                end) handle DifferentSpines => genNVar ((rho_t, T), (rho_u, U))
             else
               genNVar ((rho_t, T), (rho_u, U)) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) genRoot (d, T as I.Root (H1 as I.BVar k, S1), U as I.Root(I.Const k', S2)) =
               genNVar ((rho_t, T), (rho_u, U)) (* GEN END FUN BRANCH *)
   
          | (* GEN BEGIN FUN BRANCH *) genRoot (d, T as I.Root(H1, S1), U as I.Root(H2, S2)) =
               genNVar ((rho_t, T), (rho_u, U)) (* GEN END FUN BRANCH *)
   
       and (* GEN BEGIN FUN FIRST *) genExp (d, T as I.NVar n, U as I.Root(H, S)) =
         (S.insert rho_u (n, U); T) (* GEN END FUN FIRST *)
         | (* GEN BEGIN FUN BRANCH *) genExp (d, T as I.Root(H1, S1), U as I.Root(H2, S2)) =
         genRoot(d, I.Root(H1, S1), I.Root(H2, S2)) (* GEN END FUN BRANCH *)
         | (* GEN BEGIN FUN BRANCH *) genExp (d, I.Lam(D1 as I.Dec(_,A1), T1), I.Lam(D2 as I.Dec(_, A2), U2)) =
         (* by invariant A1 = A2 *)
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val E = genExp (d+1, T1,  U2) (* GEN END TAG OUTSIDE LET *)
         in
           I.Lam(D1, E)
         end (* GEN END FUN BRANCH *)
         | (* GEN BEGIN FUN BRANCH *) genExp (d, T, U) =
         (* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
         (print "genExp -- falls through?\n";
          genNVar ((rho_t, T), (rho_u, U))) (* GEN END FUN BRANCH *)
   
       and (* GEN BEGIN FUN FIRST *) genSpine (d, I.Nil, I.Nil) =  I.Nil (* GEN END FUN FIRST *)
         | (* GEN BEGIN FUN BRANCH *) genSpine (d, I.App(T, S1), I.App(U, S2)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val  E = genExp (d, T, U) (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val  S' = genSpine (d, S1, S2) (* GEN END TAG OUTSIDE LET *)
         in
           I.App(E, S')
         end (* GEN END FUN BRANCH *)
         | (* GEN BEGIN FUN BRANCH *) genSpine (d, I.Nil, I.App (_ , _)) = raise DifferentSpines (* GEN END FUN BRANCH *)
         | (* GEN BEGIN FUN BRANCH *) genSpine (d, I.App (_ , _), I.Nil) = raise DifferentSpines (* GEN END FUN BRANCH *)
   
         | (* GEN BEGIN FUN BRANCH *) genSpine (d, I.SClo (_ , _), _) =  raise DifferentSpines (* GEN END FUN BRANCH *)
         | (* GEN BEGIN FUN BRANCH *) genSpine (d, _ , I.SClo (_ , _)) = raise DifferentSpines (* GEN END FUN BRANCH *)
       (* GEN BEGIN TAG OUTSIDE LET *) val E = genExp (0, T, U) (* GEN END TAG OUTSIDE LET *)
     in
       Variant E
     end


   fun (* GEN BEGIN FUN FIRST *) compatible ((D_t, T as I.Root(H1, S1)),
                   (D_u, U as I.Root (H2, S2)), Ds, rho_t, rho_u) =
     if compHeads ((D_t, H1), (D_u, H2))
       then
         compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)
     else NotCompatible (* GEN END FUN FIRST *)
     |(* GEN BEGIN FUN BRANCH *) compatible ((D_t, T), (D_u, U), Ds, rho_t, rho_u) =
       compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u) (* GEN END FUN BRANCH *)

 (* ---------------------------------------------------------------*)
 (* compatibleSub(nsub_t, nsub_u) = (sigma, rho_t, rho_u) opt

   if DOM(nsub_t) <= DOM(nsub_u)
      CODOM(nsub_t) : index terms
      CODOM(nsub_u) : linear terms
        G_u, Glocal_u |- nsub_u
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have "approximately" the same type)

   *)
  fun compatibleSub ((D_t, nsub_t), (D_u, nsub_u)) =
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val (sigma, rho_t, rho_u) = (nid(), nid (), nid ()) (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val Dsigma = emptyCtx () (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val D_r1 = copy D_t (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val D_r2 = copy D_u (* GEN END TAG OUTSIDE LET *)
      (* GEN BEGIN TAG OUTSIDE LET *) val choose = ref ((* GEN BEGIN FUNCTION EXPRESSION *) fn match : bool => () (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
     (* by invariant rho_t = empty, since nsub_t <= nsub_u *)
      (* GEN BEGIN TAG OUTSIDE LET *) val _ =  S.forall nsub_u
        ((* GEN BEGIN FUNCTION EXPRESSION *) fn (nv, U) =>
         (case (S.lookup nsub_t nv)
            of SOME (T) =>     (* note by invariant Glocal_e ~ Glocal_t *)
              (case compatible ((D_r1, T), (D_r2, U), Dsigma, rho_t, rho_u)
                 of NotCompatible => (S.insert rho_t (nv, T);
                                      S.insert rho_u (nv, U))
                  | Variant(T') =>
                   let
                     (* GEN BEGIN TAG OUTSIDE LET *) val restc = (!choose) (* GEN END TAG OUTSIDE LET *)
                   in
                     (S.insert sigma (nv, T');
                     choose := ((* GEN BEGIN FUNCTION EXPRESSION *) fn match => (restc match; if match then () else ()) (* GEN END FUNCTION EXPRESSION *)))
                     end)
        
          (* here Glocal_t will be only approximately correct! *)
          | NONE => S.insert rho_u (nv, U)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    in
      if isId (rho_t)
        then
          (* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
          ((!choose) true ;
           VariantSub(D_r2, rho_u))
      else
        ((* split -- asub is unchanged *)
         (!choose) false ;
         if isId(sigma)
           then NoCompatibleSub
         else
           SplitSub((Dsigma, sigma), (D_r1, rho_t), (D_r2, rho_u)))
          (* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
    end


 (* ---------------------------------------------------------------------- *)

  fun mkLeaf (Ds, GR, n) = Leaf (Ds, GR)

  fun (* GEN BEGIN FUN FIRST *) mkNode (Node(_, Children), Dsigma, Drho1, GR, Drho2) =
       Node(Dsigma, [ref (Leaf(Drho2, ref [GR])),
                     ref (Node(Drho1, Children))]) (* GEN END FUN FIRST *)

    | (* GEN BEGIN FUN BRANCH *) mkNode (Leaf(c, GRlist), Dsigma, Drho1, GR2, Drho2) =
       Node(Dsigma,[ref(Leaf(Drho2, ref [GR2])), ref(Leaf(Drho1, GRlist))]) (* GEN END FUN BRANCH *)

  (* ---------------------------------------------------------------------- *)

  fun (* GEN BEGIN FUN FIRST *) compatibleCtx ((G, eqn), []) = NONE (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compatibleCtx ((G,eqn), ((l', G', eqn', answRef', _, status')::GRlist)) =
       (* we may not need to check that the DAVars are the same *)
      (if (equalCtx' (G, G') andalso equalEqn(eqn, eqn'))
         then SOME(l', answRef', status')
       else
         compatibleCtx ((G, eqn), GRlist)) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) compChild (N as Leaf((D_t, nsub_t), GList), (D_e, nsub_e)) =
        compatibleSub ((D_t, nsub_t), (D_e,  nsub_e)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compChild (N as Node((D_t, nsub_t), Children'), (D_e, nsub_e)) =
        compatibleSub ((D_t, nsub_t), (D_e, nsub_e)) (* GEN END FUN BRANCH *)

  fun findAllCandidates (G_r, children, Ds) =
    let
      fun (* GEN BEGIN FUN FIRST *) findAllCands (G_r, nil, (D_u, sub_u), VList, SList) = (VList, SList) (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) findAllCands (G_r, (x::L), (D_u, sub_u), VList, SList) =
          case compChild (!x, (D_u, sub_u))
            of NoCompatibleSub => findAllCands (G_r, L, (D_u, sub_u), VList, SList)
            | SplitSub (Dsigma, Drho1, Drho2) =>
              findAllCands (G_r, L, (D_u, sub_u),VList,
                            ((x, (Dsigma, Drho1, Drho2))::SList))
            | VariantSub (Drho2 as (D_r2, rho2)) =>
              findAllCands (G_r, L, (D_u, sub_u), ((x, Drho2,I.id)::VList), SList) (* GEN END FUN BRANCH *)
  
    in
      findAllCands (G_r, children, Ds, nil,  nil)
    end
 (* ---------------------------------------------------------------------- *)
  fun divergingCtx (stage, G, GRlistRef) =
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val l = I.ctxLength(G) (* GEN END TAG OUTSIDE LET *)
    in
    List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn ((evar, l), G', _, _, stage', _) => (stage = stage' andalso (l > (I.ctxLength(G')))) (* GEN END FUNCTION EXPRESSION *))
    (!GRlistRef)
    end

  fun (* GEN BEGIN FUN FIRST *) eqHeads (I.Const k, I.Const k') =  (k = k') (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eqHeads (I.BVar k, I.BVar k') =  (k = k') (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eqHeads (I.Def k, I.Def k') = (k = k') (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eqHeads (_, _) = false (* GEN END FUN BRANCH *)

 (* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1]
  t2 is a linear term which may not contain any nvars!
  t may contain nvars
 *)

 fun (* GEN BEGIN FUN FIRST *) eqTerm (I.Root(H2, S2), (t as I.Root(H, S), rho1)) =
     if eqHeads (H2, H)
       then eqSpine(S2, (S, rho1))
     else
       false (* GEN END FUN FIRST *)
   | (* GEN BEGIN FUN BRANCH *) eqTerm (T2, (I.NVar n, rho1)) =
     (case (S.lookup rho1 n)
        of NONE => false
      | SOME (T1) => eqTerm (T2, (T1, nid()))) (* GEN END FUN BRANCH *)
   | (* GEN BEGIN FUN BRANCH *) eqTerm (I.Lam(D2, T2), (I.Lam(D, T), rho1)) =
     eqTerm (T2, (T, rho1)) (* GEN END FUN BRANCH *)
   | (* GEN BEGIN FUN BRANCH *) eqTerm (_, (_, _)) = false (* GEN END FUN BRANCH *)

 and (* GEN BEGIN FUN FIRST *) eqSpine (I.Nil, (I.Nil, rho1)) = true (* GEN END FUN FIRST *)
  | (* GEN BEGIN FUN BRANCH *) eqSpine (I.App(T2, S2), (I.App(T, S), rho1)) =
    eqTerm (T2, (T, rho1)) andalso eqSpine (S2, (S, rho1)) (* GEN END FUN BRANCH *)
   | (* GEN BEGIN FUN BRANCH *) eqSpine (_, _) = false (* GEN END FUN BRANCH *)

 fun divergingSub ((Ds, sigma), (Dr1, rho1), (Dr2, rho2)) =
    S.exists rho2 ((* GEN BEGIN FUNCTION EXPRESSION *) fn (n2, t2) => S.exists sigma ((* GEN BEGIN FUNCTION EXPRESSION *) fn (_,t) => eqTerm (t2, (t, rho1)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUNCTION EXPRESSION *))

  (* ---------------------------------------------------------------------- *)
  (* Insert via variant checking *)

  (* insert' (N, (D, nsub), GR) = (f, callCheckResult)

     invariant:

       N is a substitution tree
       nsub is a normal substitution
       D contains all the existential variables in nsub
       GR = (G : bound variable context,
             eqn: residual equations
             answRef : ptr to answer list

     if there exists a path p in N s.t. p ~ nsub
      then
       f is the identity, and callCheckResult = RepeatedEntry(_,_,answRef)
     otherwise (f is a function which destructively updates N
                and once executed, will add a path p ~ nsub to N,
                 callCheckResult = NewEntry (answRef)

  *)
  fun insert (Nref, (D_u, nsub_u), GR) =
    let
      fun (* GEN BEGIN FUN FIRST *) insert' (N as Leaf ((D,  _), GRlistRef),
                   (D_u, nsub_u), GR as ((evarl,l), G_r, eqn, answRef, stage, status)) =
        (* need to compare D and D_u *)
        (case compatibleCtx ((G_r, eqn), (!GRlistRef))
           of NONE => ((* compatible path -- but different ctx! *)
                       if ((!TableParam.divHeuristic) andalso divergingCtx (stage, G_r, GRlistRef))
                         then
                           ((* ctx are diverging --- force suspension *)
                            ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (GRlistRef := (GR::(!GRlistRef));
                                answList := (answRef :: (!answList))) (* GEN END FUNCTION EXPRESSION *),
                            T.DivergingEntry(I.id, answRef)))
                       else
                         (* compatible path (variant) -- ctx are different *)
                          ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (GRlistRef := (GR::(!GRlistRef));
                                     answList := (answRef :: (!answList))) (* GEN END FUNCTION EXPRESSION *),
                          T.NewEntry(answRef))
                          )
         | SOME((evarl', Glength), answRef', status') =>
             ((* compatible path -- SAME ctx *)
              (((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *)), T.RepeatedEntry((I.id,I.id), answRef', status'))
              )) (* GEN END FUN FIRST *)
  
  
      | (* GEN BEGIN FUN BRANCH *) insert' (N as Node((D, sub), children), (D_u, nsub_u),
                 GR as (l, G_r, eqn, answRef, stage, status)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (VariantCand, SplitCand) = findAllCandidates (G_r, children, (D_u, nsub_u)) (* GEN END TAG OUTSIDE LET *)
        
          fun (* GEN BEGIN FUN FIRST *) checkCandidates (nil, nil) =
            ((* no child is compatible with nsub_u *)
             ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (Nref := Node((D, sub), (ref (Leaf((D_u, nsub_u), ref [GR])))::children);
                        answList := (answRef :: (!answList))) (* GEN END FUNCTION EXPRESSION *),
              T.NewEntry(answRef))) (* GEN END FUN FIRST *)
        
            | (* GEN BEGIN FUN BRANCH *) checkCandidates (nil, ((ChildRef, (Dsigma, Drho1, Drho2))::_)) =
              (* split an existing node *)
              if ((!TableParam.divHeuristic) andalso
                  divergingSub (Dsigma, Drho1, Drho2))
               then
                 ((* substree divering -- splitting node *)
                  ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (ChildRef :=  mkNode((!ChildRef), Dsigma, Drho1, GR, Drho2);
                             answList := (answRef :: (!answList))) (* GEN END FUNCTION EXPRESSION *),
                   T.DivergingEntry(I.id, answRef)))
             else
                ((* split existing node *)
                 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (ChildRef :=  mkNode((!ChildRef), Dsigma, Drho1, GR, Drho2);
                            answList := (answRef :: (!answList))) (* GEN END FUNCTION EXPRESSION *),
                 T.NewEntry(answRef))) (* GEN END FUN BRANCH *)
        
            | (* GEN BEGIN FUN BRANCH *) checkCandidates (((ChildRef, Drho2, asub)::nil),  _) =
              (* unique "perfect" candidate (left) *)
                insert (ChildRef, Drho2, GR) (* GEN END FUN BRANCH *)
        
            | (* GEN BEGIN FUN BRANCH *) checkCandidates (((ChildRef, Drho2, asub)::L), SCands) =
              (* there are several "perfect" candidates *)
              (case (insert (ChildRef, Drho2, GR))
                 of (_, T.NewEntry(answRef)) =>  checkCandidates (L, SCands)
               | (f, T.RepeatedEntry(asub, answRef, status)) =>
                   ((f, T.RepeatedEntry(asub, answRef, status)))
               | (f, T.DivergingEntry(asub, answRef)) =>
                   ((f, T.DivergingEntry(asub, answRef)))) (* GEN END FUN BRANCH *)
        
        in
          checkCandidates (VariantCand, SplitCand)
        end (* GEN END FUN BRANCH *)
  in
    insert' (!Nref, (D_u, nsub_u), GR)
  end

    (* ---------------------------------------------------------------------- *)
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
    fun answCheckVariant (s', answRef, O) =
      let
        fun (* GEN BEGIN FUN FIRST *) member ((D, sk), []) = false (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) member ((D, sk), (((D1, s1),_)::S)) =
            if equalSub (sk,s1) andalso equalCtx'(D, D1) then
              true
            else
              member ((D, sk), S) (* GEN END FUN BRANCH *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val (DEVars, sk) = A.abstractAnswSub s' (* GEN END TAG OUTSIDE LET *)
      in
        if member ((DEVars, sk), T.solutions answRef) then
          T.repeated
        else
          (T.addSolution (((DEVars, sk), O), answRef);
          T.new)
      end

    (* ---------------------------------------------------------------------- *)
    fun reset () =
      (nctr := 1;
       Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn (n, Tree) => (n := 0;
                                      Tree := !(makeTree ());
                                      answList := [];
                                      added := false;
                                      (n, Tree)) (* GEN END FUNCTION EXPRESSION *)) indexArray)

    fun (* GEN BEGIN FUN FIRST *) makeCtx (n, I.Null, DEVars : ctx) = n (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) makeCtx (n, I.Decl(G, D), DEVars : ctx) =
        (insertList ((n, D), DEVars);
         makeCtx (n+1, G, DEVars)) (* GEN END FUN BRANCH *)


    (* callCheck (a, DA, DE, G, U eqn) = callCheckResult

       invariant:
       DA, DE, G |- U
       a is the type family of U

       if U is not already in the index, then it is inserted.
       otherwise we return
             a pointer answRef to the answer list.
             (for variant checking, asub = I.id, and varDefs = NONE)
     *)
    fun callCheck (a, DAVars, DEVars, G,  U, eqn, status) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (n, Tree) = Array.sub (indexArray, a) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val nsub_goal = S.new() (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val DAEVars = compose (DEVars, DAVars) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val D = emptyCtx() (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val n = I.ctxLength(G) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = makeCtx (n+1, DAEVars, D:ctx) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val l = I.ctxLength(DAEVars) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = S.insert nsub_goal (1, U) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val result =  insert (Tree, (D, nsub_goal),
                              ((l, n+1), G, eqn, emptyAnswer(), !TableParam.stageCtr, status)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val esub = ctxToAVarSub (G, DAEVars, I.Shift(0)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if solveEqn' ((eqn, shift(G,esub)), G)
                  then () else print " failed to solve eqn_query\n" (* GEN END TAG OUTSIDE LET *)
      in
        case result
          of (sf, T.NewEntry(answRef)) =>
            (sf(); added := true;
             if !Global.chatter >= 5 then print "\t -- Add goal \n" else ();
             T.NewEntry(answRef))
          | (_, T.RepeatedEntry(s as (_, asub), answRef, status)) =>
            (if !Global.chatter >= 5 then print "\t -- Suspend goal\n" else ();
             T.RepeatedEntry((esub, asub), answRef, status))
          | (sf, T.DivergingEntry(answRef)) =>
            (sf(); added := true;
             if !Global.chatter >= 5 then print "\t -- Add diverging goal\n" else ();
             T.DivergingEntry(answRef))
      end



    (* insertIntoSTre (a, DA, DE, G, U eqn) = Succeeds

       invariant:
       DA, DE, G |- U
       a is the type family of U

       U is not already in the index, then it is inserted.
       otherwise we return
             a pointer answRef to the answer list.
             (for variant checking, asub = I.id, and varDefs = NONE)
     *)
    fun insertIntoTree (a, DAVars, DEVars, G,  U, eqn, answRef, status) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (n, Tree) = Array.sub (indexArray, a) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val nsub_goal = S.new() (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val DAEVars = compose (DEVars, DAVars) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val D = emptyCtx() (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val n = I.ctxLength(G) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = makeCtx (n+1, DAEVars, D:ctx) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val l = I.ctxLength(DAEVars) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = S.insert nsub_goal (1, U) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val result =  insert (Tree, (D, nsub_goal),
                              ((l, n+1), G, eqn, answRef, !TableParam.stageCtr, status)) (* GEN END TAG OUTSIDE LET *)
      in
        case result
          of (sf, T.NewEntry(answRef)) =>
            (added := true;
             if !Global.chatter >= 5 then print "\t -- Add goal \n" else ();
             T.NewEntry(answRef))
          | (_, T.RepeatedEntry(asub,answRef, status)) =>
            (if !Global.chatter >= 5 then print "\t -- Suspend goal\n" else ();
             T.RepeatedEntry(asub, answRef, status))
          | (sf, T.DivergingEntry(answRef)) =>
            (sf(); added := true;
             if !Global.chatter >= 5 then print "\t -- Add diverging goal\n" else ();
             T.DivergingEntry(answRef))
      end


    fun answCheck (s', answRef, O) = answCheckVariant (s', answRef, O)


    fun updateTable () =
      let
        fun (* GEN BEGIN FUN FIRST *) update [] Flag = Flag (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) update (answRef::AList) Flag =
            (let
               (* GEN BEGIN TAG OUTSIDE LET *) val l = length(T.solutions(answRef)) (* GEN END TAG OUTSIDE LET *)
             in
               if (l = T.lookup(answRef)) then
                 (* no new solutions were added in the previous stage *)
                 update AList Flag
              else
                (* new solutions were added *)
                (T.updateAnswLookup (l, answRef);
                 update AList true)
            end) (* GEN END FUN BRANCH *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Flag = update (!answList) false (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val r = (Flag orelse (!added)) (* GEN END TAG OUTSIDE LET *)
      in
        added := false;
        r
      end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val callCheck = ((* GEN BEGIN FUNCTION EXPRESSION *) fn (DAVars, DEVars, G, U, eqn, status) =>
                        callCheck(cidFromHead(I.targetHead U), DAVars, DEVars, G, U, eqn, status) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)


    (* GEN BEGIN TAG OUTSIDE LET *) val insertIntoTree = ((* GEN BEGIN FUNCTION EXPRESSION *) fn (DAVars, DEVars, G, U, eqn, answRef, status) =>
                          insertIntoTree(cidFromHead(I.targetHead U), DAVars, DEVars,
                                         G, U, eqn, answRef, status) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val answerCheck = answCheck (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val updateTable = updateTable (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val tableSize = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (length(!answList)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    (* memberCtx ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t. V = V'[^n]
       then return true
         otherwise false
     *)
    fun memberCtx ((G,V), G') =
      let
        fun (* GEN BEGIN FUN FIRST *) memberCtx' ((G, V), I.Null, n) = NONE (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) memberCtx' ((G, V), I.Decl(G', D' as I.Dec(_, V')), n) =
           if Conv.conv ((V, I.id), (V', I.Shift n))
             then
               SOME(D')
           else
             memberCtx' ((G,V), G',n+1) (* GEN END FUN BRANCH *)
      in
        memberCtx' ((G,V), G', 1)
      end


  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor MemoTable *)

