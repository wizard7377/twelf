open Basis

(* Linear Substitution Tree indexing *)

(* Linearity: Any variables occurring inside the substitution tree are linear *)

(* Any term we insert into the substitution tree is in normalform ! *)

(* Instance Checking *)

(* Author: Brigitte Pientka *)

module MemoTableInst
    (Conv : Conv.CONV)
    (Whnf : Whnf.WHNF)
    (Match : Match.MATCH)
    (Assign : Assign.ASSIGN)
    (AbstractTabled : Abstract.Abstract.ABSTRACTTABLED)
    (Print : Print.PRINT) : Subtree.Sw_subtree.MEMOTABLE = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure CompSyn = CompSyn' !*)

  module AbstractTabled = AbstractTabled
  (*! structure TableParam = TableParam !*)

  (* ---------------------------------------------------------------------- *)

  (* Linear substitution tree for_sml linear terms *)

  (* normalSubsts: key = int = nvar  (key, (depth, U))

   example:  \x. f( i1, a)   then i1 = (1, X) = X[x/x]

   *)

  (* property: linear *)

  type normalSubsts = int (* local depth *) * IntSyn.exp RBSet.ordSet
  type exSubsts = IntSyn.front RBSet.ordSet

  let nid : unit -> normalSubsts = RBSet.new_
  let asid : unit -> exSubsts = RBSet.new_
  let aid = TableParam.aid
  let rec isId s = RBSet.isEmpty s
  (* ---------------------------------------------------------------------- *)

  (* Context for_sml existential variable *)

  type ctx = int * IntSyn.dec list ref
  (* functions for_sml handling context for_sml existential variables *)

  let rec emptyCtx () ctx = ref []
  let rec copy L ctx = ref !L
  (* destructively updates L *)

  let rec delete ((x, L) : ctx) =
    let rec del = function
      | x, [], L -> None
      | x, H :: L, L' ->
          if x = y then Some ((y, E), rev L' @ L) else del (x, L, H :: L')
    in
    match del (x, !L, []) with
    | None -> None
    | Some ((y, E), L') ->
        L := L';
        Some (y, E)

  let rec member ((x, L) : ctx) =
    let rec memb = function
      | x, [] -> None
      | x, H -> if x = y then Some (y, E) else memb (x, L)
      | x, H -> if x = y then Some (y, E) else memb (x, L)
    in
    memb (x, !L)

  let rec insertList E L = L := E :: !L
  (* ---------------------------------------------------------------------- *)

  (* Substitution Tree *)

  (* It is only possible to distribute the evar-ctx because
     all evars occur exactly once, i.e. they are linear.
     This allows us to maintain invariant, that every occurrence of an evar is
     defined in its evar-ctx
  *)

  type tree =
    | Leaf of
        (ctx * normalSubsts)
        * (int (* #EVar *) * int (* #G *))
        * ctx (* D *)
        * IntSyn.dctx (* G *)
        * TableParam.resEqn
        * TableParam.answer
        * int
        * TableParam.status list ref
    | Node of (ctx * normalSubsts) * tree ref list

  let rec makeTree () = ref (Node ((emptyCtx (), nid ()), []))
  let rec noChildren C = C = []

  type retrieval = Variant of (int * IntSyn.exp) | NotCompatible

  type compSub =
    | SplitSub of
        ((ctx * normalSubsts (* sigma *))
        * (ctx * normalSubsts (* rho1 *))
        * (ctx * normalSubsts (* rho2 *)))
    | InstanceSub of (exSubsts * (ctx * normalSubsts (* rho2 *)))
    | VariantSub of (ctx * normalSubsts (* rho2 *))
    | NoCompatibleSub
  (* Index array

   All type families have their own substitution tree and all substitution trees
   are stored in an array [a1,...,an]   where ai is a substitution tree for_sml type family ai
   *)

  let indexArray = Array.tabulate (Global.maxCid, fun i -> (ref 0, makeTree ()))

  exception Error of string

  module I = IntSyn
  module C = CompSyn
  module S = RBSet
  module A = AbstractTabled
  module T = TableParam

  exception Assignment of string
  exception Instance of string
  exception Generalization of string
  exception DifferentSpines

  let rec emptyAnswer () = T.emptyAnsw ()
  let answList : TableParam.answer list ref = ref []
  let added = ref false

  type nvar = int
  (* index for_sml normal variables *)

  type bvar = int
  (* index for_sml bound variables *)

  type bdepth = int
  (* depth of locally bound variables *)

  (* ------------------------------------------------------ *)

  (* for_sml debugging only *)

  let rec expToS G U = try Print.expToString (G, U) with _ -> " <_ >"

  let rec printSub = function
    | G, I.Shift n -> print ("I.Shift " ^ Int.toString n ^ "\n")
    | G, I.Dot (I.Idx n, s) ->
        print ("Idx " ^ Int.toString n ^ " . ");
        printSub (G, s)
    | G, I.Dot (I.Exp X, s) ->
        print ("Exp ( EVar " ^ expToS G X ^ ").");
        printSub (G, s)
    | G, I.Dot (I.Exp X, s) ->
        print ("Exp ( EVar  " ^ expToS G X ^ ").");
        printSub (G, s)
    | G, I.Dot (I.Exp (I.AVar _), s) ->
        print "Exp (AVar _ ). ";
        printSub (G, s)
    | G, I.Dot (I.Exp (I.EClo (I.AVar { contents = Some U }, s')), s) ->
        print ("Exp (AVar " ^ expToS (G, I.EClo (U, s')) ^ ").");
        printSub (G, s)
    | G, I.Dot (I.Exp X, s) ->
        print ("Exp (EVarClo " ^ expToS (G, I.EClo (U, s')) ^ ") ");
        printSub (G, s)
    | G, I.Dot (I.Exp X, s) ->
        print ("Exp (EClo " ^ expToS (G, Whnf.normalize (U, s')) ^ ") ");
        printSub (G, s)
    | G, I.Dot (I.Exp E, s) ->
        print ("Exp ( " ^ expToS G E ^ " ). ");
        printSub (G, s)
    | G, I.Dot (I.Undef, s) ->
        print "Undef . ";
        printSub (G, s)
  (* auxiliary function  -- needed to dereference AVars -- expensive?*)

  let rec normalizeSub = function
    | I.Shift n -> I.Shift n
    | I.Dot (I.Exp (I.EClo (I.AVar { contents = Some U }, s')), s) ->
        I.Dot (I.Exp (Whnf.normalize (U, s')), normalizeSub s)
    | I.Dot (I.Exp (I.EClo (I.EVar ({ contents = Some U }, _, _, _), s')), s) ->
        I.Dot (I.Exp (Whnf.normalize (U, s')), normalizeSub s)
    | I.Dot (I.Exp U, s) ->
        I.Dot (I.Exp (Whnf.normalize (U, I.id)), normalizeSub s)
    | I.Dot (I.Idx n, s) -> I.Dot (I.Idx n, normalizeSub s)
  (* ------------------------------------------------------ *)

  (* Auxiliary functions *)

  (* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *)

  let rec etaSpine = function
    | I.Nil, n -> n = 0
    | I.App (I.Root (I.BVar k, I.Nil), S), n -> k = n && etaSpine (S, n - 1)
    | I.App (A, S), n -> false

  let rec cidFromHead = function I.Const c -> c | I.Def c -> c
  let rec dotn = function 0, s -> s | i, s -> dotn (i - 1, I.dot1 s)

  let rec raiseType = function
    | I.Null, V -> V
    | I.Decl (G, D), V -> raiseType (G, I.Lam (D, V))
  (* compose (Decl(G',D1'), G) =   G. .... D3'. D2'.D1'
       where G' = Dn'....D3'.D2'.D1' *)

  let rec compose = function
    | IntSyn.Null, G -> G
    | IntSyn.Decl (G', D), G -> IntSyn.Decl (compose (G', G), D)

  let rec shift = function
    | IntSyn.Null, s -> s
    | IntSyn.Decl (G, D), s -> I.dot1 (shift (G, s))
  (* ---------------------------------------------------------------------- *)

  (* ctxToEVarSub D = s

     if D is a context for_sml existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)

  let rec ctxToEVarSub = function
    | I.Null, s -> s
    | I.Decl (G, I.Dec (_, A)), s ->
        let X = I.newEVar (I.Null, A) in
        I.Dot (I.Exp X, ctxToEVarSub (G, s))
  (* ---------------------------------------------------------------------- *)

  (* Matching for_sml linear terms based on assignment *)

  (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)

  let rec lowerEVar' = function
    | X, G, (I.Pi ((D', _), V'), s') ->
        let D'' = I.decSub (D', s') in
        let X', U =
          lowerEVar' (X, I.Decl (G, D''), Whnf.whnf (V', I.dot1 s'))
        in
        (X', I.Lam (D'', U))
    | X, G, Vs' ->
        let X' = X in
        (X', X')

  and lowerEVar1 = function
    | X, I.EVar (r, G, _, _), (V, s) ->
        let X', U = lowerEVar' (X, G, (V, s)) in
        I.EVar (ref (Some U), I.Null, V, ref [])
    | _, X, _ -> X

  and lowerEVar = function
    | E, X -> lowerEVar1 (E, X, Whnf.whnf (V, I.id))
    | E, I.EVar _ ->
        raise
          (Error
             "abstraction : LowerEVars: Typing ambiguous -- constraint of \
              functional type cannot be simplified")

  let rec ctxToAVarSub = function
    | G', I.Null, s -> s
    | G', I.Decl (D, I.Dec (_, A)), s ->
        let E = I.newEVar (I.Null, A) in
        I.Dot (I.Exp E, ctxToAVarSub (G', D, s))
    | G', I.Decl (D, I.ADec (_, d)), s ->
        let X = I.newAVar () in
        I.Dot (I.Exp (I.EClo (X, I.Shift ~-d)), ctxToAVarSub (G', D, s))
  (* assign(d, Dec(n, V), I.Root(BVar k, S), U, asub) = ()
      Invariant:
      if D ; G |- U : V
         D ; G |- X : V
      then
         add (X, U) to asub
         where  assub is a set of substitutions for_sml existential variables)
    *)

  (* [asub]E1  = U *)

  let rec assign = function
    | ( (* (t, passed)*)
        d,
        Dec1,
        E1,
        U,
        asub ) ->
        let E = I.newEVar (I.Null, V) in
        let X =
          lowerEVar1 (E, I.EVar (r, I.Null, V, cnstr), Whnf.whnf (V, I.id))
        in
        let _ = r := Some U in
        S.insert asub (k - d, I.Exp X)
    | ( (* (t, passed)*)
        d,
        Dec1,
        E1,
        U,
        asub ) ->
        let A = I.newAVar () in
        let _ = r := Some U in
        let Us = Whnf.whnf (U, I.Shift ~-d') in
        S.insert asub (k - d, I.Exp (I.EClo (A, I.Shift ~-d')))
  (* terms are in normal form *)

  (* exception Assignment of string *)

  (* assignExp (fasub, (l, (r, passed), d) (D1, U1), (D2, U2))) = fasub'

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

      NOTE: We only allow assignment for_sml fully applied evars --
      and we will fail otherwise. This essentially only allows first-order assignment.
      To generalize this, we would need to linearize the ctx and have more complex
      abstraction algorithm.

   *)

  let rec assignExp = function
    | fasub, (ctxTotal, d), (D1, U1), (D2, U2) -> (
        match (H1, H2) with
        | I.Const c1, I.Const c2 ->
            if c1 = c2 then
              assignSpine (fasub, (ctxTotal, d), (D1, S1), (D2, S2))
            else raise (Assignment "Constant clash")
        | I.Def c1, I.Def c2 ->
            (* we do not expand definitions here -- this is very conservative! *)
            if c1 = c2 then
              assignSpine (fasub, (ctxTotal, d), (D1, S1), (D2, S2))
            else
              let U1' = Whnf.normalize (Whnf.expandDef (U1, I.id)) in
              let U2' = Whnf.normalize (Whnf.expandDef (U2, I.id)) in
              assignExp (fasub, (ctxTotal, d), (D1, U1'), (D2, U2'))
        | I.Def c1, _ ->
            (* we do not expand definitions here -- this is very conservative! *)
            let U1' = Whnf.normalize (Whnf.expandDef (U1, I.id)) in
            assignExp (fasub, (ctxTotal, d), (D1, U1'), (D2, U2))
        | _, I.Def c2 ->
            (* we do not expand definitions here -- this is very conservative! *)
            let U2' = Whnf.normalize (Whnf.expandDef (U2, I.id)) in
            assignExp (fasub, (ctxTotal, d), (D1, U1), (D2, U2'))
        | I.BVar k1, I.BVar k2 -> (
            if k1 <= r + d (* if (k1 - d) >= l *) then
              (* k1 is a globally bound variable *)
              if k2 <= r + d then (* k2 is globally bound *)
                if k2 = k1 then fasub else raise (Assignment "BVar clash")
              else raise (Assignment "BVar - EVar clash")
            else (* k1 is an existial variable *)
              match member (k1 - d + passed, D1) with
              | None -> raise (Assignment "EVar nonexistent")
              | Some (x, Dec) ->
                  if k2 <= r + d then (* k2 is globally bound *)
                    raise (Assignment "EVar - BVar clash")
                  else if k2 = k1 then (* denote the same evar *)
                    (fun asub ->
                    fasub asub;
                    assign
                      ( (* ctxTotal,*)
                        d,
                        Dec,
                        U1,
                        U2,
                        asub ))
                  else
                    raise
                      (Assignment
                         "EVars are different -- outside of the allowed \
                          fragment"))
        | I.Skonst c1, I.Skonst c2 ->
            if c1 = c2 then
              assignSpine (fasub, (ctxTotal, d), (D1, S1), (D2, S2))
            else raise (Assignment "Skolem constant clash")
              (* can this happen ? -- definitions should be already expanded ?*)
        | _ -> raise (Assignment "Head mismatch "))
    | fasub, (ctxTotal, d), (D1, I.Lam (Dec1, U1)), (D2, I.Lam (Dec2, U2)) ->
        assignExp (fasub, (ctxTotal, d + 1), (D1, U1), (D2, U2))
    | ( fasub,
        (ctxTotal, d),
        (D1, I.Pi ((Dec1, _), U1)),
        (D2, I.Pi ((Dec2, _), U2)) ) ->
        (* is this necessary? Tue Aug  3 11:56:17 2004 -bp *)
        let fasub' = assignExp (fasub, (ctxTotal, d), (D1, V1), (D2, V2)) in
        assignExp (fasub', (ctxTotal, d + 1), (D1, U1), (D2, U2))
    | fasub, (ctxTotal, d), (D1, I.EClo (U, s')), (D2, U2) ->
        assignExp (fasub, (ctxTotal, d), (D1, U), (D2, U2))
    | fasub, (ctxTotal, d), (D1, U1), (D2, I.EClo (U, s)) ->
        assignExp (fasub, (ctxTotal, d), (D1, U1), (D2, U))

  and assignSpine = function
    | fasub, (ctxTotal, d), (D1, I.Nil), (D2, I.Nil) -> fasub
    | fasub, (ctxTotal, d), (D1, I.App (U1, S1)), (D2, I.App (U2, S2)) ->
        let fasub' = assignExp (fasub, (ctxTotal, d), (D1, U1), (D2, U2)) in
        assignSpine (fasub', (ctxTotal, d), (D1, S1), (D2, S2))
  (* assignCtx (fasub, (r, passed), (D1, G), (D2, G')) = fasub'
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

  let rec assignCtx = function
    | fasub, ctxTotal, (D1, I.Null), (D2, I.Null) -> fasub
    | ( fasub,
        ctxTotal,
        (D1, I.Decl (G1, I.Dec (_, V1))),
        (D2, I.Decl (G2, I.Dec (_, V2))) ) ->
        let fasub' =
          assignExp (fasub, ((r - 1, passed + 1), 0), (D1, V1), (D2, V2))
        in
        assignCtx (fasub', (r - 1, passed + 1), (D1, G1), (D2, G2))
  (* ------------------------------------------------------ *)

  (*  Variable b    : bound variable
    Variable n    : index variable
    linear term  U ::=  Root(c, S) | Lam (D, U) | Root(b, S)
    linear Spine S ::= p ; S | NIL
    indexed term t ::= Root(n, NIL) |  Root(c, S) | Lam (D, p) | Root(b, S)
    indexed spines S_i ::= t ; S_i | NIL
    Types   A
    Context G : context for_sml bound variables (bvars)
    (type information is stored in the context)

       G ::= . | G, x : A
       Set of all index variables:  N

    linear terms are well-typed in G:     G |- p
    indexed terms are well-typed in (N ; G) |- t

    Let s is a substitution for_sml index variables (nvar)
    and s1 o s2 o .... o sn = s, s.t.
    forall nvar in CODOM(sk).
     exists i . nvar in DOM(si) and i > k.

    IMAGE (s) = the index variables occurring in the CODOM(s)

    Let N1 ... Nn be the path from the root N1 to the Leaf Nn,
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

  let nctr = ref 1

  let rec newNVar () =
    nctr := !nctr + 1;
    I.NVar !nctr

  let rec equalDec = function
    | I.Dec (_, U), I.Dec (_, U') -> Conv.conv ((U, I.id), (U', I.id))
    | I.ADec (_, d), I.ADec (_, d') -> d = d'
    | _, _ -> false
  (* too restrictive if we require order of both eqn must be the same ?
     Sun Sep  8 20:37:48 2002 -bp *)

  (* s = s' = I.id *)

  let rec equalCtx = function
    | I.Null, s, I.Null, s' -> true
    | I.Decl (G, D), s, I.Decl (G', D'), s' ->
        Conv.convDec ((D, s), (D', s')) && equalCtx (G, I.dot1 s, G', I.dot1 s')
    | _, s, _, s' -> false
  (* equalEqn (e, e') = (e = e') *)

  let rec equalEqn = function
    | T.Trivial, T.Trivial -> true
    | T.Unify (G, X, N, eqn), T.Unify (G', X', N', eqn') ->
        equalCtx (G, I.id, G', I.id)
        && Conv.conv ((X, I.id), (X', I.id))
        && Conv.conv ((N, I.id), (N', I.id))
        && equalEqn (eqn, eqn')
    | _, _ -> false
  (* equalEqn' (d, (D, e), (D', e'), asub) = (e = e')

       destructively updates asub such that all the evars occurring in D'
       will be instantiated and  D |- asub : D'

       if D |- e and D' |- e'  and d = depth of context G'
          asub partially instantiates variables from D'
       then
         D |- asub : D'

    *)

  let rec equalEqn' = function
    | d, (D, T.Trivial), (D', T.Trivial), asub -> true
    | ( d,
        (D, T.Unify (G, X, N (* AVar *), eqn)),
        (D', T.Unify (G', X', N' (* AVar *), eqn')),
        asub ) ->
        if
          equalCtx (G, I.id, G', I.id)
          && Conv.conv ((X, I.id), (X', I.id))
          && Conv.conv ((N, I.id), (N', I.id))
        then (
          (* X is the evar in the query, X' is the evar in the index,
             potentially X' is not yet instantiated and X' in D' but X' not in asub *)
          let d' = d + I.ctxLength G' in
          if k - d' > 0 then
            match member (k - d', D') with
            | None -> ()
            | Some (x, Dec) -> (
                (* k refers to an evar *)
                match RBSet.lookup asub (k - d') with
                | None ->
                    (* it is not instantiated yet *)
                    delete (x, D');
                    S.insert asub (k - d', I.Idx (k - d'))
                | Some _ -> ())
            (* it is instantiated;
                                          since eqn were solvable, eqn' would be solvable too *)
          else (* k refers to a bound variable *)
            (
            print "Impossible -- Found BVar instead of EVar\n";
            raise (Error "Impossibe -- Found BVar instead of EVar "));
          equalEqn' (d, (D, eqn), (D', eqn'), asub))
        else false
    | d, _, _, asub -> false
  (* equalSub (s, s') = (s=s') *)

  let rec equalSub = function
    | I.Shift k, I.Shift k' -> k = k'
    | I.Dot (F, S), I.Dot (F', S') -> equalFront (F, F') && equalSub (S, S')
    | I.Dot (F, S), I.Shift k -> false
    | I.Shift k, I.Dot (F, S) -> false

  and equalFront = function
    | I.Idx n, I.Idx n' -> n = n'
    | I.Exp U, I.Exp V -> Conv.conv ((U, I.id), (V, I.id))
    | I.Undef, I.Undef -> true
  (* equalCtx' (G, G') = (G=G') *)

  let rec equalCtx' = function
    | I.Null, I.Null -> true
    | I.Decl (Dk, I.Dec (_, A)), I.Decl (D1, I.Dec (_, A1)) ->
        Conv.conv ((A, I.id), (A1, I.id)) && equalCtx' (Dk, D1)
    | I.Decl (Dk, I.ADec (_, d')), I.Decl (D1, I.ADec (_, d)) ->
        d = d' && equalCtx' (Dk, D1)
    | _, _ -> false
  (* ---------------------------------------------------------------*)

  (* destructively may update asub ! *)

  let rec instanceCtx (asub, (D1, G1), (D2, G2)) =
    let d1 = I.ctxLength G1 in
    let d2 = I.ctxLength G2 in
    if d1 = d2 then
      try
        let fasub = assignCtx ((fun asub -> ()), (d1, 0), (D1, G1), (D2, G2)) in
        fasub asub;
        true
      with Assignment msg ->
        (* print msg;*)
        false
    else false
  (* ---------------------------------------------------------------*)

  (* collect EVars in sub *)

  (* collectEVar D sq = (D_sub, D')
     if D |- sq where D is a set of free variables
     then Dsq |- sq  and (Dsq u D') = D
          Dsq contains all the free variables occuring in sq
          D' contains all the free variables corresponding to Gsq
   *)

  let rec collectEVar D nsub =
    let D' = emptyCtx () in
    let rec collectExp = function
      | d, D', D, I.Lam (_, U) -> collectExp (d + 1, D', D, U)
      | d, D', D, I.Root (I.Const c, S) -> collectSpine (d, D', D, S)
      | d, D', D, I.Root (I.BVar k, S) -> (
          match member (k - d, D) with
          | None -> collectSpine (d, D', D, S)
          | Some (x, Dec) ->
              delete (x - d, D);
              insertList ((x - d, Dec), D'))
      | d, D', D, U ->
          let U' = Whnf.normalize (Whnf.expandDef (U, I.id)) in
          collectExp (d, D', D, U')
    and collectSpine = function
      | d, D', D, I.Nil -> ()
      | d, D', D, I.App (U, S) ->
          collectExp (d, D', D, U);
          collectSpine (d, D', D, S)
    in
    S.forall nsub (fun (nv, (du, U)) -> collectExp (0, D', D, U));
    (D', D)
  (* ---------------------------------------------------------------*)

  (* most specific linear common generalization *)

  (* compatible (T, U) = (T', rho_u, rho_t) opt
    if T is an indexed term
       U is a linear term
       U and T share at least the top function symbol
   then
       T'[rho_u] = U and T'[rho_t] = T
   *)

  let rec convAssSub' (G, idx_k, D, asub, d, evarsl) =
    match RBSet.lookup asub d with
    | None -> (
        match member (d, D) with
        | None -> IntSyn.Shift (evars + avars (* 0 *))
        | Some (x, IntSyn.Dec (n, V)) ->
            (* Found an EVar which is not yet
                     instantiated -- must be instantiated when
                     solving residual equations! *)
            let s = convAssSub' (G, idx_k + 1, D, asub, d + 1, evarsl) in
            let E = I.newEVar (I.Null, V) in
            I.Dot (I.Exp (I.EClo (E, I.Shift (evars + avars))), s)
        | Some (x, IntSyn.ADec (n, V)) ->
            (* should never happen -- all avars should
                     have been assigned! *)
            print "convAssSub' -- Found an uninstantiated AVAR\n";
            raise (Error "Unassigned AVar -- should never happen\n"))
    | Some F ->
        let E' = Whnf.normalize (E, I.id) in
        I.Dot (I.Exp E', convAssSub' (G, idx_k + 1, D, asub, d + 1, evarsl))

  let rec convAssSub (G, asub, Glength, D', evarsl) =
    convAssSub' (G, 0, D', asub, Glength, evarsl)

  let rec isExists (d, I.BVar k, D) = member (k - d, D)
  (* [s']T = U so U = query and T is in the index *)

  let rec instance ((D_t, (dt, T)), (D_u, (du, U)), rho_u, ac) =
    let rec instRoot = function
      | depth, T, U, ac ->
          if k = k' then instSpine (depth, S1, S2, ac)
          else raise (Instance "Constant mismatch\n")
      | depth, T, U, ac ->
          if k = k' then instSpine (depth, S1, S2, ac)
          else
            let T' = Whnf.normalize (Whnf.expandDef (T, I.id)) in
            let U' = Whnf.normalize (Whnf.expandDef (U, I.id)) in
            instExp (depth, T', U', ac)
      | depth, T, U, ac ->
          let T' = Whnf.normalize (Whnf.expandDef (T, I.id)) in
          instExp (depth, T', U, ac)
      | d, T, U, ac ->
          if k > d && k' > d then (* globally bound variable *)
            let k1 = k - d in
            let k2 = k' - d in
            match (member (k1, D_t), member (k2, D_u)) with
            | None, None ->
                if
                  (* both refer to the same globally bound variable in G *)
                  k1 = k2
                then instSpine (d, S1, S2, ac)
                else raise (Instance "Bound variable mismatch\n")
            | Some (x, Dec1), Some (x', Dec2) ->
                (* k, k' refer to the existential *)
                if k1 = k2 && equalDec (Dec1, Dec2) then
                  (* they refer to the same existential variable *)
                  (* this is unecessary *)
                  (* since existential variables have the same type
                             and need to be fully applied in order, S1 = S2 *)
                  let ac' = instSpine (d, S1, S2, ac) in
                  let ac'' =
                   fun asub ->
                    ac' asub;
                    (* S.insert asub (k - d, I.Idx (k-d)) *)
                    assign
                      ( (* ctxTotal,*)
                        d,
                        Dec1,
                        T,
                        U,
                        asub )
                  in
                  ac''
                else (* instance checking only Sun Oct 27 12:16:10 2002 -bp *)
                  fun asub ->
                  ac asub;
                  assign
                    ( (* ctxTotal,*)
                      d,
                      Dec1,
                      T,
                      U,
                      asub )
                  (* instance checking only Sun Oct 27 12:18:53 2002 -bp *)
            | Some (x, Dec1), None ->
                fun asub ->
                  ac asub;
                  assign
                    ( (* ctxTotal,*)
                      d,
                      Dec1,
                      T,
                      U,
                      asub )
            | Some (x, Dec1), None ->
                fun asub ->
                  ac asub;
                  assign
                    ( (* ctxTotal,*)
                      d,
                      Dec1,
                      T,
                      U,
                      asub )
            | _, _ -> raise (Instance "Impossible\n")
          else (* locally bound variables *)
            raise (Instance "Bound variable mismatch\n")
      | d, T, U, ac -> (
          match isExists (d, I.BVar k, D_t) with
          | None -> raise (Instance "Impossible\n")
          | Some (x, Dec1) ->
              fun asub ->
                ac asub;
                assign
                  ( (* ctxTotal,*)
                    d,
                    Dec1,
                    T,
                    U,
                    asub )
          | Some (x, Dec1) ->
              fun asub ->
                ac asub;
                assign
                  ( (* ctxTotal, *)
                    d,
                    Dec1,
                    T,
                    U,
                    asub ))
      | d, T, U, ac -> (
          match isExists (d, I.BVar k, D_t) with
          | None -> raise (Instance "Impossible\n")
          | Some (x, Dec1) ->
              fun asub ->
                ac asub;
                assign
                  ( (* ctxTotal,*)
                    d,
                    Dec1,
                    T,
                    U,
                    asub )
          | Some (x, Dec1) ->
              fun asub ->
                ac asub;
                assign
                  ( (* ctxTotal, *)
                    d,
                    Dec1,
                    T,
                    U,
                    asub ))
      | depth, T, U, ac ->
          let U' = Whnf.normalize (Whnf.expandDef (U, I.id)) in
          instExp (depth, T, U', ac)
      | d, T, U, ac -> raise (Instance "Other Cases impossible\n")
    and instExp = function
      | d, T, U, ac ->
          S.insert rho_u (n, (d, U));
          ac
      | d, T, U, ac -> instRoot (d, I.Root (H1, S1), I.Root (H2, S2), ac)
      | d, I.Lam (D1, T1), I.Lam (D2, U2), ac -> instExp (d + 1, T1, U2, ac)
      | d, T, U, ac ->
          print "instExp -- falls through?\n";
          raise (Instance "Impossible\n")
    and instSpine = function
      | d, I.Nil, I.Nil, ac -> ac
      | d, I.App (T, S1), I.App (U, S2), ac ->
          let ac' = instExp (d, T, U, ac) in
          let ac'' = instSpine (d, S1, S2, ac') in
          ac''
      | d, I.Nil, I.App (_, _), ac ->
          print
            "Spines are not the same -- (first one is Nil) -- cannot happen!\n";
          raise (Instance "DifferentSpines\n")
      | d, I.App (_, _), I.Nil, ac ->
          print
            "Spines are not the same -- second one is Nil -- cannot happen!\n";
          raise (Instance "DifferentSpines\n")
      | d, I.SClo (_, _), _, ac ->
          print "Spine Closure!(1) -- cannot happen!\n";
          raise (Instance "DifferentSpines\n")
      | d, _, I.SClo (_, _), ac ->
          print "Spine Closure! (2) -- cannot happen!\n";
          raise (Instance " DifferentSpines\n")
    in
    (* by invariant dt = du *)
    ac := instExp (dt, T, U, !ac)
  (* if it succeeds then it will return a continuation which will
         instantiate the "evars" and rho_t will contain all
         nvar instantiations
         otherwise it will raise Instance *)

  let rec compHeads = function
    | (D_1, I.Const k), (D_2, I.Const k') -> k = k'
    | (D_1, I.Def k), (D_2, I.Def k') -> k = k'
    | (D_1, I.BVar k), (D_2, I.BVar k') -> (
        match isExists (0, I.BVar k, D_1) with
        | None -> k = k'
        | Some (x, Dec) -> true)
    | (D_1, I.BVar k), (D_2, H2) -> (
        match isExists (0, I.BVar k, D_1) with
        | None -> false
        | Some (x, Dec) -> true)
    | (D_1, H1), (D_2, H2) -> false

  let rec compatible' ((D_t, (dt, T)), (D_u, (du, U)), Ds, rho_t, rho_u) =
    let rec genNVar ((rho_t, T), (rho_u, U)) =
      S.insert rho_t (!nctr + 1, T);
      S.insert rho_u (!nctr + 1, U);
      (* by invariant dt = du *)
      newNVar ()
    in
    let rec genRoot = function
      | d, T, U ->
          if k = k' then
            let S' = genSpine (d, S1, S2) in
            I.Root (H1, S')
          else genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
      | d, T, U ->
          if k = k' then
            let S' = genSpine (d, S1, S2) in
            I.Root (H1, S')
          else (* could expand definitions here ? -bp*)
            genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
      | d, T, U ->
          if k > d && k' > d then (* globally bound variable *)
            let k1 = k - d in
            let k2 = k' - d in
            match (member (k1, D_t), member (k2, D_u)) with
            | None, None ->
                (* should never happen *)
                if k1 = k2 then
                  try
                    let S' = genSpine (d, S1, S2) in
                    I.Root (H1, S')
                  with DifferentSpine ->
                    genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
                else genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
            | Some (x, Dec1), Some (x', Dec2) ->
                (* k, k' refer to the existential *)
                if k1 = k2 && equalDec (Dec1, Dec2) then (
                  (* they refer to the same existential variable *)
                  (* this is unecessary -- since existential variables have the same type
                            and need to be fully applied in order, S1 = S2 *)
                  let S' = genSpine (d, S1, S2) in
                  delete (x, D_t);
                  delete (x', D_u);
                  insertList ((x, Dec1), Ds);
                  I.Root (H1, S'))
                else (* variant checking only *)
                  genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
            | _, _ -> genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
          else if
            (* locally bound variables *)
            k = k'
          then
            try
              let S' = genSpine (d, S1, S2) in
              I.Root (H1, S')
            with DifferentSpines -> genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
          else genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
      | d, T, U -> genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
      | d, T, U -> genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
      | d, T, U -> genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
    and genExp = function
      | d, T, U ->
          S.insert rho_u (n, (d, U));
          T
      | d, T, U -> genRoot (d, I.Root (H1, S1), I.Root (H2, S2))
      | d, I.Lam (D1, T1), I.Lam (D2, U2) ->
          let E = genExp (d + 1, T1, U2) in
          I.Lam (D1, E)
      | d, T, U ->
          print "genExp -- falls through?\n";
          genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
    and genSpine = function
      | d, I.Nil, I.Nil -> I.Nil
      | d, I.App (T, S1), I.App (U, S2) ->
          let E = genExp (d, T, U) in
          let S' = genSpine (d, S1, S2) in
          I.App (E, S')
      | d, I.Nil, I.App (_, _) -> raise DifferentSpines
      | d, I.App (_, _), I.Nil -> raise DifferentSpines
      | d, I.SClo (_, _), _ -> raise DifferentSpines
      | d, _, I.SClo (_, _) -> raise DifferentSpines
    in
    (* by invariant dt = du *)
    Variant (dt, genExp (dt, T, U))

  let rec compatible = function
    | (D_t, T), (D_u, U), Ds, rho_t, rho_u ->
        if compHeads ((D_t, H1), (D_u, H2)) then
          compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)
        else NotCompatible
    | (D_t, T), (D_u, U), Ds, rho_t, rho_u ->
        compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)
  (* compatibleCtx (asub, (Dsq, Gsq, eqn_sq), GR) = option

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

  let rec compatibleCtx = function
    | asub, (Dsq, Gsq, eqn_sq), [] -> None
    | ( asub,
        (Dsq, Gsq, eqn_sq),
        (_, Delta', G', eqn', answRef', _, status') :: GRlist ) ->
        if instanceCtx (asub, (Dsq, Gsq), (Delta', G')) then
          Some ((Delta', G', eqn'), answRef', status')
        else compatibleCtx (asub, (Dsq, Gsq, eqn_sq), GRlist)
  (* ---------------------------------------------------------------*)

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

  let rec instanceSub ((D_t, nsub_t), (Dsq, squery), asub) =
    (* by invariant rho_t = empty, since nsub_t <= squery *)
    let rho_u = nid () in
    let D_r2 = copy Dsq in
    let ac = ref (fun (asub : exSubsts) -> ()) in
    try
      S.forall squery (fun (nv, (du, U)) ->
          match S.lookup nsub_t nv with
          | Some (dt, T) ->
              (* note by invariant Glocal_e ~ Glocal_t *)
              (* [ac]T = U *)
              instance ((D_t, (dt, T)), (D_r2, (du, U)), rho_u, ac)
          (* if U is an instance of T then [ac][rc_u]T = U *)
          (* once the continuations ac are triggered *)
          | None -> S.insert rho_u (nv, (du, U)));
      !ac asub;
      InstanceSub (asub, (D_r2, rho_u))
    with Instance msg -> NoCompatibleSub
  (* [asub]nsub_t = sq  where sq is the query substitution *)

  let rec instChild = function
    | N, (D_sq, sq), asub -> instanceSub ((D_t, nsub_t), (D_sq, sq), asub)
    | N, (D_sq, sq), asub -> instanceSub ((D_t, nsub_t), (D_sq, sq), asub)

  let rec findAllInst (G_r, children, Ds, asub) =
    let rec findAllCands = function
      | G_r, [], (Dsq, sub_u), asub, IList -> IList
      | G_r, x :: L, (Dsq, sub_u), asub, IList -> (
          let asub' = S.copy asub in
          match instChild (!x, (Dsq, sub_u), asub) (* will update asub *) with
          | NoCompatibleSub -> findAllCands (G_r, L, (Dsq, sub_u), asub', IList)
          | InstanceSub (asub, Drho2) ->
              findAllCands
                (G_r, L, (Dsq, sub_u), asub', (x, Drho2, asub) :: IList))
    in
    findAllCands (G_r, children, Ds, asub, [])
  (* Solving  variable definitions *)

  (* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)

  let rec solveEqn = function
    | (T.Trivial, s), G -> true
    | (T.Unify (G', e1, N (* evar *), eqns), s), G ->
        let G'' = compose (G', G) in
        let s' = shift (G'', s) in
        Assign.unifiable (G'', (N, s'), (e1, s')) && solveEqn ((eqns, s), G)
  (* Mon Dec 27 11:57:35 2004 -bp *)

  (* solveEqn' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)

  let rec solveEqn' = function
    | (T.Trivial, s), G -> true
    | (T.Unify (G', e1, N (* evar *), eqns), s), G ->
        let G'' = compose (G', G) in
        let s' = shift (G', s) in
        Assign.unifiable (G'', (N, s'), (e1, s')) && solveEqn' ((eqns, s), G)
  (* Mon Dec 27 12:20:45 2004 -bp
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

  let rec solveEqnI' = function
    | (T.Trivial, s), G -> true
    | (T.Unify (G', e1, N (* evar *), eqns), s), G ->
        (* note: we check whether N[s'] is an instance of e1[s'] !!! *)
        (* at this point all AVars have been instantiated, and we could use Match.instance directly *)
        let G'' = compose (G', G) in
        let s' = shift (G', s) in
        Assign.instance (G'', (e1, s'), (N, s')) && solveEqnI' ((eqns, s), G)
  (* retrieve all Instances from substitution tree *)

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

  let rec retrieveInst (Nref, (Dq, sq), asub, GR) =
    let rec retrieve' = function
      | N, (Dq, sq), asubst, GR' -> (
          (* Dq = (Dsq' u Dg) where Dsq' = evars occurring in sq
                                      D_G = evars occuring in G_sq or only in eqn_sq

               and Dsq = D since there exists a path s1 ... sn from the root to the Leaf (D,s)
                 s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
             *)
          let Dsq, D_G = collectEVar Dq sq in
          match
            compatibleCtx (asubst, (D_G, G_r, eqn), !GRlistRef)
            (* compatibleCtx may destructively update asub ! *)
          with
          | None ->
              (* compatible path -- but different ctx *)
              raise (Instance "Compatible path -- different ctx\n")
          | Some ((D', G', eqn'), answRef', status') ->
              (* compatible path -- SAME ctx *)
              (* note: previously we checked eqn' = eqn! -- this is too restrictive
                 now - Dec  6 2004 -bp we check whether eqn is an instance of eqn'
                 note: this is very delicate code.
               *)
              (* Since there exists a path (D1, s1) ... (Dn,sn) from the root to the Leaf (D,s)
                   D1', ...., Dn', D, D' = D*
                   and          G' |- esub' : DAEVars, G'        and       .   |- esub : DAEVars
                        DAEVars, G |- asub' : D*, G'                   DAEVars |- asub : D*

                  note: asub' may refer to free variables which denote evars in D*
                        which only occur in eqn' and hence have not yet been instantiated
                        however: all avars in D* have been instantiated!
                 *)
              (* Residual equation of query:
                   DAEVars, G' |- eqn  hence we solve : G' |= [esub']eqn *)
              (*              val _ = if solveEqn' (eqn, esub)
                          then () else print " failed to solve eqn_query\n"  *)
              (* Residual equations in index:
                   D*, G' |- eqn'    where eqn' = AVar1 = E1 .... AVarn = En
                                      and  Ei may contain free variables
                      G'  |= [esub](asub) (eqn')

                      solve eqn' from path in index using instance or matching ONLY
                      to instantiate the free variables Ei

                   remark: DAEVars, G' |= [asub]eqn'   should work in theory too,
                           if the free variables in asub are created in such a way that they may depend on DAVars.
                           otherwise unification or instance checking will fail or the resulting instantiation
                           for_sml the free variables in asub is too restrictive, s.t. retrieval fails
                   *)
              let DAEVars = compose (DEVars, DAVars) in
              let esub = ctxToAVarSub (G', DAEVars, I.Shift 0) in
              let asub =
                convAssSub
                  ( G',
                    asubst,
                    I.ctxLength G' + 1,
                    D',
                    (I.ctxLength DAVars, I.ctxLength DEVars) )
              in
              let _ =
                if solveEqn' ((eqn, shift (G', esub)), G' (* = G_r *)) then ()
                else print " failed to solve eqn_query\n"
              in
              let easub = normalizeSub (I.comp (asub, esub)) in
              if solveEqnI' ((eqn', shift (G', easub)), G')
              (*              if solveEqnI' (eqn', easub) *)
              (* solve residual equations using higher-order matching Wed Dec 22 2004 -bp *)
              then T.RepeatedEntry ((esub, asub), answRef', status')
              else
                raise
                  (Instance "Compatible path -- resdidual equ. not solvable\n"))
      | N, (Dq, sq), asub, GR ->
          let InstCand = findAllInst (G_r, children, (Dq, sq), asub) in
          let rec checkCandidates = function
            | [] -> raise (Instance "No compatible child\n")
            | (ChildRef, Drho2, asub) :: ICands -> (
                try retrieve' (!ChildRef, Drho2, asub, GR)
                with Instance msg ->
                  (* print msg; *)
                  checkCandidates ICands)
          in
          checkCandidates InstCand
    in
    fun () -> ((), retrieve' (!Nref, (Dq, sq), asub, GR))
  (*---------------------------------------------------------------------------*)

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

  let rec compatibleSub ((D_t, nsub_t), (Dsq, squery)) =
    (* by invariant rho_t = empty, since nsub_t <= squery *)
    let sigma, rho_t, rho_u = (nid (), nid (), nid ()) in
    let Dsigma = emptyCtx () in
    let D_r1 = copy D_t in
    let D_r2 = copy Dsq in
    let choose = ref (fun match_ : bool -> ()) in
    let _ =
      S.forall squery (fun nv U ->
          match S.lookup nsub_t nv with
          | Some T -> (
              (* note by invariant Glocal_e ~ Glocal_t *)
              match compatible ((D_r1, T), (D_r2, U), Dsigma, rho_t, rho_u) with
              | NotCompatible ->
                  S.insert rho_t (nv, T);
                  S.insert rho_u (nv, U)
              | Variant T' ->
                  let restc = !choose in
                  S.insert sigma (nv, T');
                  choose :=
                    fun match_ ->
                      restc match_;
                      if match_ then () else ()
                  (* here Glocal_t will be only approximately correct! *))
          | None -> S.insert rho_u (nv, U))
    in
    if isId rho_t then (
      (* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
      !choose true;
      VariantSub (D_r2, rho_u))
    else (
      (* split -- asub is unchanged *)
      !choose false;
      if isId sigma then NoCompatibleSub
      else SplitSub ((Dsigma, sigma), (D_r1, rho_t), (D_r2, rho_u)))
  (* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
  (* ---------------------------------------------------------------------- *)

  (*  fun mkLeaf (Ds, GR, n) = Leaf (Ds, GR)*)

  let rec mkNode = function
    | Node (_, Children), Dsigma, Drho1, GR, Drho2 ->
        let D_rho2, D_G2 = collectEVar D2 rho2 in
        let GR' = ((evarl, l), D_G2, dp, eqn, answRef, stage, status) in
        let sizeSigma, sizeRho1, sizeRho2 =
          (S.size sigma, S.size rho1, S.size rho2)
        in
        Node
          ( Dsigma,
            [
              ref (Leaf ((D_rho2, rho2), ref [ GR' ]));
              ref (Node (Drho1, Children));
            ] )
    | Leaf (c, GRlist), Dsigma, Drho1, GR2, Drho2 ->
        let D_rho2, D_G2 = collectEVar D2 rho2 in
        let GR2' = ((evarl, l), D_G2, dp, eqn, answRef, stage, status) in
        Node
          ( Dsigma,
            [
              ref (Leaf ((D_rho2, rho2), ref [ GR2' ]));
              ref (Leaf (Drho1, GRlist));
            ] )
  (* ---------------------------------------------------------------------- *)

  let rec compChild = function
    | N, (D_e, nsub_e) -> compatibleSub ((D_t, nsub_t), (D_e, nsub_e))
    | N, (D_e, nsub_e) -> compatibleSub ((D_t, nsub_t), (D_e, nsub_e))

  let rec findAllCandidates G_r children Ds =
    let rec findAllCands = function
      | G_r, [], (Dsq, sub_u), VList, SList -> (VList, SList)
      | G_r, x :: L, (Dsq, sub_u), VList, SList -> (
          match compChild (!x, (Dsq, sub_u)) with
          | NoCompatibleSub -> findAllCands (G_r, L, (Dsq, sub_u), VList, SList)
          | SplitSub (Dsigma, Drho1, Drho2) ->
              findAllCands
                ( G_r,
                  L,
                  (Dsq, sub_u),
                  VList,
                  (x, (Dsigma, Drho1, Drho2)) :: SList )
          | VariantSub Drho2 ->
              findAllCands
                (G_r, L, (Dsq, sub_u), (x, Drho2, I.id) :: VList, SList))
    in
    findAllCands (G_r, children, Ds, [], [])
  (* ---------------------------------------------------------------------- *)

  let rec divergingCtx stage G GRlistRef =
    (* this 3 is arbitrary -- lockstep *)
    let l = I.ctxLength G + 3 in
    List.exists
      (fun ((_, l), D, G', _, _, stage', _) ->
        stage = stage' && l > I.ctxLength G')
      !GRlistRef

  let rec eqHeads = function
    | I.Const k, I.Const k' -> k = k'
    | I.BVar k, I.BVar k' -> k = k'
    | I.Def k, I.Def k' -> k = k'
    | _, _ -> false
  (* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1]
  t2 is a linear term which may not contain any nvars!
  t may contain nvars
 *)

  let rec eqTerm = function
    | I.Root (H2, S2), (t, rho1) ->
        if eqHeads (H2, H) then eqSpine (S2, (S, rho1)) else false
    | T2, (I.NVar n, rho1) -> (
        match S.lookup rho1 n with
        | None -> false
        | Some (dt1, T1) -> eqTerm (T2, (T1, nid ())))
    | I.Lam (D2, T2), (I.Lam (D, T), rho1) -> eqTerm (T2, (T, rho1))
    | _, (_, _) -> false

  and eqSpine = function
    | I.Nil, (I.Nil, rho1) -> true
    | I.App (T2, S2), (I.App (T, S), rho1) ->
        eqTerm (T2, (T, rho1)) && eqSpine (S2, (S, rho1))

  let rec divergingSub ((Ds, sigma), (Dr1, rho1), (Dr2, rho2)) =
    S.exists rho2 (fun (n2, (dt2, t2)) ->
        S.exists sigma (fun (_, (d, t)) -> eqTerm (t2, (t, rho1))))
  (* ---------------------------------------------------------------------- *)

  (* Insert via variant checking *)

  let rec variantCtx = function
    | (G, eqn), [] -> None
    | (G, eqn), (l', D_G, G', eqn', answRef', _, status') :: GRlist ->
        if equalCtx' (G, G') && equalEqn (eqn, eqn') then
          Some (l', answRef', status')
        else variantCtx ((G, eqn), GRlist)
  (* insert (Nref, (Dq, sq), GR) = TableResult *)

  let rec insert (Nref, (Dsq, sq), GR) =
    let rec insert' = function
      | N, (Dsq, sq), GR -> (
          match variantCtx ((G_r, eqn), !GRlistRef) with
          | None ->
              (* compatible path -- but different ctx! *)
              (* D_G contains evars occurring only in eqn or G
                        D_nsub contains evars occurring only in sq
                        furthermore: D_nsub = D where Leaf((D,s), GRlistRef)
                     *)
              let D_nsub, D_G = collectEVar Dsq sq in
              let GR' = (l, D_G, G_r, eqn, answRef, stage, status) in
              fun () ->
                ( (GRlistRef := GR' :: !GRlistRef;
                   answList := answRef :: !answList),
                  T.NewEntry answRef )
          | Some (_, answRef', status') ->
              ( (* compatible path -- SAME ctx and SAME eqn!
                                          this implies: SAME D_G *)
                (fun () -> ()),
                T.RepeatedEntry ((I.id, I.id), answRef', status') ))
      | N, (Dsq, sq), GR ->
          let VariantCand, SplitCand =
            findAllCandidates (G_r, children, (Dsq, sq))
          in
          let D_nsub, D_G = collectEVar Dsq sq in
          let GR' = (l, D_G, G_r, eqn, answRef, stage, status) in
          let rec checkCandidates = function
            | [], [] ->
                fun () ->
                  ( (Nref :=
                       Node
                         ( (D, sub),
                           ref (Leaf ((D_nsub, sq), ref [ GR' ])) :: children );
                     answList := answRef :: !answList),
                    T.NewEntry answRef )
            | [], (ChildRef, (Dsigma, Drho1, Drho2)) :: _ ->
                if
                  !TableParam.divHeuristic && divergingSub (Dsigma, Drho1, Drho2)
                then
                  fun (* substree diverging -- splitting node *)
                        ()
                  ->
                  ( (ChildRef := mkNode (!ChildRef, Dsigma, Drho1, GR, Drho2);
                     answList := answRef :: !answList),
                    T.DivergingEntry (I.id, answRef) )
                else
                  fun (* split existing node *)
                        ()
                  ->
                  ( (ChildRef := mkNode (!ChildRef, Dsigma, Drho1, GR, Drho2);
                     answList := answRef :: !answList),
                    T.NewEntry answRef )
            | (ChildRef, Drho2, asub) :: [], _ -> insert (ChildRef, Drho2, GR)
            | (ChildRef, Drho2, asub) :: L, SCands -> (
                match insert (ChildRef, Drho2, GR) with
                | _, T.NewEntry answRef -> checkCandidates (L, SCands)
                | f, T.RepeatedEntry (asub, answRef, status) ->
                    (f, T.RepeatedEntry (asub, answRef, status))
                | f, T.DivergingEntry (asub, answRef) ->
                    (f, T.DivergingEntry (asub, answRef)))
          in
          checkCandidates (VariantCand, SplitCand)
    in
    insert' (!Nref, (Dsq, sq), GR)
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
         Sideeffect: update answer list for_sml U
     *)

  let rec answCheckVariant s' answRef O =
    let rec member = function
      | (D, sk), [] -> false
      | (D, sk), ((D1, s1), _) :: S ->
          if equalSub (sk, s1) && equalCtx' (D, D1) then true
          else member ((D, sk), S)
    in
    let DEVars, sk = A.abstractAnswSub s' in
    if member ((DEVars, sk), T.solutions answRef) then T.repeated
    else (
      T.addSolution (((DEVars, sk), O), answRef);
      T.new_)
  (* ---------------------------------------------------------------------- *)

  let rec reset () =
    nctr := 1;
    (* Reset Subsitution Tree *)
    Array.modify
      (fun n Tree ->
        n := 0;
        Tree := !(makeTree ());
        answList := [];
        added := false;
        (n, Tree))
      indexArray
  (* makeCtx (n, G, G') =  unit
     if G LF ctx
     then
      G' is a set
      where (i,Di) corresponds to the i-th declaration in G

    note: G' is destructively updated
    *)

  let rec makeCtx = function
    | ((n, I.Null, DEVars) : ctx) -> ()
    | ((n, I.Decl (G, D), DEVars) : ctx) ->
        insertList ((n, D), DEVars);
        makeCtx (n + 1, G, DEVars)
  (* callCheck (a, DAVars, DEVars, G, U, eqn, status) = TableResult
    if
      U is atomic (or base type) i.e. U = a S

      DAVars, DEVars, G |- U
      DAVars, DEVars, G |- eqn

      Tree is the substitution trie associated with type family a

   then
      if there exists a path r1 o r2 o ... o rn = p in Tree
         together with some (G',eqn', answRef') at the Leaf
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
           together with (G,eqn, answRef) at the Leaf

   *)

  let rec callCheck (a, DAVars, DEVars, G, U, eqn, status) =
    (* n = |G| *)
    (* Dq = DAVars, DEVars *)
    (* l = |D| *)
    let n, Tree = Array.sub (indexArray, a) in
    let sq = S.new_ () in
    let DAEVars = compose (DEVars, DAVars) in
    let Dq = emptyCtx () in
    let n = I.ctxLength G in
    let _ = makeCtx (n + 1, DAEVars, (Dq : ctx)) in
    let l = I.ctxLength DAEVars in
    let _ = S.insert sq (1, (0, U)) in
    let GR =
      ((l, n + 1), G, eqn, emptyAnswer (), !TableParam.stageCtr, status)
    in
    let GR' = ((DEVars, DAVars), G, eqn, !TableParam.stageCtr, status) in
    let result =
      try retrieveInst (Tree, (Dq, sq), asid () (* assignable subst *), GR')
      with Instance msg ->
        (* sq not in index --> insert it *)
        insert (Tree, (Dq, sq), GR)
    in
    match result with
    | sf, T.NewEntry answRef ->
        sf ();
        added := true;
        T.NewEntry answRef
    | _, T.RepeatedEntry (asub, answRef, status) ->
        T.RepeatedEntry (asub, answRef, status)
    | sf, T.DivergingEntry (asub, answRef) ->
        sf ();
        added := true;
        T.DivergingEntry (asub, answRef)
  (* we assume we alsways insert new things into the tree *)

  let rec insertIntoTree (a, DAVars, DEVars, G, U, eqn, answRef, status) =
    (* sq = query substitution *)
    let n, Tree = Array.sub (indexArray, a) in
    let sq = S.new_ () in
    let DAEVars = compose (DEVars, DAVars) in
    let Dq = emptyCtx () in
    let n = I.ctxLength G in
    let _ = makeCtx (n + 1, DAEVars, (Dq : ctx)) in
    let l = I.ctxLength DAEVars in
    let _ = S.insert sq (1, (0, U)) in
    let GR =
      ((l, n + 1), G, eqn, emptyAnswer (), !TableParam.stageCtr, status)
    in
    let result =
      insert
        ( Tree,
          (Dq, sq),
          ((l, n + 1), G, eqn, answRef, !TableParam.stageCtr, status) )
    in
    match result with
    | sf, T.NewEntry answRef ->
        sf ();
        added := true;
        T.NewEntry answRef
    | _, T.RepeatedEntry (asub, answRef, status) ->
        T.RepeatedEntry (asub, answRef, status)
    | sf, T.DivergingEntry (asub, answRef) ->
        sf ();
        added := true;
        T.DivergingEntry (asub, answRef)

  let rec answCheck s' answRef O = answCheckVariant s' answRef O

  let rec updateTable () =
    let rec update = function
      | [], Flag -> Flag
      | answRef :: AList, Flag ->
          let l = length (T.solutions answRef) in
          if l = T.lookup answRef then
            (* no new solutions were added in the previous stage *)
            update AList Flag
          else (* new solutions were added *)
            (
            T.updateAnswLookup (l, answRef);
            update AList true)
    in
    let Flag = update !answList false in
    let r = Flag || !added in
    added := false;
    r

  let reset = reset

  let callCheck =
   fun (DAVars, DEVars, G, U, eqn, status) ->
    callCheck (cidFromHead (I.targetHead U), DAVars, DEVars, G, U, eqn, status)

  let insertIntoTree =
   fun (DAVars, DEVars, G, U, eqn, answRef, status) ->
    insertIntoTree
      (cidFromHead (I.targetHead U), DAVars, DEVars, G, U, eqn, answRef, status)

  let answerCheck = answCheck
  let updateTable = updateTable
  let tableSize = fun () -> length !answList
  (* memberCtxS ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t.  V'[^n]  is an instance of V
       then return true
         otherwise false
    *)

  let rec memberCtx ((G, V), G') =
    let rec instanceCtx' = function
      | (G, V), I.Null, n -> None
      | (G, V), I.Decl (G', D'), n ->
          if Match.instance (G, (V, I.id), (V', I.Shift n)) then Some D'
          else instanceCtx' ((G, V), G', n + 1)
    in
    instanceCtx' ((G, V), G', 1)
  (* local *)
end

(* functor MemoTable *)
