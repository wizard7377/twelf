(* Search (based on abstract machine ) *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) OLDSearch ((*! structure IntSyn' : INTSYN !*)
                structure MetaGlobal : METAGLOBAL
                structure MetaSyn' : METASYN
                (*! sharing MetaSyn'.IntSyn = IntSyn' !*)
                (*! structure CompSyn' : COMPSYN !*)
                (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                structure Whnf : WHNF
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                structure Unify : UNIFY
                (*! sharing Unify.IntSyn = IntSyn' !*)
                (*
                structure Assign : ASSIGN
                sharing Assign.IntSyn = IntSyn'
                *)
                structure Index : INDEX
                (*! sharing Index.IntSyn = IntSyn' !*)
                structure Compile : COMPILE
                (*! sharing Compile.IntSyn = IntSyn' !*)
                (*! sharing Compile.CompSyn = CompSyn' !*)
                structure CPrint : CPRINT
                (*! sharing CPrint.IntSyn = IntSyn' !*)
                (*! sharing CPrint.CompSyn = CompSyn' !*)
                structure Print : PRINT
                (*! sharing Print.IntSyn = IntSyn' !*)
                structure Names : NAMES
                (*! sharing Names.IntSyn = IntSyn' !*)
                (*! structure CSManager : CS_MANAGER !*)
                (*! sharing CSManager.IntSyn = IntSyn' !*)
)
  : OLDSEARCH =
struct

  (*! structure IntSyn = IntSyn' !*)
  structure MetaSyn = MetaSyn'
  (*! structure CompSyn = CompSyn' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure M = MetaSyn
    structure C = CompSyn


  fun (* GEN BEGIN FUN FIRST *) cidFromHead (I.Const a) = a (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) cidFromHead (I.Def a) = a (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) cidFromHead (I.Skonst a) = a (* GEN END FUN BRANCH *)

  (* only used for type families of compiled clauses *)
  fun (* GEN BEGIN FUN FIRST *) eqHead (I.Const a, I.Const a') = a = a' (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eqHead (I.Def a, I.Def a') = a = a' (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eqHead _ = false (* GEN END FUN BRANCH *)

  (* solve ((g,s), (G,dPool), sc, (acc, k)) => ()
     Invariants:
       G |- s : G'
       G' |- g :: goal
       G ~ dPool  (context G matches dPool)
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if  G |- M :: g[s] then G |- sc :: g[s] => Answer, Answer closed
  *)
  fun (* GEN BEGIN FUN FIRST *) solve ((C.Atom p, s), dp, sc, acck) = matchAtom ((p,s), dp, sc, acck) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) solve ((C.Impl (r, A, H, g), s), C.DProg(G, dPool), sc, acck) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.Dec (NONE, I.EClo (A, s)) (* GEN END TAG OUTSIDE LET *)
       in
         solve ((g, I.dot1 s),
                C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, H))),
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn (M, acck') => sc (I.Lam (D', M), acck') (* GEN END FUNCTION EXPRESSION *)), acck)
       end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) solve ((C.All (D, g), s), C.DProg (G, dPool), sc, acck) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.decSub (D, s) (* GEN END TAG OUTSIDE LET *)
       in
         solve ((g, I.dot1 s),
                C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)),
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn (M, acck') => sc (I.Lam (D', M), acck') (* GEN END FUNCTION EXPRESSION *)), acck)
       end (* GEN END FUN BRANCH *)

  (* rsolve ((p,s'), (r,s), (G,dPool), sc, (acc, k)) = ()
     Invariants:
       G |- s : G'
       G' |- r :: resgoal
       G |- s' : G''
       G'' |- p :: atom
       G ~ dPool
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if G |- S :: r[s] then G |- sc : (r >> p[s']) => Answer
  *)
  and (* GEN BEGIN FUN FIRST *) rSolve (ps', (C.Eq Q, s), C.DProg (G, dPool), sc, acck as (acc, k)) =
      if Unify.unifiable (G, ps', (Q, s))
        then sc (I.Nil, acck)
      else acc (* GEN END FUN FIRST *)
      (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
    (*
    | rSolve (ps', (C.Assign (Q, ag), s), dp, sc, acck as (acc, k)) =
        ((Assign.assign (ps', (Q, s));
          aSolve ((ag, s), dp, (fn () => sc (I.Nil, acck)) , acc))
          handle Unify.Unify _ => acc
               | Assign.Assign _ => acc)
    *)
    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.And (r, A, g), s), dp as C.DProg (G, dPool), sc, acck) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo(A, s)) (* GEN END TAG OUTSIDE LET *)
      in
        rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp,
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn (S, acck') => solve ((g, s), dp,
                                         ((* GEN BEGIN FUNCTION EXPRESSION *) fn (M, acck'') => ((Unify.unify (G, (X, I.id), (M, I.id));
                                                             (* why doesn't it always succeed?
                                                                --cs *)
                                                             sc (I.App (M, S), acck''))
                                                             handle Unify.Unify _ => []) (* GEN END FUNCTION EXPRESSION *)),
                                         acck') (* GEN END FUNCTION EXPRESSION *)), acck)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.Exists (I.Dec (_, A), r), s), dp as C.DProg (G, dPool), sc, acck) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (A, s)) (* GEN END TAG OUTSIDE LET *)
        in
          rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp,
                  ((* GEN BEGIN FUNCTION EXPRESSION *) fn (S, acck') => sc (I.App (X, S), acck') (* GEN END FUNCTION EXPRESSION *)), acck)
        end (* GEN END FUN BRANCH *)
(*    | rSolve (ps', (C.Axists (I.Dec (_, A), r), s), dp as C.DProg (G, dPool), sc, acck) =
        let
          val X = I.newEVar (G, I.EClo (A, s))
        in
          rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp,
                  (fn (S, acck') => sc (S, acck')), acck)
        end
*)
  (* aSolve ... *)
  and aSolve ((C.Trivial, s), dp, sc, acc) = sc ()
    (* Fri Jan 15 16:04:39 1999 -fp,cs
    | aSolve ((C.Unify(I.Eqn(e1, e2), ag), s), dp, sc, acc) =
      ((Unify.unify ((e1, s), (e2, s));
        aSolve ((ag, s), dp, sc, acc))
       handle Unify.Unify _ => acc)
     *)

  (* matchatom ((p, s), (G, dPool), sc, (acc, k)) => ()
     G |- s : G'
     G' |- p :: atom
     G ~ dPool
     acc is the accumulator of results
     and k is the max search depth limit
         (used in the existential case for iterative deepening,
          used in the universal case for max search depth)
     if G |- M :: p[s] then G |- sc :: p[s] => Answer
  *)
  and matchAtom (ps' as (I.Root (Ha, _), _),
                 dp as C.DProg (G, dPool), sc, (acc, k)) =
      let
        fun matchSig acc' =
            let
              fun (* GEN BEGIN FUN FIRST *) matchSig' (nil, acc'') = acc'' (* GEN END FUN FIRST *)
                | (* GEN BEGIN FUN BRANCH *) matchSig' (Hc ::sgn', acc'') =
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val C.SClause(r) = C.sProgLookup (cidFromHead Hc) (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val acc''' = CSManager.trail
                                 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                                    rSolve (ps', (r, I.id), dp,
                                            ((* GEN BEGIN FUNCTION EXPRESSION *) fn (S, acck') => sc (I.Root (Hc, S),
                                                                  acck') (* GEN END FUNCTION EXPRESSION *)), (acc'', k-1)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
                  in
                    matchSig' (sgn', acc''')
                  end (* GEN END FUN BRANCH *)
            in
              matchSig' (Index.lookup (cidFromHead Ha), acc')
            end
  
        fun (* GEN BEGIN FUN FIRST *) matchDProg (I.Null, _, acc') = matchSig acc' (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.Dec (r, s, Ha')), n, acc') =
            if eqHead (Ha, Ha') then
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val acc'' = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                            rSolve (ps', (r, I.comp (s, I.Shift n)), dp,
                                    ((* GEN BEGIN FUNCTION EXPRESSION *) fn (S, acck') => sc (I.Root (I.BVar n, S),
                                                          acck') (* GEN END FUNCTION EXPRESSION *)), (acc', k-1)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
              in
                matchDProg (dPool', n+1, acc'')
              end
            else matchDProg (dPool', n+1, acc') (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.Parameter), n, acc') =
              matchDProg (dPool', n+1, acc') (* GEN END FUN BRANCH *)
      in
        if k < 0 then acc else matchDProg (dPool, 1, acc)
      end


    (* occursInExp (r, (U, s)) = B,

       Invariant:
       If    G |- s : G1   G1 |- U : V
       then  B holds iff r occurs in (the normal form of) U
    *)
    fun occursInExp (r, Vs) = occursInExpW (r, Whnf.whnf Vs)

    and (* GEN BEGIN FUN FIRST *) occursInExpW (r, (I.Uni _, _)) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInExpW (r, (I.Pi ((D, _), V), s)) =
          occursInDec (r, (D, s)) orelse occursInExp (r, (V, I.dot1 s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExpW (r, (I.Root (_, S), s)) = occursInSpine (r, (S, s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExpW (r, (I.Lam (D, V), s)) =
          occursInDec (r, (D, s)) orelse occursInExp (r, (V, I.dot1 s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExpW (r, (I.EVar (r' , _, V', _), s)) =
          (r = r') orelse occursInExp (r, (V', s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExpW (r, (I.FgnExp csfe, s)) =
        I.FgnExpStd.fold csfe ((* GEN BEGIN FUNCTION EXPRESSION *) fn (U,B) => B orelse occursInExp (r, (U,s)) (* GEN END FUNCTION EXPRESSION *)) false (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) occursInSpine (_, (I.Nil, _)) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInSpine (r, (I.SClo (S, s'), s)) =
          occursInSpine (r, (S, I.comp (s', s))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInSpine (r, (I.App (U, S), s)) =
          occursInExp (r, (U, s)) orelse occursInSpine (r, (S, s)) (* GEN END FUN BRANCH *)

    and occursInDec (r, (I.Dec (_, V), s)) = occursInExp (r, (V, s))

    (* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)
    fun (* GEN BEGIN FUN FIRST *) nonIndex (_, nil) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) nonIndex (r, I.EVar (_, _, V, _) :: GE) =
          (not (occursInExp (r, (V, I.id)))) andalso nonIndex (r, GE) (* GEN END FUN BRANCH *)

    (* select (GE, (V, s), acc) = acc'

       Invariant:
       If   GE is a list of Evars
       and  G |- s : G'   G' |- V : L
       then acc' is a list of EVars (G', X') s.t.
         (0) it extends acc'
         (1) (G', X') occurs in V[s]
         (2) (G', X') is not an index Variable to any (G, X) in acc'.
    *)
    (* Efficiency: repeated whnf for every subterm in Vs!!! *)

    fun (* GEN BEGIN FUN FIRST *) selectEVar (nil, _, acc) = acc (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) selectEVar ((X as I.EVar (r, _, _, _)) :: GE, Vs, acc) =
          if occursInExp (r, Vs) andalso nonIndex (r, acc) then
            selectEVar (GE, Vs, X :: acc)
          else selectEVar (GE, Vs, acc) (* GEN END FUN BRANCH *)



    (* searchEx' max (GE, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)
    (* contexts of EVars are recompiled for each search depth *)
    fun (* GEN BEGIN FUN FIRST *) searchEx' max (nil, sc) = [sc ()] (* GEN END FUN FIRST *)
        (* Possible optimization:
           Check if there are still variables left over
        *)
      | (* GEN BEGIN FUN BRANCH *) searchEx' max (I.EVar (r, G, V, _) :: GE, sc) =
          solve ((Compile.compileGoal (G, V), I.id),
                 Compile.compileCtx false G,
                 ((* GEN BEGIN FUNCTION EXPRESSION *) fn (U', (acc', _)) => (Unify.instantiateEVar (r, U', nil);
                                         searchEx' max (GE, sc)) (* GEN END FUNCTION EXPRESSION *)),
                 (nil, max)) (* GEN END FUN BRANCH *)

    (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MetaGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MetaGlobal.maxLevel
    *)
    fun deepen f P =
        let
          fun deepen' (level, acc) =
            if level > (!MetaGlobal.maxFill) then acc
            else (if !Global.chatter > 5 then print "#" else ();
                    deepen' (level+1, f level P))
        in
          deepen' (1, nil)
        end

    (* searchEx (G, GE, (V, s), sc) = acc'
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list containing the one result from executing the success continuation
         All EVar's got instantiated with the smallest possible terms.
    *)
    fun searchEx (G, GE, Vs, sc) =
      (if !Global.chatter > 5 then print "[Search: " else ();
         deepen searchEx' (selectEVar (GE, Vs, nil),
                           (* GEN BEGIN FUNCTION EXPRESSION *) fn Params => (if !Global.chatter > 5 then
                                            print "OK]\n" else ();
                                          sc Params) (* GEN END FUNCTION EXPRESSION *));
         if !Global.chatter > 5 then print "FAIL]\n" else ();
           raise Error "No object found")

    (* searchAll' (GE, acc, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  acc is list of already collected results of the success continuation
       then acc' is an extension of acc', containing the results of sc
         after trying all combinations of instantiations of EVars in GE
    *)
    (* Shared contexts of EVars in GE may recompiled many times *)

    fun (* GEN BEGIN FUN FIRST *) searchAll' (nil, acc, sc) = sc (acc) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) searchAll' (I.EVar (r, G, V, _) :: GE, acc, sc) =
          solve ((Compile.compileGoal (G, V), I.id),
                 Compile.compileCtx false G,
                 ((* GEN BEGIN FUNCTION EXPRESSION *) fn (U', (acc', _)) => (Unify.instantiateEVar (r, U', nil);
                                         searchAll' (GE, acc', sc)) (* GEN END FUNCTION EXPRESSION *)),
                 (acc, !MetaGlobal.maxFill)) (* GEN END FUN BRANCH *)

    (* searchAll (G, GE, (V, s), sc) = acc'

       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list of results from executing the success continuation
    *)
    fun searchAll (G, GE, Vs, sc) =
          searchAll' (selectEVar (GE, Vs, nil), nil, sc)


  in
    (* GEN BEGIN TAG OUTSIDE LET *) val searchEx = searchEx (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val searchAll = searchAll (* GEN END TAG OUTSIDE LET *)
  end (* local ... *)

end (* GEN END FUNCTOR DECL *); (* functor Search *)

