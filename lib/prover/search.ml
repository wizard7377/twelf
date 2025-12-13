(* Search (based on abstract machine ) : Version 1.3 *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Search
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (*! sharing Abstract.Tomega = Tomega' !*)
   structure Data : DATA
   structure CompSyn' : COMPSYN
   (*! sharing CompSyn'.IntSyn = IntSyn' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)
   structure Assign : ASSIGN
   (*! sharing Assign.IntSyn = IntSyn' !*)
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
   structure CSManager : CS_MANAGER
   (*! sharing CSManager.IntSyn = IntSyn' !*)
       )
     : SEARCH =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'
  (*! structure CompSyn = CompSyn' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure C = CompSyn


    (* isInstantiated (V) = SOME(cid) or NONE
       where cid is the type family of the atomic target type of V,
       NONE if V is a kind or object or have variable type.
    *)
    fun (* GEN BEGIN FUN FIRST *) isInstantiated (I.Root (I.Const(cid), _)) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isInstantiated (I.Pi(_, V)) = isInstantiated V (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isInstantiated (I.Root (I.Def(cid), _)) = true (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isInstantiated (I.Redex (V, S)) = isInstantiated V (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isInstantiated (I.Lam (_, V)) = isInstantiated V (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isInstantiated (I.EVar (ref (SOME(V)),_,_,_)) = isInstantiated V (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isInstantiated (I.EClo (V, s)) = isInstantiated V (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isInstantiated _ = false (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) compose'(IntSyn.Null, G) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) compose'(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose'(G, G'), D) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) shift (IntSyn.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s)) (* GEN END FUN BRANCH *)


    (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
    fun exists P K =
        let fun (* GEN BEGIN FUN FIRST *) exists' (I.Null) = false (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) exists' (I.Decl(K',Y)) = P(Y) orelse exists' (K') (* GEN END FUN BRANCH *)
        in
          exists' K
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
(*      | occursInExpW (r, (I.FgnExp (cs, ops), s)) =
          occursInExp (r, (#toInternal(ops)(), s)) *)
          (* hack - should consult cs  -rv *)

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
    *)
    (* Efficiency: repeated whnf for every subterm in Vs!!! *)
    fun (* GEN BEGIN FUN FIRST *) selectEVar (nil) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) selectEVar ((X as I.EVar (r, _, _, ref nil)) :: GE) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Xs = selectEVar (GE) (* GEN END TAG OUTSIDE LET *)
        in
          if nonIndex (r, Xs) then Xs @ [X]
          else Xs
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) selectEVar ((X as I.EVar (r, _, _, cnstrs)) :: GE) =  (* Constraint case *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Xs = selectEVar (GE) (* GEN END TAG OUTSIDE LET *)
        in
          if nonIndex (r, Xs) then X :: Xs
          else Xs
        end (* GEN END FUN BRANCH *)


    (* pruneCtx (G, n) = G'

       Invariant:
       If   |- G ctx
       and  G = G0, G1
       and  |G1| = n
       then |- G' = G0 ctx
    *)
    fun (* GEN BEGIN FUN FIRST *) pruneCtx (G, 0) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) pruneCtx (I.Decl (G, _), n) = pruneCtx (G, n-1) (* GEN END FUN BRANCH *)

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
  fun (* GEN BEGIN FUN FIRST *) solve (max, depth, (C.Atom p, s), dp, sc) = matchAtom (max, depth, (p,s), dp, sc) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) solve (max, depth, (C.Impl (r, A, Ha, g), s), C.DProg (G, dPool), sc) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.Dec (NONE, I.EClo (A, s)) (* GEN END TAG OUTSIDE LET *)
       in
         solve (max, depth+1, (g, I.dot1 s),
                C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn M => sc (I.Lam (D', M)) (* GEN END FUNCTION EXPRESSION *)))
       end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) solve (max, depth, (C.All (D, g), s), C.DProg (G, dPool), sc) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.decSub (D, s) (* GEN END TAG OUTSIDE LET *)
       in
         solve (max, depth+1, (g, I.dot1 s),
                C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)),
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn M => sc (I.Lam (D', M)) (* GEN END FUNCTION EXPRESSION *)))
       end (* GEN END FUN BRANCH *)

  (* rsolve (max, depth, (p,s'), (r,s), (G,dPool), sc, (acc, k)) = ()
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
  and (* GEN BEGIN FUN FIRST *) rSolve (max, depth, ps', (C.Eq Q, s), C.DProg (G, dPool), sc) =
      if Unify.unifiable (G, ps', (Q, s))
        then sc I.Nil
      else () (* GEN END FUN FIRST *)
      (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)

    | (* GEN BEGIN FUN BRANCH *) rSolve (max, depth, ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc) =
         (case Assign.assignable (G, ps', (Q, s))
            of SOME(cnstr) =>
               aSolve((eqns, s), dp, cnstr, ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => sc I.Nil (* GEN END FUNCTION EXPRESSION *)))
             | NONE => ()) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) rSolve (max, depth, ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
        (* is this EVar redundant? -fp *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo(A, s)) (* GEN END TAG OUTSIDE LET *)
      in
        rSolve (max, depth, ps', (r, I.Dot(I.Exp(X), s)), dp,
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => solve (max, depth, (g, s), dp,
                                ((* GEN BEGIN FUNCTION EXPRESSION *) fn M => sc (I.App (M, S)) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *)))
    
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) rSolve (max, depth, ps', (C.In (r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
                                        (* G |- g goal *)
                                        (* G |- A : type *)
                                        (* G, A |- r resgoal *)
                                        (* G0, Gl  |- s : G *)
        (* GEN BEGIN TAG OUTSIDE LET *) val G0 = pruneCtx (G, depth) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val dPool0 = pruneCtx (dPool, depth) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val w = I.Shift (depth) (* GEN END TAG OUTSIDE LET *)         (* G0, Gl  |- w : G0 *)
        (* GEN BEGIN TAG OUTSIDE LET *) val iw = Whnf.invert w (* GEN END TAG OUTSIDE LET *)
                                        (* G0 |- iw : G0, Gl *)
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = I.comp (s, iw) (* GEN END TAG OUTSIDE LET *)
                                        (* G0 |- w : G *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G0, I.EClo(A, s')) (* GEN END TAG OUTSIDE LET *)
                                        (* G0 |- X : A[s'] *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X' = I.EClo (X, w) (* GEN END TAG OUTSIDE LET *)
                                        (* G0, Gl |- X' : A[s'][w] = A[s] *)
      in
        rSolve (max, depth, ps', (r, I.Dot (I.Exp (X'), s)), dp,
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn S =>
                 if isInstantiated X then sc (I.App (X', S))
                 else  solve (max, 0, (g, s'), C.DProg (G0, dPool0),
                              ((* GEN BEGIN FUNCTION EXPRESSION *) fn M =>
                               ((Unify.unify (G0, (X, I.id), (M, I.id));
                                 sc (I.App (I.EClo (M, w), S)))
                                handle Unify.Unify _ => ()) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *)))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) rSolve (max, depth, ps', (C.Exists (I.Dec (_, A), r), s), dp as C.DProg (G, dPool), sc) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (A, s)) (* GEN END TAG OUTSIDE LET *)
        in
          rSolve (max, depth, ps', (r, I.Dot (I.Exp (X), s)), dp,
                  ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc (I.App (X, S)) (* GEN END FUNCTION EXPRESSION *)))
        end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) rSolve (max, depth, ps', (C.Axists(I.ADec(SOME(X), d), r), s), dp as C.DProg (G, dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X' = I.newAVar () (* GEN END TAG OUTSIDE LET *)
      in
        rSolve (max, depth, ps', (r, I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s)), dp, sc)
        (* we don't increase the proof term here! *)
      end (* GEN END FUN BRANCH *)

  (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)

  and (* GEN BEGIN FUN FIRST *) aSolve ((C.Trivial, s), dp, cnstr, sc) =
        (if Assign.solveCnstr cnstr then
          sc ()
        else
           ()) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr, sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (G'') = compose'(G', G) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = shift (G', s) (* GEN END TAG OUTSIDE LET *)
      in
        if Assign.unifiable (G'', (N, s'), (e1, s')) then
              aSolve ((eqns, s), dp, cnstr, sc)
        else ()
     end (* GEN END FUN BRANCH *)

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
  and (* GEN BEGIN FUN FIRST *) matchAtom (0, _, _, _, _) = () (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) matchAtom (max, depth,
                 ps' as (I.Root (Ha, _), _),
                 dp as C.DProg (G, dPool), sc) =
      let
        fun (* GEN BEGIN FUN FIRST *) matchSig' nil = () (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) matchSig' (Hc ::sgn') =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val C.SClause(r) = C.sProgLookup (cidFromHead Hc) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = CSManager.trail
                      ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                       rSolve (max-1, depth, ps', (r, I.id), dp,
                               ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc (I.Root (Hc, S)) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
            in
              matchSig' sgn'
            end (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) matchBlock (nil, (n, i)) = () (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) matchBlock ((r, s, H') :: RGs', (n, i)) =
            if eqHead (Ha, H') then
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                            rSolve (max-1,depth, ps', (r, I.comp (s, I.Shift n)), dp,
                                    ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc (I.Root (I.Proj (I.Bidx n, i), S)) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
              in
                matchBlock (RGs', (n, i+1))
              end
            else matchBlock (RGs', (n, i+1)) (* GEN END FUN BRANCH *)
    
    
        fun (* GEN BEGIN FUN FIRST *) matchDProg (I.Null, _) = matchSig' (Index.lookup (cidFromHead Ha)) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.Dec (r, s, Ha')), n) =
            if eqHead (Ha, Ha') then
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                            rSolve (max-1,depth, ps', (r, I.comp (s, I.Shift n)), dp,
                                    ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc (I.Root (I.BVar n, S)) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
              in
                matchDProg (dPool', n+1)
              end
            else matchDProg (dPool', n+1) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.Parameter), n) =
              matchDProg (dPool', n+1) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.BDec RGs), n) =
              (matchBlock (RGs, (n, 1)); matchDProg (dPool', n+1)) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.PDec), n) =
              matchDProg (dPool', n+1) (* GEN END FUN BRANCH *)
      in
        matchDProg (dPool, 1)
      end (* GEN END FUN BRANCH *)


    (* searchEx' max (GE, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)
    (* contexts of EVars are recompiled for each search depth *)
    and (* GEN BEGIN FUN FIRST *) searchEx' max (nil, sc) = sc max (* GEN END FUN FIRST *)
        (* Possible optimization:
           Check if there are still variables left over
        *)
      | (* GEN BEGIN FUN BRANCH *) searchEx' max ((X as I.EVar (r, G, V, _)) :: GE, sc) =
          solve (max, 0, (Compile.compileGoal (G, V), I.id),
                 Compile.compileCtx false G,
                 ((* GEN BEGIN FUNCTION EXPRESSION *) fn U' => (Unify.unify (G, (X, I.id), (U', I.id));
                                         searchEx' max (GE, sc)) handle Unify.Unify _ => () (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)

    (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MTPGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MTPGlobal.maxLevel
    *)
    fun deepen depth f P =
        let
          fun deepen' level =
            if level > depth then ()
            else (if !Global.chatter > 5 then print "#" else ();
                    (f level P;
                     deepen' (level+1)))
        in
          deepen' 1
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

    fun searchEx (it, depth) (GE, sc) =
      (if !Global.chatter > 5 then print "[Search: " else ();
         deepen depth searchEx' (selectEVar (GE),
                                 (* GEN BEGIN FUNCTION EXPRESSION *) fn max => (if !Global.chatter > 5 then print "OK]\n" else ();
                                            let
                                              (* GEN BEGIN TAG OUTSIDE LET *) val GE' = foldr ((* GEN BEGIN FUNCTION EXPRESSION *) fn (X as I.EVar (_, G, _, _), L) =>
                                                               Abstract.collectEVars (G, (X, I.id), L) (* GEN END FUNCTION EXPRESSION *)) nil GE (* GEN END TAG OUTSIDE LET *)
                                              (* GEN BEGIN TAG OUTSIDE LET *) val gE' = List.length GE' (* GEN END TAG OUTSIDE LET *)
                                            in
                                              if gE' > 0 then
                                                if it > 0 then searchEx (it-1, 1) (GE', sc)
                                                else ()
                                              else sc max
                                            (* warning: iterative deepening depth is not propably updated.
                                             possible that it runs into an endless loop ? *)
                                         end) (* GEN END FUNCTION EXPRESSION *));
         if !Global.chatter > 5 then print "FAIL]\n" else ();
           ())

    (* search (GE, sc) = ()

       Invariant:
       GE is a list of uninstantiated EVars
       and sc is a success continuation : int -> unit

       Side effect:
       success continuation will raise exception
    *)
    (* Shared contexts of EVars in GE may recompiled many times *)
    fun search (maxFill, GE, sc) = searchEx (1, maxFill) (GE, sc)

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val searchEx = search (* GEN END TAG OUTSIDE LET *)
  end (* local ... *)

end (* GEN END FUNCTOR DECL *); (* functor Search *)

