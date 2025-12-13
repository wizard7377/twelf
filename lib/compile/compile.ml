(* Compilation for indexing with substitution trees *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Carsten Schuermann, Larry Greenfield,
             Roberto Virga, Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) Compile ((*! structure IntSyn' : INTSYN !*)
                 (*! structure CompSyn' : COMPSYN !*)
                 (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                 structure Whnf : WHNF
                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                 structure TypeCheck : TYPECHECK
                  (* sharing TypeCheck.IntSyn = IntSyn' !*)
                 structure SubTree : SUBTREE
                  (*! sharing SubTree.IntSyn = IntSyn' !*)
                  (*! sharing SubTree.CompSyn = CompSyn' !*)

                    (* CPrint currently unused *)
                 structure CPrint : CPRINT
                 (*! sharing CPrint.IntSyn = IntSyn' !*)
                 (*! sharing CPrint.CompSyn = CompSyn' !*)

                   (* CPrint currently unused *)
                 structure Print : PRINT
                 (*! sharing Print.IntSyn = IntSyn' !*)

                 structure Names : NAMES
                 (*! sharing Names.IntSyn = IntSyn' !*)
                   )
  : COMPILE =
struct

  (* FIX: need to associate errors with occurrences -kw *)
  exception Error of string

  local
    structure I = IntSyn
    structure T = Tomega
    structure C = CompSyn
  in

    datatype duplicates = BVAR of int | FGN | DEF of int

    fun (* GEN BEGIN FUN FIRST *) notCS (I.FromCS) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) notCS _ = true (* GEN END FUN BRANCH *)

   datatype opt = datatype CompSyn.opt
   (* GEN BEGIN TAG OUTSIDE LET *) val optimize  = CompSyn.optimize (* GEN END TAG OUTSIDE LET *)

    fun (* GEN BEGIN FUN FIRST *) cidFromHead (I.Const c) = c (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) cidFromHead (I.Def c) = c (* GEN END FUN BRANCH *)

    (* isConstraint(H) = B
       where B iff H is a constant with constraint status
    *)
    fun (* GEN BEGIN FUN FIRST *) isConstraint (I.Const (c)) =
          (case I.constStatus (c)
             of (I.Constraint _) => true
              | _ => false) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isConstraint H = false (* GEN END FUN BRANCH *)

    (* head (A) = H, the head of V

       Invariants:
       G |- A : type, A enf
       A = H @ S
    *)
    fun (* GEN BEGIN FUN FIRST *) head (I.Root(h, _)) = h (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) head (I.Pi (_, A)) = head(A) (* GEN END FUN BRANCH *)

  fun seen (i, Vars) =
        List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn (d, x) => (x = i) (* GEN END FUNCTION EXPRESSION *)) Vars

  (* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *)

(*
  fun etaSpine' (I.Nil, n) = (n=0)
    | etaSpine' (I.App(U, S), n) =
        if Whnf.etaContract U = n then etaSpine' (S, n-1)
        else false

  fun etaSpine (S, n) = etaSpine' (S, n) handle Eta => false
*)

  fun (* GEN BEGIN FUN FIRST *) etaSpine (I.Nil, n) = (n=0) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) etaSpine (I.App(I.Root(I.BVar k, I.Nil), S), n) =
       (k = n andalso etaSpine(S, n-1)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) etaSpine (I.App(A, S), n) = false (* GEN END FUN BRANCH *)

  (* collectHead (h, K, Vars, depth) = (K', Vars', replaced)
     adds to K and Vars as in collectExp and collectSpine
   *)
  fun (* GEN BEGIN FUN FIRST *) collectHead(h as I.BVar k, S, K, Vars, depth) =
       (* check if k is in Vars *)
       (if (k > depth) then
           (* check if h is an eta-expanded variable *)
           (if etaSpine(S, depth) then
              (if seen (k-depth, Vars) then
                 (((depth, BVAR(k-depth))::K), Vars, true)
               else
                 (K, ((depth, k-depth)::Vars), false))
            else
              (((depth, BVAR(k-depth))::K), Vars, true))
         else
           (* h is a locally bound variable and need not be collected *)
           (K, Vars, false)) (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) collectHead (_, _, K, Vars, depth) = (K, Vars, false) (* GEN END FUN BRANCH *)

   (* collectExp (U, K, Vars, depth) = (K', Vars')
      collectSpine (S, K, Vars, depth) = (K', Vars')

      Vars' - Vars = all variables seen in U or S
      K' - K = expressions in U or S to be replaced

      U, S in NF

      for each new variable (d, k-d) for depth wrt locally bound variables
   *)
   fun (* GEN BEGIN FUN FIRST *) collectSpine(I.Nil, K, Vars, depth) = (K, Vars) (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) collectSpine(I.App(U, S), K, Vars, depth) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val (K', Vars') = collectExp(U, K, Vars, depth) (* GEN END TAG OUTSIDE LET *)
       in
         collectSpine(S, K', Vars', depth)
       end (* GEN END FUN BRANCH *)

   and (* GEN BEGIN FUN FIRST *) collectExp (I.Root(h as I.BVar k, S), K, Vars, depth) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val (K', Vars', replaced) = collectHead (h, S, K, Vars, depth) (* GEN END TAG OUTSIDE LET *)
       in
         if replaced
           then (K', Vars')
         else
           collectSpine (S, K', Vars', depth)
       end (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) collectExp (U as I.Root(I.Def k, S), K, Vars, depth) =
       ((depth, DEF k)::K, Vars) (* GEN END FUN BRANCH *)
     (* h is either const or skonst of def*)
     | (* GEN BEGIN FUN BRANCH *) collectExp (I.Root(h, S), K, Vars, depth) =
         collectSpine (S, K, Vars, depth) (* GEN END FUN BRANCH *)
     (* should be impossible, Mon Apr 15 14:55:15 2002 -fp *)
     (* | collectExp (I.Uni(L), K, Vars, depth) = (K, Vars) *)
     | (* GEN BEGIN FUN BRANCH *) collectExp (I.Lam(D, U), K, Vars, depth) =
         (* don't collect D, since it is ignored in unification *)
         collectExp (U, K, Vars, depth+1) (* GEN END FUN BRANCH *)
     | (* GEN BEGIN FUN BRANCH *) collectExp (I.FgnExp (cs, fe), K, Vars, depth) =
         ((depth, FGN)::K, Vars) (* GEN END FUN BRANCH *)
     (* no EVars, since U in NF *)

  (* shiftHead (H, depth, total) = H'
     shiftExp (U, depth, total) = U'
     shiftSpine (S, depth, total) = S'

     where each variable k > depth is shifted by +total

     Invariants: U is NF, S is in NF
  *)
  fun (* GEN BEGIN FUN FIRST *) shiftHead ((h as I.BVar k), depth, total) =
      (if k > depth then
         I.BVar(k + total)
       else
         I.BVar(k)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) shiftHead ((h as I.Const k), depth, total) = h (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) shiftHead ((h as I.Def k), depth, total) = h (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) shiftHead ((h as I.NSDef k), depth, total) = h (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) shiftHead ((h as I.FgnConst k), depth, total) = h (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) shiftHead ((h as I.Skonst k) , depth, total) = h (* GEN END FUN BRANCH *)


  fun (* GEN BEGIN FUN FIRST *) shiftExp (I.Root(h, S), depth, total) =
        I.Root(shiftHead(h, depth, total), shiftSpine(S, depth, total)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) shiftExp (I.Uni(L), _, _) = I.Uni(L) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) shiftExp (I.Lam(D, U), depth, total) =
        I.Lam(shiftDec(D, depth, total), shiftExp(U, depth+1, total)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) shiftExp (I.Pi((D, P), U), depth, total) =
        I.Pi((shiftDec(D, depth, total), P), shiftExp (U, depth+1, total)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) shiftExp (I.FgnExp csfe, depth, total) =
        (* calling normalize here because U may not be normal *)
        (* this is overkill and could be very expensive for deeply nested foreign exps *)
        (* Tue Apr  2 12:10:24 2002 -fp -bp *)
        I.FgnExpStd.Map.apply csfe ((* GEN BEGIN FUNCTION EXPRESSION *) fn U => shiftExp(Whnf.normalize (U, I.id), depth, total) (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN BRANCH *)
  and (* GEN BEGIN FUN FIRST *) shiftSpine (I.Nil, _, _) = I.Nil (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) shiftSpine (I.App(U, S), depth, total) =
        I.App(shiftExp(U, depth, total), shiftSpine(S, depth, total)) (* GEN END FUN BRANCH *)

  and shiftDec (I.Dec(x, V), depth, total) =
        I.Dec(x, shiftExp (V, depth, total))

  (* linearHead (Gl, h, S, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

   if G0, Gl |- h @ S and
      h is a duplicate (i.e. it is either not fully applied pattern
       or it has already occured and is an element of Vars)

      |Gl| = depth, Gl is local context of BVars
   then
      h' is a new variable standing for a new AVar
      M = Root(h, S) where each variable in G0 is shifted by total
      N = Root(h', I.Nil)

   and
      Eqn accumulates residual equation UnifyEq(Gl, M, N)
  *)
   fun (* GEN BEGIN FUN FIRST *) linearHead(G, h as I.BVar(k), S, left, Vars, depth, total) =
       if k > depth then
         (if etaSpine(S, depth) then
            (if (seen (k-depth, Vars)) then
               (left-1, Vars, I.BVar(left + depth), true)
             else
               (left, ((depth, k-depth)::Vars), I.BVar (k + total), false))
          else
            (left-1, Vars, I.BVar(left + depth), true))
       else
         (left, Vars, h, false) (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) linearHead(G, (h as I.Const k), S, left, Vars, depth, total) =
         (left, Vars, h, false) (* GEN END FUN BRANCH *)
     (*
     | linearHead(G, (h as I.NSDef k), s, S, left, Vars, depth, total) =
         (left, Vars, h, false)
     *)
     | (* GEN BEGIN FUN BRANCH *) linearHead(G, (h as I.FgnConst(k, ConDec)), S, left, Vars, depth, total) =
         (left, Vars, h, false) (* GEN END FUN BRANCH *)

     | (* GEN BEGIN FUN BRANCH *) linearHead(G, (h as I.Skonst k) , S, left, Vars, depth, total) =
         (left, Vars, h, false) (* GEN END FUN BRANCH *)
     (* Def cannot occur *)

  (* linearExp (Gl, U, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

     call linearHead on every embedded root

     left' = left - #replaced expressions in U
     Vars' = all BVars in G0 seen in U
     N = copy of U with replaced expressions
     Eqn = residual equations

     "For any U', U = U' iff (N = U' and Eqn)"
  *)
   fun (* GEN BEGIN FUN FIRST *) linearExp (Gl, U as I.Root(h as I.Def k, S), left, Vars, depth, total, eqns) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val N = I.Root(I.BVar(left + depth), I.Nil) (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val U' = shiftExp(U, depth, total) (* GEN END TAG OUTSIDE LET *)
       in
         (left-1, Vars, N, C.UnifyEq(Gl, U', N, eqns))
       end (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) linearExp (Gl, U as I.Root(h, S), left, Vars, depth, total, eqns) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val (left', Vars', h', replaced) =  linearHead (Gl, h, S, left, Vars, depth, total) (* GEN END TAG OUTSIDE LET *)
       in
         if replaced then
           let
             (* GEN BEGIN TAG OUTSIDE LET *) val N = I.Root(h', I.Nil) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val U' = shiftExp (U, depth, total) (* GEN END TAG OUTSIDE LET *)
           in
             (left', Vars, N, C.UnifyEq(Gl, U', N, eqns))
           end
         else (* h = h' not replaced *)
           let
             (* GEN BEGIN TAG OUTSIDE LET *) val (left'', Vars'', S', eqns') =
                 linearSpine (Gl, S, left', Vars', depth, total, eqns) (* GEN END TAG OUTSIDE LET *)
           in
             (left'',  Vars'', I.Root(h', S'), eqns')
           end
       end (* GEN END FUN BRANCH *)
     (* should be impossible  Mon Apr 15 14:54:42 2002 -fp *)
     (*
     | linearExp (Gl, U as I.Uni(L), left, Vars, depth, total, eqns) =
         (left, Vars, I.Uni(L), eqns)
     *)

     | (* GEN BEGIN FUN BRANCH *) linearExp (Gl, I.Lam(D, U), left, Vars, depth, total, eqns) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val D' = shiftDec(D, depth, total) (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (left', Vars', U', eqns') = linearExp (I.Decl(Gl, D'), U, left, Vars,
                                                    depth+1, total, eqns) (* GEN END TAG OUTSIDE LET *)
       in
         (left', Vars', I.Lam(D', U'), eqns')
       end (* GEN END FUN BRANCH *)
   | (* GEN BEGIN FUN BRANCH *) linearExp (Gl, U as I.FgnExp (cs, ops), left, Vars, depth, total, eqns) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val N = I.Root(I.BVar(left + depth), I.Nil) (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val U' = shiftExp(U, depth, total) (* GEN END TAG OUTSIDE LET *)
       in
         (left-1, Vars, N, C.UnifyEq(Gl, U', N, eqns))
       end (* GEN END FUN BRANCH *)

   and (* GEN BEGIN FUN FIRST *) linearSpine(Gl, I.Nil, left, Vars, depth, total, eqns) = (left, Vars, I.Nil, eqns) (* GEN END FUN FIRST *)
     | (* GEN BEGIN FUN BRANCH *) linearSpine(Gl, I.App(U, S), left, Vars, depth, total, eqns) =
       let
         (* GEN BEGIN TAG OUTSIDE LET *) val (left', Vars',  U',eqns') = linearExp(Gl, U, left, Vars, depth, total,eqns) (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (left'', Vars'', S', eqns'') = linearSpine(Gl, S, left', Vars', depth, total, eqns') (* GEN END TAG OUTSIDE LET *)
       in
         (left'', Vars'', I.App(U', S'), eqns'')
       end (* GEN END FUN BRANCH *)
     (* SClo(S, s') cannot occur *)


   (*  compileLinearHead (G, R as I.Root (h, S)) = r

       r is residual goal
       if G |- R and R might not be linear

       then

           G |- H ResGoal  and H is linear
       and of the form
           (Axists(_ , Axists( _, ....., Axists( _, Assign (E, AuxG)))))
  *)
    fun compileLinearHead (G, R as I.Root (h, S)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (K, _) =  collectExp (R, nil, nil, 0) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val left = List.length K (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (left', _, R', Eqs) = linearExp(I.Null, R, left, nil, 0, left, C.Trivial) (* GEN END TAG OUTSIDE LET *)
    
          fun (* GEN BEGIN FUN FIRST *) convertKRes (ResG, nil, 0) = ResG (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) convertKRes (ResG, ((d,k)::K), i) =
              (C.Axists(I.ADec (SOME("A"^Int.toString i), d), convertKRes (ResG, K, i-1))) (* GEN END FUN BRANCH *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val r = convertKRes(C.Assign(R', Eqs), List.rev K, left) (* GEN END TAG OUTSIDE LET *)
        in
          (if (!Global.chatter) >= 6 then
             (print ("\nClause LH Eqn" );
              print (CPrint.clauseToString "\t" (G, r)))
           else
             ());
          r
        end

  (*  compileSbtHead (G, R as I.Root (h, S)) = r

       r is residual goal
       if G |- R and R might not be linear

       then

           G |- H ResGoal  and H is linear

  *)
    fun compileSbtHead (G, H as I.Root (h, S)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (K, _) =  collectExp (H, nil, nil, 0) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val left = List.length K (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (left', _, H', Eqs) = linearExp(I.Null, H, left, nil, 0, left, C.Trivial) (* GEN END TAG OUTSIDE LET *)
    
          fun (* GEN BEGIN FUN FIRST *) convertKRes (G, nil, 0) = G (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) convertKRes (G, ((d,k)::K), i) =
            convertKRes (I.Decl(G, I.ADec (SOME("AVar "^Int.toString i), d)), K, i-1) (* GEN END FUN BRANCH *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val G' = convertKRes(G, List.rev K, left) (* GEN END TAG OUTSIDE LET *)
        in
          (if (!Global.chatter) >= 6 then
             (print ("\nClause Sbt Eqn" );
              print (CPrint.clauseToString "\t" (G', C.Assign(H', Eqs))))
           else
             ());
           (* insert R' together with Eqs and G and sc C.True *)
           (G',  SOME(H', Eqs))
        end

  (* compileGoalN  fromCS A => g
     if A is a type interpreted as a subgoal in a clause and g is its
     compiled form.  No optimization is performed.

     Invariants:
     If G |- A : type,  A enf
        A has no existential type variables
     then G |- A ~> g  (A compiles to goal g)
     and  G |- g  goal

     Note: we don't accept objects that may introduce assumptions of
     constraint types, unless fromCS = true (the object come from a
     Constraint Solver module.
  *)
  fun (* GEN BEGIN FUN FIRST *) compileGoalN fromCS (G, R as I.Root _) =
      (* A = H @ S *)
       C.Atom (R) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compileGoalN fromCS (G, I.Pi((I.Dec(_,A1), I.No), A2)) =
      (* A = A1 -> A2 *)
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val Ha1 = I.targetHead A1 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val R = compileDClauseN fromCS false (G, A1) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val goal = compileGoalN fromCS (I.Decl(G, I.Dec(NONE, A1)), A2) (* GEN END TAG OUTSIDE LET *)
      in
        (* A1 is used to build the proof term, Ha1 for indexing *)
        (* never optimize when compiling local assumptions *)
        C.Impl(R, A1, Ha1, goal)
    
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compileGoalN fromCS (G, I.Pi((D as I.Dec (_, A1), I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
       if notCS fromCS andalso isConstraint (head (A1))
       then raise Error "Constraint appears in dynamic clause position"
       else C.All(D, compileGoalN fromCS (I.Decl(G, D), A2)) (* GEN END FUN BRANCH *)

  (*  compileGoalN _ should not arise by invariants *)
  and compileGoal fromCS (G, (A, s)) =
       compileGoalN fromCS (G, Whnf.normalize (A, s))

  (* compileDClause A => G (top level)
     if A is a type interpreted as a clause and G is its compiled form.

     Some optimization is attempted if so flagged.

     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> r  (A compiles to residual goal r)
     and  G |- r  resgoal
  *)

   and (* GEN BEGIN FUN FIRST *) compileDClauseN fromCS opt (G, R as I.Root (h, S)) =
      if opt  andalso (!optimize = C.LinearHeads) then
        compileLinearHead (G, R)
      else
        if notCS fromCS andalso isConstraint (h)
        then
          raise Error "Constraint appears in dynamic clause position"
        else C.Eq(R) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compileDClauseN fromCS opt (G, I.Pi((D as (I.Dec(_,A1)),I.No), A2)) =
      (* A = A1 -> A2 *)
      C.And(compileDClauseN fromCS opt (I.Decl(G, D), A2), A1,
            compileGoalN fromCS (G, A1)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) compileDClauseN fromCS opt (G, I.Pi((D as (I.Dec(_,A1)),I.Meta), A2)) =
      (* A = {x: A1} A2, x  meta variable occuring in A2 *)
      C.In(compileDClauseN fromCS opt (I.Decl(G, D), A2), A1,
           compileGoalN fromCS (G, A1)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) compileDClauseN fromCS opt (G, I.Pi((D,I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
      C.Exists (D, compileDClauseN fromCS opt (I.Decl(G, D), A2)) (* GEN END FUN BRANCH *)
  (*  compileDClauseN _ should not arise by invariants *)


  (* Compilation of (static) program clauses *)

  (* compileSubgoals G' (n, Stack, G) = Subgoals  (top level)

     Invariants:
     If G : Stack
        G' ctx where G' = G, GAVar
     then Stack ~> subgoals  (Stack compiles to subgoals)
     and  G' |- subgoals
  *)
  fun (* GEN BEGIN FUN FIRST *) compileSubgoals fromCS G' (n, I.Decl(Stack, I.No), I.Decl(G, I.Dec(_, A))) =
    let
      (* G |- A and G' |- A[^(n+1)] *)
      (* GEN BEGIN TAG OUTSIDE LET *) val sg = compileSubgoals fromCS G' (n+1, Stack, G) (* GEN END TAG OUTSIDE LET *)
    in
      C.Conjunct (compileGoal fromCS (G', (A, I.Shift (n+1))), I.EClo(A, I.Shift(n+1)), sg)
    end (* GEN END FUN FIRST *)

    | (* GEN BEGIN FUN BRANCH *) compileSubgoals fromCS G' (n, I.Decl(Stack, I.Maybe), I.Decl(G, I.Dec(_, A1))) =
       compileSubgoals fromCS G' (n+1, Stack, G) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) compileSubgoals fromCS G' (n, I.Null, I.Null) = C.True (* GEN END FUN BRANCH *)

  (* compileSClause (Stack, G, A) => (Head, SubGoals) (top-level)
     if A is a type interpreted as a clause and (Head, SubGoals)
     is its compiled form.

     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> (Head, subgoals) ((A compiles to head and subgoals)
          where GAVar, G |- Head and GAVar, G |- subgoals
          and Head is linear and G' = GAVar, G
  *)

  fun (* GEN BEGIN FUN FIRST *) compileSClauseN fromCS (Stack, G, R as I.Root (h, S)) =
      let
         (* GEN BEGIN TAG OUTSIDE LET *) val (G', Head) = compileSbtHead (G, R) (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val d = I.ctxLength G' - I.ctxLength G (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val Sgoals = compileSubgoals fromCS G' (d, Stack, G) (* GEN END TAG OUTSIDE LET *)
         (* G' |- Sgoals  and G' |- ^d : G *)
      in
         ((G', Head), Sgoals)
       end (* GEN END FUN FIRST *)

    | (* GEN BEGIN FUN BRANCH *) compileSClauseN fromCS (Stack, G, I.Pi((D as (I.Dec(_,A1)),I.No), A2)) =
      compileSClauseN fromCS (I.Decl(Stack, I.No), I.Decl(G, D), A2) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) compileSClauseN fromCS (Stack, G, I.Pi((D as (I.Dec(_,A1)),I.Meta), A2)) =
      compileSClauseN fromCS (I.Decl(Stack, I.Meta), I.Decl(G, D), A2) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) compileSClauseN fromCS (Stack, G, I.Pi((D as (I.Dec(_,A1)),I.Maybe), A2)) =
      compileSClauseN fromCS (I.Decl(Stack, I.Maybe), I.Decl(G, D), A2) (* GEN END FUN BRANCH *)


  fun compileDClause opt (G, A) =
        compileDClauseN I.Ordinary opt (G, Whnf.normalize (A, I.id))

  fun compileGoal (G, A) =
    compileGoalN I.Ordinary (G, Whnf.normalize (A, I.id))

  (* compileCtx G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  fun compileCtx opt G =
      let
        fun (* GEN BEGIN FUN FIRST *) compileBlock (nil, s, (n, i)) = nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) compileBlock (I.Dec (_, V) :: Vs, t, (n, i)) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Vt = I.EClo (V, t) (* GEN END TAG OUTSIDE LET *)
            in
              (compileDClause opt (G, Vt), I.id, I.targetHead Vt)
              :: compileBlock (Vs, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx n, i), I.Nil)), t), (n, i+1))
            end (* GEN END FUN BRANCH *)
        fun (* GEN BEGIN FUN FIRST *) compileCtx' (I.Null) = I.Null (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) compileCtx' (I.Decl (G, I.Dec (_, A))) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Ha = I.targetHead A (* GEN END TAG OUTSIDE LET *)
            in
              I.Decl (compileCtx' G, CompSyn.Dec (compileDClause opt (G, A), I.id, Ha))
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) compileCtx' (I.Decl (G, I.BDec (_, (c, s)))) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (G, L)= I.constBlock c (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val dpool = compileCtx' G (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val n = I.ctxLength dpool (* GEN END TAG OUTSIDE LET *)   (* this is inefficient! -cs *)
            in
              I.Decl (dpool, CompSyn.BDec (compileBlock (L, s, (n, 1))))
            end (* GEN END FUN BRANCH *)
      in
        C.DProg (G, compileCtx' G)
      end

  (* compile G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  fun compilePsi opt Psi =
      let
        fun (* GEN BEGIN FUN FIRST *) compileBlock (nil, s, (n, i)) = nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) compileBlock (I.Dec (_, V) :: Vs, t, (n, i)) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Vt = I.EClo (V, t) (* GEN END TAG OUTSIDE LET *)
            in
              (compileDClause opt (T.coerceCtx Psi, Vt), I.id, I.targetHead Vt)
              :: compileBlock (Vs, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx n, i), I.Nil)), t), (n, i+1))
            end (* GEN END FUN BRANCH *)
        fun (* GEN BEGIN FUN FIRST *) compileCtx' (I.Null) = I.Null (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) compileCtx' (I.Decl (G, I.Dec (_, A))) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Ha = I.targetHead A (* GEN END TAG OUTSIDE LET *)
            in
              I.Decl (compileCtx' G, CompSyn.Dec (compileDClause opt (G, A), I.id, Ha))
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) compileCtx' (I.Decl (G, I.BDec (_, (c, s)))) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (G, L)= I.constBlock c (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val dpool = compileCtx' G (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val n = I.ctxLength dpool (* GEN END TAG OUTSIDE LET *)   (* this is inefficient! -cs *)
            in
              I.Decl (dpool, CompSyn.BDec (compileBlock (L, s, (n, 1))))
            end (* GEN END FUN BRANCH *)
        fun (* GEN BEGIN FUN FIRST *) compilePsi' (I.Null) = I.Null (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) compilePsi' (I.Decl (Psi, T.UDec (I.Dec (_, A)))) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Ha = I.targetHead A (* GEN END TAG OUTSIDE LET *)
            in
              I.Decl (compilePsi' Psi, CompSyn.Dec (compileDClause opt (T.coerceCtx Psi, A), I.id, Ha))
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) compilePsi' (I.Decl (Psi, T.UDec (I.BDec (_, (c, s))))) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (G, L)= I.constBlock c (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val dpool = compileCtx' G (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val n = I.ctxLength dpool (* GEN END TAG OUTSIDE LET *)   (* this is inefficient! -cs *)
            in
              I.Decl (dpool, CompSyn.BDec (compileBlock (L, s, (n, 1))))
            
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) compilePsi' (I.Decl (Psi, T.PDec _)) =
            I.Decl (compilePsi' Psi, CompSyn.PDec) (* GEN END FUN BRANCH *)
  
  
  
      in
        C.DProg (T.coerceCtx Psi, compilePsi' Psi)
      end


  (* installClause fromCS (a, A) = ()
     Effect: compiles and installs compiled form of A according to
             the specified compilation strategy
  *)
  fun installClause fromCS (a, A) =
    (case (!C.optimize)
     of C.No => C.sProgInstall (a, C.SClause (compileDClauseN fromCS true (I.Null, A)))
      | C.LinearHeads => C.sProgInstall (a, C.SClause(compileDClauseN fromCS true (I.Null, A)))
      | C.Indexing =>
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val ((G, Head), R) = compileSClauseN fromCS (I.Null, I.Null, Whnf.normalize (A, I.id)) (* GEN END TAG OUTSIDE LET *)
           (* GEN BEGIN TAG OUTSIDE LET *) val _ = C.sProgInstall (a, C.SClause(compileDClauseN fromCS true (I.Null, A))) (* GEN END TAG OUTSIDE LET *)
         in
           case Head
             of NONE => raise Error "Install via normal index"
           | SOME (H, Eqs) => SubTree.sProgInstall (cidFromHead(I.targetHead A),
                                                    C.Head(H, G, Eqs, a), R)
         end)

  (* compileConDec (a, condec) = ()
     Effect: install compiled form of condec in program table.
             No effect if condec has no operational meaning
  *)
  (* Defined constants are currently not compiled *)

  fun (* GEN BEGIN FUN FIRST *) compileConDec fromCS (a, I.ConDec(_, _, _, _, A, I.Type)) =
      installClause fromCS (a, A) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compileConDec fromCS (a, I.SkoDec(_, _, _, A, I.Type)) =
      (* we don't use substitution tree indexing for skolem constants yet -bp*)
      (case (!C.optimize)
         of C.No => C.sProgInstall (a, C.SClause (compileDClauseN fromCS true (I.Null, A)))
       | _ => C.sProgInstall (a, C.SClause(compileDClauseN fromCS true (I.Null, A)))) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) compileConDec I.Clause (a, I.ConDef(_, _, _, _, A, I.Type, _)) =
        C.sProgInstall (a, C.SClause (compileDClauseN I.Clause true (I.Null, Whnf.normalize (A, I.id)))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compileConDec _ _ = () (* GEN END FUN BRANCH *)

  fun install fromCS (cid) =  compileConDec fromCS (cid, I.sgnLookup cid)

  fun sProgReset () = (SubTree.sProgReset(); C.sProgReset())


  end  (* local open ... *)

end (* GEN END FUNCTOR DECL *); (* functor Compile *)


