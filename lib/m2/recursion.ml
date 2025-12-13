(* Recursion *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)

functor (* GEN BEGIN FUNCTOR DECL *) Recursion (structure Global : GLOBAL
                   structure MetaSyn' : METASYN
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                   structure Unify : UNIFY
                   (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
                   structure Conv : CONV
                   (*! sharing Conv.IntSyn = MetaSyn'.IntSyn !*)
                   structure Names : NAMES
                   (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                   structure Subordinate : SUBORDINATE
                   (*! sharing Subordinate.IntSyn = MetaSyn'.IntSyn !*)
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                   structure Order : ORDER
                   (*! sharing Order.IntSyn = MetaSyn'.IntSyn !*)
                   structure ModeTable : MODETABLE
                   (*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
                   structure Lemma : LEMMA
                   sharing Lemma.MetaSyn = MetaSyn'
                   structure Filling : FILLING
                   sharing Filling.MetaSyn = MetaSyn'
                   structure MetaPrint : METAPRINT
                   sharing MetaPrint.MetaSyn = MetaSyn'
                   structure MetaAbstract : METAABSTRACT
                   sharing MetaAbstract.MetaSyn = MetaSyn'
                   structure Formatter : FORMATTER
                   (*! structure CSManager : CS_MANAGER !*)
                   (*! sharing CSManager.IntSyn = MetaSyn'.IntSyn !*)
)  : RECURSION =
struct

  structure MetaSyn = MetaSyn'

  exception Error of string

  type operator = MetaSyn.state

  local
    structure M = MetaSyn
    structure I = IntSyn
    structure O = Order
    structure N = Names
    structure F = Formatter


    datatype quantifier =                     (* Quantifier to mark parameters *)
      Universal                               (* Q ::= Uni                     *)
    | Existential                             (*     | Ex                      *)

    (* If Q marks all parameters in a context G we write   G : Q               *)


    (* duplicate code? -fp *)
    fun vectorToString (G, O) =
        let
          fun (* GEN BEGIN FUN FIRST *) fmtOrder (Order.Arg (Us, Vs)) =
              [F.String (Print.expToString (G, I.EClo Us)), F.String ":",
               F.String (Print.expToString (G, I.EClo Vs))] (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) fmtOrder (Order.Lex L) = [F.String "{", F.HVbox (fmtOrders L), F.String "}"] (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) fmtOrder (Order.Simul L) = [F.String "[", F.HVbox (fmtOrders L), F.String "]"] (* GEN END FUN BRANCH *)
    
          and (* GEN BEGIN FUN FIRST *) fmtOrders nil = nil (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) fmtOrders (O :: nil) = fmtOrder O (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) fmtOrders (O :: L) = fmtOrder O @ (F.String " " :: fmtOrders L) (* GEN END FUN BRANCH *)
        in
          F.makestring_fmt (F.HVbox (fmtOrder O))
        end

    (* vector (c, (S, s)) = P'

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type
       and  G |- S[s] = U1 .. Un : V[s] > type
       and  sel (c) = i1 .. im
       then P' = (U1'[s1']: V1'[t1'], .., U1'[sm']: V1'[tm'])
       and  G |- sj' : Gj'    Gj' |- Uj' : V1j'
       and  G |- tj' : Gj'    Gj' |- Vj' : L
       and  G |- Vj' [tj'] = V1j' [sj'] : L
       and  G |- Uik = Uk'[sk']
    *)
    fun vector (c, (S, s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Vid = (I.constType c, I.id) (* GEN END TAG OUTSIDE LET *)
          fun select' (n, (Ss', Vs'')) =
                select'W (n, (Ss', Whnf.whnf Vs''))
          and (* GEN BEGIN FUN FIRST *) select'W (1, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V''), _), _), s''))) =
                ((U', s'), (V'', s'')) (* GEN END FUN FIRST *)
              (* select'W (1, _, (I.Root _, _)) cannot occur by invariant ! *)
            | (* GEN BEGIN FUN BRANCH *) select'W (n, ((I.SClo (S', s1'), s2'), Vs'')) =
                select'W (n, ((S', I.comp (s1', s2')), Vs'')) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select'W (n, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V1''), _), V2''), s''))) =
                select' (n-1, ((S', s'), (V2'', I.Dot (I.Exp (I.EClo (U', s')), s'')))) (* GEN END FUN BRANCH *)
          fun (* GEN BEGIN FUN FIRST *) select (O.Arg n) = O.Arg (select' (n, ((S, s), Vid))) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) select (O.Lex L) = O.Lex (map select L) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select (O.Simul L) = O.Simul (map select L) (* GEN END FUN BRANCH *)
        in
          select (O.selLookup c)
        end

    (* set_parameter (G, X, k, sc, ops) = ops'

       Invariant:
       appends a list of recursion operators to ops after
       instantiating X with all possible local parameters (between 1 and k)
    *)
    fun set_parameter (G, X as I.EVar (r, _, V, _), k, sc, ops) =
        let
          fun (* GEN BEGIN FUN FIRST *) set_parameter' (0, ops') =  ops' (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) set_parameter' (k', ops') =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val D' as I.Dec (_, V') = I.ctxDec (G, k') (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val ops'' =
                    CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                                 if Unify.unifiable (G, (V, I.id), (V', I.id))
                                   andalso Unify.unifiable (G, (X, I.id), (I.Root (I.BVar k', I.Nil), I.id))
                                   then sc ops'
                                 else ops' (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
                in
                  set_parameter' (k'-1, ops'')
                end (* GEN END FUN BRANCH *)
        in
          set_parameter' (k, ops)
        end

    (* ltinit (G, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of all all possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
    fun ltinit (G, k, (Us, Vs), UsVs', sc, ops) =
          ltinitW (G, k, Whnf.whnfEta (Us, Vs), UsVs', sc, ops)
    and (* GEN BEGIN FUN FIRST *) ltinitW (G, k, (Us, Vs as (I.Root _, _)), UsVs', sc, ops) =
          lt (G, k, (Us, Vs), UsVs', sc, ops) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ltinitW (G, k,
                 ((I.Lam (D1, U), s1), (I.Pi (D2, V), s2)),
                 ((U', s1'), (V', s2')),
                 sc, ops) =
          ltinit (I.Decl (G, I.decSub (D1, s1) (* = I.decSub (D2, s2) *)), k+1,
                  ((U, I.dot1 s1), (V, I.dot1 s2)),
                  ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))),
                  sc, ops) (* GEN END FUN BRANCH *)

    (* lt (G, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuate possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)

    (* Vs is Root!!! *)
    (* (Us',Vs') may not be eta-expanded!!! *)
    and lt (G, k, (Us, Vs), (Us', Vs'), sc, ops) =
          ltW (G, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, ops)
    and (* GEN BEGIN FUN FIRST *) ltW (G, k, (Us, Vs), ((I.Root (I.Const c, S'), s'), Vs'), sc, ops) =
          ltSpine (G, k, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, ops) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ltW (G, k, (Us, Vs), ((I.Root (I.BVar n, S'), s'), Vs'), sc, ops) =
          if n <= k then  (* n must be a local variable *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V') = I.ctxDec (G, n) (* GEN END TAG OUTSIDE LET *)
            in
              ltSpine (G, k, (Us, Vs), ((S', s'), (V', I.id)), sc, ops)
            end
          else ops (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ltW (G, _, _, ((I.EVar _, _), _), _, ops) = ops (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ltW (G, k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'),
                                        (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, ops) =
        if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then
          let  (* enforce that X gets only bound to parameters *)
            (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1', s1')) (* GEN END TAG OUTSIDE LET *) (* = I.newEVar (I.EClo (V2', s2')) *)
            (* GEN BEGIN TAG OUTSIDE LET *) val sc' = (* GEN BEGIN FUNCTION EXPRESSION *) fn ops' => set_parameter (G, X, k, sc, ops') (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
          in
            lt (G, k, ((U, s1), (V, s2)),
                ((U', I.Dot (I.Exp (X), s1')),
                 (V', I.Dot (I.Exp (X), s2'))), sc', ops)
          end
        else
          if Subordinate.below (I.targetFam V1', I.targetFam V) then
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1', s1')) (* GEN END TAG OUTSIDE LET *) (* = I.newEVar (I.EClo (V2', s2')) *)
            in
              lt (G, k, ((U, s1), (V, s2)),
                  ((U', I.Dot (I.Exp (X), s1')),
                   (V', I.Dot (I.Exp (X), s2'))), sc, ops)
            end
          else ops (* GEN END FUN BRANCH *)

    and ltSpine (G, k, (Us, Vs), (Ss', Vs'), sc, ops) =
          ltSpineW (G, k, (Us, Vs), (Ss', Whnf.whnf Vs'), sc, ops)
    and (* GEN BEGIN FUN FIRST *) ltSpineW (G, k, (Us, Vs), ((I.Nil, _), _), _, ops) = ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ltSpineW (G, k, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc, ops) =
          ltSpineW (G, k, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc, ops) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ltSpineW (G, k, (Us, Vs), ((I.App (U', S'), s1'),
                                   (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), sc, ops) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ops' = le (G, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, ops) (* GEN END TAG OUTSIDE LET *)
        in
          ltSpine (G, k, (Us, Vs), ((S', s1'),
                                 (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), sc, ops')
        end (* GEN END FUN BRANCH *)

    (* eq (G, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] = U'[s']
    *)
    and eq (G, (Us, Vs), (Us', Vs'), sc, ops) =
        (CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                      if Unify.unifiable (G, Vs, Vs')
                        andalso Unify.unifiable (G, Us, Us')
                        then sc ops
                      else ops (* GEN END FUNCTION EXPRESSION *)))


    (* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] <= U'[s']
    *)

    and le (G, k, (Us, Vs), (Us', Vs'), sc, ops) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ops' = eq (G, (Us, Vs), (Us', Vs'), sc, ops) (* GEN END TAG OUTSIDE LET *)
        in
          leW (G, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, ops')
        end

    and (* GEN BEGIN FUN FIRST *) leW (G, k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'),
                                        (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, ops) =
        if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1', s1')) (* GEN END TAG OUTSIDE LET *) (* = I.newEVar (I.EClo (V2', s2')) *)
            (* GEN BEGIN TAG OUTSIDE LET *) val sc' = (* GEN BEGIN FUNCTION EXPRESSION *) fn ops' => set_parameter (G, X, k, sc, ops') (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
          (* enforces that X can only bound to parameter *)
          in
            le (G, k, ((U, s1), (V, s2)),
                ((U', I.Dot (I.Exp (X), s1')),
                 (V', I.Dot (I.Exp (X), s2'))), sc', ops)
          end
        else
          if Subordinate.below  (I.targetFam V1', I.targetFam V) then
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1', s1')) (* GEN END TAG OUTSIDE LET *) (* = I.newEVar (I.EClo (V2', s2')) *)
            in
              le (G, k, ((U, s1), (V, s2)),
                  ((U', I.Dot (I.Exp (X), s1')),
                   (V', I.Dot (I.Exp (X), s2'))), sc, ops)
            end
          else ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) leW (G, k, (Us, Vs), (Us', Vs'), sc, ops) = lt (G, k, (Us, Vs), (Us', Vs'), sc, ops) (* GEN END FUN BRANCH *)


    (* ordlt (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
    fun (* GEN BEGIN FUN FIRST *) ordlt (G, O.Arg UsVs, O.Arg UsVs', sc, ops) =  ltinit (G, 0, UsVs, UsVs', sc, ops) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordlt (G, O.Lex L, O.Lex L', sc, ops) = ordltLex (G, L, L', sc, ops) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ordlt (G, O.Simul L, O.Simul L', sc, ops) = ordltSimul (G, L, L', sc, ops) (* GEN END FUN BRANCH *)


    (* ordltLex (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
    and (* GEN BEGIN FUN FIRST *) ordltLex (G, nil, nil, sc, ops) = ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordltLex (G, O :: L, O' :: L', sc, ops) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ops' = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => ordlt (G, O, O', sc, ops) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          ordeq (G, O, O', (* GEN BEGIN FUNCTION EXPRESSION *) fn ops'' =>  ordltLex (G, L, L', sc, ops'') (* GEN END FUNCTION EXPRESSION *), ops')
        end (* GEN END FUN BRANCH *)

    (* ordltSimul (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
    and (* GEN BEGIN FUN FIRST *) ordltSimul (G, nil, nil, sc, ops) = ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordltSimul (G, O :: L, O' :: L', sc, ops) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ops'' = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => ordlt (G, O, O',
                        (* GEN BEGIN FUNCTION EXPRESSION *) fn ops' => ordleSimul (G, L, L', sc, ops') (* GEN END FUNCTION EXPRESSION *), ops) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          ordeq (G, O, O', (* GEN BEGIN FUNCTION EXPRESSION *) fn ops' => ordltSimul (G, L, L', sc, ops') (* GEN END FUNCTION EXPRESSION *), ops'')
        end (* GEN END FUN BRANCH *)

    (* ordleSimul (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
    and (* GEN BEGIN FUN FIRST *) ordleSimul (G, nil, nil, sc, ops) = sc ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordleSimul (G, O :: L, O' :: L', sc, ops) =
          ordle (G, O, O', (* GEN BEGIN FUNCTION EXPRESSION *) fn ops' => ordleSimul (G, L, L', sc, ops') (* GEN END FUNCTION EXPRESSION *), ops) (* GEN END FUN BRANCH *)


    (* ordeq (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
    and (* GEN BEGIN FUN FIRST *) ordeq (G, O.Arg (Us, Vs), O.Arg (Us' ,Vs'), sc, ops) =
          if Unify.unifiable (G, Vs, Vs') andalso Unify.unifiable (G, Us, Us') then sc ops else ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordeq (G, O.Lex L, O.Lex L', sc, ops) = ordeqs (G, L, L', sc, ops) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ordeq (G, O.Simul L, O.Simul L', sc, ops) = ordeqs (G, L, L', sc, ops) (* GEN END FUN BRANCH *)

    (* ordlteqs (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
    and (* GEN BEGIN FUN FIRST *) ordeqs (G, nil, nil, sc, ops) = sc ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordeqs (G, O :: L, O' :: L', sc, ops) =
          ordeq (G, O, O', (* GEN BEGIN FUNCTION EXPRESSION *) fn ops' => ordeqs (G, L, L', sc, ops') (* GEN END FUNCTION EXPRESSION *), ops) (* GEN END FUN BRANCH *)

    (* ordeq (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
1           recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
    and ordle (G, O, O', sc, ops) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ops' = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => ordeq (G, O, O', sc, ops) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          ordlt (G, O, O', sc, ops')
        end

    (* createEVars (G, M) = ((G', M'), s')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
    *)
    fun (* GEN BEGIN FUN FIRST *) createEVars (M.Prefix (I.Null, I.Null, I.Null)) =
          (M.Prefix (I.Null, I.Null, I.Null), I.id) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createEVars (M.Prefix (I.Decl (G, D), I.Decl (M, M.Top), I.Decl (B, b))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (M.Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B)) (* GEN END TAG OUTSIDE LET *)
        in
          (M.Prefix (I.Decl (G', I.decSub (D, s')), I.Decl (M', M.Top), I.Decl (B', b)),
           I.dot1 s')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) createEVars (M.Prefix (I.Decl (G, I.Dec (_, V)), I.Decl (M, M.Bot), I.Decl (B, _))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (M.Prefix (G', M', B'), s') = createEVars (M.Prefix (G, M, B)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X  = I.newEVar (G', I.EClo (V, s')) (* GEN END TAG OUTSIDE LET *)
        in
          (M.Prefix (G', M', B'), I.Dot (I.Exp (X), s'))
        end (* GEN END FUN BRANCH *)

    (* select (G, (V, s)) = (G', (V1', s1'), (V2', s2'))

     Invariant:
     If   G |- s : G1   G1 |- V : type
     and  G |- V [s] = {V1} ... {Vn} a S
     then G' = G, V1 .. Vn
     and  G' |- s1' : G1'   G1' |- V1' : type
     and  G' |- s2' : G2'   G2' |- V2' : type
     and  G' |- V1' [s1'] = V1 [^n]
     and  G' |- V2' [s2'] = a S
    *)
    fun select (G, Vs) = selectW (G, (Whnf.whnf Vs))
    and selectW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
        let
          fun select' (G, (Vs1, Vs2)) =
              selectW' (G, (Vs1, Whnf.whnf Vs2))
          and (* GEN BEGIN FUN FIRST *) selectW' (G, (Vs1, Vs2 as (I.Root _, _))) = (G, (Vs1, Vs2)) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) selectW' (G, ((V1, s1), (I.Pi ((D, P), V2'), s2))) =
                select' (I.Decl (G, I.decSub (D, s2)), ((V1, I.comp (s1, I.shift)),
                                                        (V2', I.dot1 s2))) (* GEN END FUN BRANCH *)
        in
          select' (I.Decl (G, I.decSub (D, s)) , ((V1, I.comp (s, I.shift)), (V2, I.dot1 s)))
        end

    (* lemma (S, t, ops) = (G', P', P'', abstract', ops')

       Invariant:
       If   S state  (S = ((G, M), V)
                     |- G ctx
                     G |- M mtx
                     G |- V = {V1} ... {Vn} a S)
       and  S' state derived from S by an inductive call to t
       and  ops a list of operators
       then G is context, where all - variables are replaced by EVars in S'
       and  P' is induction variable vector of EVars in the inductive call
       and  P'' is induction variable vector of the theorem S.
       and  G' |- P' : (V1' .. Vn')
              (where  t : {W1} ..{Wm} b S, and Vi' are among W1 .. Wm)
       and  G'' |- P'' : (V1'' .. Vn'')
              (where  a : {W1} ..{Wm} b S, and Vi'' are among W1 .. Wm)

    *)
    fun lemma (S, t, ops) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val M.State (name, GM, V) = Lemma.apply (S, t) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (M.Prefix (G', M', B'), s') = createEVars GM (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (G'', ((I.Root (I.Const a1, S1), s1),
                     (I.Root (I.Const a2, S2), s2))) = select (G', (V, s')) (* GEN END TAG OUTSIDE LET *)
        in
          (G'', vector (a1, (S1, s1)), vector (a2, (S2, s2)),
           (* GEN BEGIN FUNCTION EXPRESSION *) fn ops' => ((MetaAbstract.abstract (M.State (name, M.Prefix (G', M', B'),
                                                        I.EClo (V, s')))) :: ops') (* GEN END FUNCTION EXPRESSION *), ops)
        end

    (* expandLazy' (S, L, ops) = ops'

       Invariant:
       If   S state
       and  L list of mutual recursive type families
       and  ops a list of operators
       then ops' extends ops by all operators
         representing inductive calls to theorems in L
    *)
    fun (* GEN BEGIN FUN FIRST *) expandLazy' (S, O.Empty, ops) = ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) expandLazy' (S, (O.LE (t, L)), ops) = expandLazy' (S, L, ordle (lemma (S, t, ops))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) expandLazy' (S, (O.LT (t, L)), ops) = expandLazy' (S, L, ordlt (lemma (S, t, ops))) (* GEN END FUN BRANCH *)


    fun recursionDepth V =
        let
          fun (* GEN BEGIN FUN FIRST *) recursionDepth' (I.Root _, n) = n (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) recursionDepth' (I.Pi (_, V), n) = recursionDepth' (V, n+1) (* GEN END FUN BRANCH *)
        in
          recursionDepth' (V, 0)
        end

    (* expandLazy S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (only induction variables are instantiated)
    *)
    fun expandLazy (S as M.State (_, _, V)) =
        if recursionDepth V > (!MetaGlobal.maxRecurse) then nil
        else expandLazy' (S, (O.mutLookup (I.targetFam  V)), nil)


    (* inputConv ((V1, s1), (V2, s2)) = B

       Invariant:
       If  G |- s1 : G1   G1 |- V1 : L
       and G |- s2 : G2   G2 |- V2 : L
       and G |- V1[s1] = c1 ; S1
       and G |- V2[s2] = c2 ; S2
       then B' holds iff c1 =  c2 and V1[s1] ==+ V2[s2]   (convertible on + arguments of c1)
    *)
    fun inputConv (Vs1, Vs2) = inputConvW (Whnf.whnf Vs1, Whnf.whnf Vs2)
    and inputConvW ((I.Root (I.Const c1, S1), s1), (I.Root (I.Const c2, S2), s2)) =
          (* s1 = s2 = id *)
          if c1 = c2 then inputConvSpine (valOf (ModeTable.modeLookup c1),
                                          ((S1, s1), (I.constType c1, I.id)),
                                          ((S2, s2), (I.constType c2, I.id)))
          else false

    and (* GEN BEGIN FUN FIRST *) inputConvSpine (ModeSyn.Mnil, ((S1, _), _), ((S2, _), _)) = true (* GEN END FUN FIRST *) (* S1 = S2 = Nil *)
      | (* GEN BEGIN FUN BRANCH *) inputConvSpine (mS, ((I.SClo (S1, s1'), s1), Vs1), (Ss2, Vs2)) =
          inputConvSpine (mS, ((S1, I.comp (s1', s1)), Vs1), (Ss2, Vs2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inputConvSpine (mS, (Ss1, Vs1), ((I.SClo (S2, s2'), s2), Vs2)) =
          inputConvSpine (mS, (Ss1, Vs1), ((S2, I.comp (s2', s2)), Vs2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inputConvSpine (ModeSyn.Mapp (ModeSyn.Marg (ModeSyn.Minus, _), mS),
                        ((I.App (U1, S1), s1), (I.Pi ((I.Dec (_, V1), _), W1), t1)),
                        ((I.App (U2, S2), s2), (I.Pi ((I.Dec (_, V2), _), W2), t2))) =
          Conv.conv ((V1, t1), (V2, t2)) andalso
          inputConvSpine (mS,
                          ((S1, s1), (W1, I.Dot (I.Exp (I.EClo (U1, s1)), t1))),
                          ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U1, s1)), t2)))) (* GEN END FUN BRANCH *)
          (* BUG: use the same variable (U1, s1) to continue comparing! --cs
                  in ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U2, s2), V2), t2))))
             FIXED: --cs Mon Nov  9 19:38:55 EST 1998 *)
        | (* GEN BEGIN FUN BRANCH *) inputConvSpine (ModeSyn.Mapp (ModeSyn.Marg (ModeSyn.Plus, _), mS),
                        ((I.App (U1, S1), s1), (I.Pi ((I.Dec (_, V1), _), W1), t1)),
                        ((I.App (U2, S2), s2), (I.Pi ((I.Dec (_, V2), _), W2), t2))) =
           inputConvSpine (mS,
                          ((S1, s1), (W1, I.Dot (I.Exp (I.EClo (U1, s1)), t1))),
                          ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U2, s2)), t2)))) (* GEN END FUN BRANCH *)


    (* removeDuplicates ops = ops'

       Invariant:
       If   ops is a list of recursion operators,
       then ops' is a sublist of ops, s.t.
         forall S = ((G, M), V) in ops'
               |- G ctx
               G |- M mtx
               G |- V = {V0} .. {Vn} a ; S : type
               and Vi = ci ; S'
               and forall 1 <= i <= n:
                 either ci =/= c0 orelse
                 G, V0 .. Vi |- V0 [^ i] =/=+ Vi (not convertible on + arguments on c0)
    *)
    fun (* GEN BEGIN FUN FIRST *) removeDuplicates nil = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) removeDuplicates (S' :: ops) =
        let
          fun compExp (Vs1, Vs2) =
                compExpW (Whnf.whnf Vs1, Whnf.whnf Vs2)
          and (* GEN BEGIN FUN FIRST *) compExpW (Vs1, (I.Root _, _)) = false (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) compExpW (Vs1 as (V1, s1), (I.Pi ((D2, _), V2), s2)) =
                compDec (Vs1, (D2, s2))
                orelse compExp ((V1, I.comp (s1, I.shift)), (V2, I.dot1 s2)) (* GEN END FUN BRANCH *)
      
          and compDec (Vs1, (I.Dec (_, V2), s2)) =
                inputConv (Vs1, (V2, s2))
      
          fun check (M.State (name, GM, V)) = checkW (Whnf.whnf (V, I.id))
          and checkW (I.Pi ((D, _), V), s) =
                checkDec ((D, I.comp (s, I.shift)), (V, I.dot1 s))
          and checkDec ((I.Dec (_, V1), s1), Vs2) =
                compExp ((V1, s1), Vs2)
        in
          if check S' then removeDuplicates ops
          else S' :: (removeDuplicates ops)
        end (* GEN END FUN BRANCH *)

    (* fillOps ops = ops'

       Invariant:
       If   ops is a list of lazy recursion operators
       then ops' is a list of recursion operators combined with a filling
         operator to fill non-index variables.
    *)
    fun (* GEN BEGIN FUN FIRST *) fillOps nil = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fillOps (S' :: ops) =
        let
          fun (* GEN BEGIN FUN FIRST *) fillOps' nil = nil (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) fillOps' (O :: _) = (Filling.apply O) (* GEN END FUN BRANCH *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val (fillop, _) = Filling.expand S' (* GEN END TAG OUTSIDE LET *)
        in
          (fillOps' fillop) @ (fillOps ops)
        end (* GEN END FUN BRANCH *)

    (* expandEager S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (all variables of recursive call are instantiated)
    *)
    fun expandEager S = removeDuplicates (fillOps (expandLazy S))

    fun apply S = S

    fun menu (S as M.State (name, M.Prefix (G', M', B'), I.Pi ((I.Dec (_, V), _), _))) =
      "Recursion : " ^ (Print.expToString (G', V))

    fun handleExceptions f P =
        (f P) handle Order.Error s => raise Error s

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val expandLazy = handleExceptions expandLazy (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val expandEager = handleExceptions expandEager (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val apply = apply (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val menu = menu (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor Recursion *)
