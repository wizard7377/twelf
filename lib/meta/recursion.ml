(* Meta Recursion Version 1.3 *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)

functor (* GEN BEGIN FUNCTOR DECL *) MTPRecursion (structure MTPGlobal : MTPGLOBAL
                      structure Global : GLOBAL
                      (*! structure IntSyn : INTSYN !*)
                      (*! structure FunSyn : FUNSYN !*)
                      (*! sharing FunSyn.IntSyn = IntSyn !*)
                      structure StateSyn' : STATESYN
                      (*! sharing StateSyn'.IntSyn = IntSyn !*)
                      (*! sharing StateSyn'.FunSyn = FunSyn !*)
                      structure Abstract : ABSTRACT
                      (*! sharing Abstract.IntSyn = IntSyn !*)
                      structure MTPAbstract : MTPABSTRACT
                      (*! sharing MTPAbstract.IntSyn = IntSyn !*)
                      (*! sharing MTPAbstract.FunSyn = FunSyn !*)
                        sharing MTPAbstract.StateSyn = StateSyn'
                      structure FunTypeCheck : FUNTYPECHECK
                      (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
                        sharing FunTypeCheck.StateSyn = StateSyn'
                      structure MTPrint : MTPRINT
                        sharing MTPrint.StateSyn = StateSyn'
                      structure Whnf : WHNF
                      (*! sharing Whnf.IntSyn = IntSyn !*)
                      structure Unify : UNIFY
                      (*! sharing Unify.IntSyn = IntSyn !*)
                      structure Conv : CONV
                      (*! sharing Conv.IntSyn = IntSyn !*)
                      structure Names : NAMES
                      (*! sharing Names.IntSyn = IntSyn !*)
                      structure Subordinate : SUBORDINATE
                      (*! sharing Subordinate.IntSyn = IntSyn !*)
                      structure Print : PRINT
                      (*! sharing Print.IntSyn = IntSyn !*)
                      structure TypeCheck : TYPECHECK
                      (*! sharing TypeCheck.IntSyn = IntSyn !*)
                      structure Formatter : FORMATTER
                      structure FunPrint :FUNPRINT
                      (*! sharing FunPrint.FunSyn = FunSyn !*)
                        sharing FunPrint.Formatter = Formatter
                        (*! structure CSManager : CS_MANAGER !*)
                      (*! sharing CSManager.IntSyn = IntSyn !*)

)  : MTPRECURSION =
struct

  structure StateSyn = StateSyn'

  exception Error of string

  type operator = StateSyn.state

  local
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn
    structure N = Names
    structure Fmt = Formatter
    structure A = MTPAbstract

    datatype dec =                      (* Newly created *)
      Lemma of int * F.for              (* Residual Lemma *)


    fun (* GEN BEGIN FUN FIRST *) closedCtx (I.Null) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) closedCtx (I.Decl (G, D)) =
        if Abstract.closedDec (G, (D, I.id)) then raise Domain
        else closedCtx G (* GEN END FUN BRANCH *)


    (*  spine n = S'

        Invariant:
        S' = n;..;1;Nil
     *)
    fun (* GEN BEGIN FUN FIRST *) spine 0 = I.Nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) spine n = I.App (I.Root (I.BVar n, I.Nil),  spine (n-1)) (* GEN END FUN BRANCH *)

    (* someEVars (G, G1, s) = s'

       Invariant:
       If  |- G ctx
       and  G |- s : G
       then G |- s' : G, G1
    *)
    fun (* GEN BEGIN FUN FIRST *) someEVars (G, nil, s) =  s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) someEVars (G, I.Dec (_, V) :: L, s) =
      someEVars(G, L, I.Dot (I.Exp (I.newEVar (G, I.EClo (V, s))), s)) (* GEN END FUN BRANCH *)



    (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx

       NOTE, should go into a different module. Code duplication!
    *)
    fun (* GEN BEGIN FUN FIRST *) ctxSub (nil, s) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxSub (D :: G, s) = I.decSub (D, s) :: ctxSub (G, I.dot1 s) (* GEN END FUN BRANCH *)



    (* appendCtx ((G1, B1), T, G2) = (G', B')

       Invariant:
       If   |- G1 ctx
       and  G1 |- B1 tags
       and  T tag
       and  G1 |- G2 ctx
       then |- G' = G1, G2 ctx
       and  G' |- B' tags
    *)
    fun (* GEN BEGIN FUN FIRST *) appendCtx (GB1, T, nil) = GB1 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) appendCtx ((G1, B1), T, D :: G2) =
          appendCtx ((I.Decl (G1, D), I.Decl (B1, T)), T, G2) (* GEN END FUN BRANCH *)



    (* createCtx ((G, B), ll, s) = ((G', B'), s', af')

     Invariant:
     If   |- G ctx
     and  G |- B tags
     and  . |- label list
     and  |- G1 ctx
     and  G |- s : G1

     then |- G' : ctx
     and  G' |- B' tags
     and  G' = G, G''
     and  G' |- s' : G1
     and  af : forall . |- AF aux formulas. Ex . |- AF' = {{G''}} AF  auxFor
     *)
    fun (* GEN BEGIN FUN FIRST *) createCtx ((G, B), nil, s) =
          ((G, B), s, (* GEN BEGIN FUNCTION EXPRESSION *) fn AF => AF (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createCtx ((G, B), n :: ll, s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val F.LabelDec (l, G1, G2) = F.labelLookup n (* GEN END TAG OUTSIDE LET *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val t = someEVars (G, G1, I.id) (* GEN END TAG OUTSIDE LET *)
                                          (* G |- s' : G1 *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G2' = ctxSub (G2, t) (* GEN END TAG OUTSIDE LET *)
                                          (* G |- G2' ctx *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', B') = appendCtx ((G, B), S.Parameter (SOME n), G2') (* GEN END TAG OUTSIDE LET *)
                                          (* . |- G' = G, G2' ctx *)
          (* GEN BEGIN TAG OUTSIDE LET *) val s' = I.comp (s, I.Shift (List.length  G2')) (* GEN END TAG OUTSIDE LET *)
                                          (* G' |- s'' : G0 *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (GB'', s'', af'') = createCtx ((G', B'), ll, s') (* GEN END TAG OUTSIDE LET *)
        in
          (GB'', s'', (* GEN BEGIN FUNCTION EXPRESSION *) fn AF => A.Block ((G, t, List.length G1, G2'), af'' AF) (* GEN END FUNCTION EXPRESSION *))
        end (* GEN END FUN BRANCH *)


    (* createEVars' (G, G0) = s'

       Invariant :
       If   |- G ctx
       and  |- G0 ctx
       then G |- s' : G0
       and  s' = X1 .. Xn where n = |G0|
    *)
    fun (* GEN BEGIN FUN FIRST *) createEVars (G, I.Null) = I.Shift (I.ctxLength G) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createEVars (G, I.Decl (G0, I.Dec (_, V))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val s = createEVars (G, G0) (* GEN END TAG OUTSIDE LET *)
        in
          I.Dot (I.Exp (I.newEVar (G, I.EClo (V, s))), s)
        end (* GEN END FUN BRANCH *)


    (* checkCtx (G, G2, (V, s)) = B'

       Invariant:
       If   |- G = G0, G1 ctx
       and  G |- G2 ctx
       and  G |- s : G0
       and  G0 |- V : L
       then B' holds iff
            G1 = V1 .. Vn and G, G1, V1 .. Vi-1 |- Vi unifies with V [s o ^i] : L
    *)
    fun (* GEN BEGIN FUN FIRST *) checkCtx (G, nil, (V2, s)) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkCtx (G, (D as I.Dec (_, V1)) :: G2, (V2, s)) =
          (CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => Unify.unifiable (G, (V1, I.id), (V2, s)) (* GEN END FUNCTION EXPRESSION *))
          orelse checkCtx (I.Decl (G, D), G2, (V2, I.comp (s, I.shift)))) (* GEN END FUN BRANCH *)


    (* checkLabels ((G', B'), V, ll, l) = lopt'

       Invariant:
       If   |- G' ctx
       and  G' |- B' ctx
       and  G' |- s : G0
       and  G0 |- V : type
       and  . |- ll label list
       and  . |- l label number
       then lopt' = NONE if no context block is applicable
       or   lopt' = SOME l' if context block l' is applicable

       NOTE: For this implementation we only pick the first applicable contextblock.
       It is not yet clear what should happen if there are inductive calls where more
       then one contextblocks are introduced --cs
    *)
    fun checkLabels ((G', B'), (V, s), ll (* as nil *), l) =
        if l < 0 then NONE
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val F.LabelDec (name, G1, G2) = F.labelLookup l (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val s = someEVars (G', G1, I.id) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val G2' = ctxSub (G2, s) (* GEN END TAG OUTSIDE LET *)
    
            (* GEN BEGIN TAG OUTSIDE LET *) val t = someEVars (G', G1, I.id) (* GEN END TAG OUTSIDE LET *)
                                          (* G' |- t : G1 *)
            (* GEN BEGIN TAG OUTSIDE LET *) val G2' = ctxSub (G2, t) (* GEN END TAG OUTSIDE LET *)
                                          (* G |- G2' ctx *)
          in
            if not (List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn l' => l = l' (* GEN END FUNCTION EXPRESSION *)) ll) andalso checkCtx (G', G2', (V, s)) then SOME l
            else checkLabels ((G', B'), (V, s), ll, l-1)
          end
(*      | checkLabels _ = NONE  (* more than one context block is introduced *) *)


    (* appendRL (Ds1, Ds2) = Ds'

       Invariant:
       Ds1, Ds2 are a list of residual lemmas
       Ds' = Ds1 @ Ds2, where all duplicates are removed
    *)
    fun (* GEN BEGIN FUN FIRST *) appendRL (nil, Ds) = Ds (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) appendRL ((L as Lemma (n, F)) :: Ds1, Ds2) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = appendRL (Ds1, Ds2) (* GEN END TAG OUTSIDE LET *)
        in
          if List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn (Lemma (n', F')) => (n = n') andalso F.convFor ((F, I.id), (F', I.id)) (* GEN END FUNCTION EXPRESSION *)) Ds'
            then Ds'
          else L :: Ds'
        end (* GEN END FUN BRANCH *)


    (* recursion ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) = Ds

       Invariant:

       If

       nih  is the id or the induction hypothesis
       |- Gall ctx
       Gall |- Fex : for        (Fex doesn't contain any universal quantifiers)
       Gall |- Oex : order

       and
       ncurrent is the id of the current proof goal
       |- G0 ctx
       G0 |- B0 tags
       . |- ll label list
       G0 |- Ocurrent order
       G0 |- H history
       G0 |- F formula

       then
       G0 |- Ds decs
    *)
    fun recursion ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val ((G', B'), s', af) = createCtx ((G0, B0), ll, I.id) (* GEN END TAG OUTSIDE LET *)
                                        (* G' |- s' : G0 *)
        (* GEN BEGIN TAG OUTSIDE LET *) val t' = createEVars (G', Gall) (* GEN END TAG OUTSIDE LET *)
                                        (* G' |- t' : Gall *)
        (* GEN BEGIN TAG OUTSIDE LET *) val AF = af (A.Head (G', (Fex, t'), I.ctxLength Gall)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Oex' =  S.orderSub (Oex, t') (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Ocurrent' = S.orderSub (Ocurrent, s') (* GEN END TAG OUTSIDE LET *)
    
        fun sc Ds =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val Fnew = A.abstractApproxFor AF (* GEN END TAG OUTSIDE LET *)
          in
            if List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn (nhist, Fhist) => nih = nhist andalso
                            F.convFor ((Fnew, I.id), (Fhist, I.id)) (* GEN END FUNCTION EXPRESSION *)) H then
              Ds
            else
              Lemma (nih, Fnew) :: Ds
          end
    
        fun ac ((G', B'), Vs, Ds) =
          (case checkLabels ((G', B'), Vs, ll, F.labelSize ()-1)
             of NONE => Ds
              | SOME l' =>
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = recursion ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), l' :: ll, Ocurrent, H, F)) (* GEN END TAG OUTSIDE LET *)
                  in
                    appendRL (Ds', Ds)
                  end)
    
      in
        if ncurrent < nih then ordle ((G', B'), Oex', Ocurrent', sc, ac, nil)
        else ordlt ((G', B'), Oex', Ocurrent', sc, ac, nil)
      end



    (* set_parameter (GB, X, k, sc, ac, S) = S'

       Invariant:
       appends a list of recursion operators to S after
       instantiating X with all possible local parameters (between 1 and k)
    *)
    and set_parameter (GB as (G1, B1), X as I.EVar (r, _, V, _), k, sc, ac, Ds) =
      let
        (* set_parameter' ((G, B), k, Ds) = Ds'
    
           Invariant:
           If    G1, D < G
        *)
        fun (* GEN BEGIN FUN FIRST *) set_parameter' ((I.Null, I.Null), _, Ds) =  Ds (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) set_parameter' ((I.Decl (G, D), I.Decl (B, S.Parameter _)), k, Ds) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val D' as I.Dec (_, V') = I.decSub (D, I.Shift (k)) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Ds' =
                CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                             if Unify.unifiable (G1, (V, I.id), (V', I.id))
                               andalso Unify.unifiable (G1, (X, I.id), (I.Root (I.BVar k, I.Nil), I.id))
                               then sc Ds
                             else Ds (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
            in
              set_parameter' ((G, B), k+1, Ds')
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) set_parameter' ((I.Decl (G, D), I.Decl (B, _)), k, Ds) =
              set_parameter' ((G, B), k+1, Ds) (* GEN END FUN BRANCH *)
      in
        set_parameter' (GB, 1, Ds)
      end



    (* ltinit (GB, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, ac, Ds) = Ds'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
                G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of all all possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators
    *)
    and ltinit (GB, k, (Us, Vs), UsVs', sc, ac, Ds) =
          ltinitW (GB, k, Whnf.whnfEta (Us, Vs), UsVs', sc, ac, Ds)
    and (* GEN BEGIN FUN FIRST *) ltinitW (GB, k, (Us, Vs as (I.Root _, _)), UsVs', sc, ac, Ds) =
          lt (GB, k, (Us, Vs), UsVs', sc, ac, Ds) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ltinitW ((G, B), k,
                 ((I.Lam (D1, U), s1), (I.Pi (D2, V), s2)),
                 ((U', s1'), (V', s2')),
                 sc, ac, Ds) =
          ltinit ((I.Decl (G, I.decSub (D1, s1) (* = I.decSub (D2, s2) *)),
                   I.Decl (B, S.Parameter NONE)), k+1,
                  ((U, I.dot1 s1), (V, I.dot1 s2)),
                  ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))),
                  sc, ac, Ds) (* GEN END FUN BRANCH *)


    (* lt (GB, k, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

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
       and  Ds is a set of already calculuate possible states
       and  sc is success continuation
           then Ds' is an extension of Ds, containing all
                recursion operators
    *)

    (* Vs is Root!!! *)
    (* (Us',Vs') may not be eta-expanded!!! *)
    and lt (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds) =
          ltW (GB, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, ac, Ds)
    and (* GEN BEGIN FUN FIRST *) ltW (GB, k, (Us, Vs), ((I.Root (I.Const c, S'), s'), Vs'), sc, ac, Ds) =
          ltSpine (GB, k, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, ac, Ds) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ltW (GB as (G, B), k, (Us, Vs), ((I.Root (I.BVar n, S'), s'), Vs'), sc, ac, Ds) =
      (*          if n <= k then  (* n must be a local variable *) *)
      (* k might not be needed any more: Check --cs *)
        (case I.ctxLookup (B, n)
           of S.Parameter _ =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V') = I.ctxDec (G, n) (* GEN END TAG OUTSIDE LET *)
             in
               ltSpine (GB, k, (Us, Vs), ((S', s'), (V', I.id)), sc, ac, Ds)
             end
         | S.Lemma _ => Ds) (* GEN END FUN BRANCH *)
      (*            else Ds *)
      | (* GEN BEGIN FUN BRANCH *) ltW (GB, _, _, ((I.EVar _, _), _), _, _, Ds) = Ds (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ltW (GB as (G, B), k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'),
                                                   (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, ac, Ds) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = Ds (* GEN END TAG OUTSIDE LET *) (* ctxBlock (GB, I.EClo (V1', s1'), k, sc, ac, Ds) *)
        in
          if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then
            let  (* enforce that X gets only bound to parameters *)
              (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1', s1')) (* GEN END TAG OUTSIDE LET *) (* = I.newEVar (I.EClo (V2', s2')) *)
              (* GEN BEGIN TAG OUTSIDE LET *) val sc' = (* GEN BEGIN FUNCTION EXPRESSION *) fn Ds'' => set_parameter (GB, X, k, sc, ac, Ds'') (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
            in
              lt (GB, k, ((U, s1), (V, s2)),
                  ((U', I.Dot (I.Exp (X), s1')),
                   (V', I.Dot (I.Exp (X), s2'))), sc', ac, Ds')
            end
          else
            if Subordinate.below (I.targetFam V1', I.targetFam V) then
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1', s1')) (* GEN END TAG OUTSIDE LET *) (* = I.newEVar (I.EClo (V2', s2')) *)
              in
                lt (GB, k, ((U, s1), (V, s2)),
                    ((U', I.Dot (I.Exp (X), s1')),
                     (V', I.Dot (I.Exp (X), s2'))), sc, ac, Ds')
              end
            else Ds'
        end (* GEN END FUN BRANCH *)

    and ltSpine (GB, k, (Us, Vs), (Ss', Vs'), sc, ac, Ds) =
          ltSpineW (GB, k, (Us, Vs), (Ss', Whnf.whnf Vs'), sc, ac, Ds)
    and (* GEN BEGIN FUN FIRST *) ltSpineW (GB, k, (Us, Vs), ((I.Nil, _), _), _, _, Ds) = Ds (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ltSpineW (GB, k, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc, ac, Ds) =
          ltSpineW (GB, k, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc, ac, Ds) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ltSpineW (GB, k, (Us, Vs), ((I.App (U', S'), s1'),
                                    (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), sc, ac, Ds) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = le (GB, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, ac, Ds) (* GEN END TAG OUTSIDE LET *)
        in
          ltSpine (GB, k, (Us, Vs), ((S', s1'),
                                     (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), sc, ac, Ds')
        end (* GEN END FUN BRANCH *)

    (* eq (GB, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators resulting from U[s1] = U'[s']
    *)
    and eq ((G, B), (Us, Vs), (Us', Vs'), sc, ac, Ds) =
            (CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                          if Unify.unifiable (G, Vs, Vs')
                            andalso Unify.unifiable (G, Us, Us')
                            then sc Ds
                          else Ds (* GEN END FUNCTION EXPRESSION *)))


    (* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

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
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators resulting from U[s1] <= U'[s']
    *)

    and le (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = eq (GB, (Us, Vs), (Us', Vs'), sc, ac, Ds) (* GEN END TAG OUTSIDE LET *)
        in
          leW (GB, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, ac, Ds')
        end

    and (* GEN BEGIN FUN FIRST *) leW (GB as (G, B), k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'),
                                                   (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, ac, Ds) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = ac (GB, (V1', s1'), Ds) (* GEN END TAG OUTSIDE LET *)
        in
          if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1', s1')) (* GEN END TAG OUTSIDE LET *) (* = I.newEVar (I.EClo (V2', s2')) *)
              (* GEN BEGIN TAG OUTSIDE LET *) val sc' = (* GEN BEGIN FUNCTION EXPRESSION *) fn Ds'' => set_parameter (GB, X, k, sc, ac, Ds'') (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
            (* enforces that X can only bound to parameter *)
            in
              le (GB, k, ((U, s1), (V, s2)),
                  ((U', I.Dot (I.Exp (X), s1')),
                   (V', I.Dot (I.Exp (X), s2'))), sc', ac, Ds')
            end
          else
            if Subordinate.below  (I.targetFam V1', I.targetFam V) then
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (V1', s1')) (* GEN END TAG OUTSIDE LET *) (* = I.newEVar (I.EClo (V2', s2')) *)
                (* GEN BEGIN TAG OUTSIDE LET *) val sc' = sc (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val Ds'' =  le (GB, k, ((U, s1), (V, s2)),
                                ((U', I.Dot (I.Exp (X), s1')),
                                 (V', I.Dot (I.Exp (X), s2'))), sc', ac, Ds') (* GEN END TAG OUTSIDE LET *)
    (*              val sc'' = fn Ds'' => set_parameter (GB, X, k, sc, ac, Ds'')   (* BUG -cs *)
                val Ds''' =  le (GB, k, ((U, s1), (V, s2)),
                                 ((U', I.Dot (I.Exp (X), s1')),
                                  (V', I.Dot (I.Exp (X), s2'))), sc'', ac, Ds'') *)
              in
                Ds''
              end
            else Ds'
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) leW (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds) = lt (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds) (* GEN END FUN BRANCH *)


    (* ordlt (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
    and (* GEN BEGIN FUN FIRST *) ordlt (GB, S.Arg UsVs, S.Arg UsVs', sc, ac, Ds) =  ltinit (GB, 0, UsVs, UsVs', sc, ac, Ds) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordlt (GB, S.Lex L, S.Lex L', sc, ac, Ds) = ordltLex (GB, L, L', sc, ac, Ds) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ordlt (GB, S.Simul L, S.Simul L', sc, ac, Ds) = ordltSimul (GB, L, L', sc, ac, Ds) (* GEN END FUN BRANCH *)


    (* ordltLex (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
    and (* GEN BEGIN FUN FIRST *) ordltLex (GB, nil, nil, sc, ac, Ds) = Ds (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordltLex (GB, O :: L, O' :: L', sc, ac, Ds) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => ordlt (GB, O, O', sc, ac, Ds) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          ordeq (GB, O, O', (* GEN BEGIN FUNCTION EXPRESSION *) fn Ds'' =>  ordltLex (GB, L, L', sc, ac, Ds'') (* GEN END FUNCTION EXPRESSION *), ac, Ds')
        end (* GEN END FUN BRANCH *)

    (* ordltSimul (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
    and (* GEN BEGIN FUN FIRST *) ordltSimul (GB, nil, nil, sc, ac, Ds) = Ds (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordltSimul (GB, O :: L, O' :: L', sc, ac, Ds) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Ds'' = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => ordlt (GB, O, O',
                                                  (* GEN BEGIN FUNCTION EXPRESSION *) fn Ds' => ordleSimul (GB, L, L', sc, ac, Ds') (* GEN END FUNCTION EXPRESSION *), ac, Ds) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          ordeq (GB, O, O', (* GEN BEGIN FUNCTION EXPRESSION *) fn Ds' => ordltSimul (GB, L, L', sc, ac, Ds') (* GEN END FUNCTION EXPRESSION *), ac, Ds'')
        end (* GEN END FUN BRANCH *)


    (* ordleSimul (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
    and (* GEN BEGIN FUN FIRST *) ordleSimul (GB, nil, nil, sc, ac, Ds) = sc Ds (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordleSimul (GB, O :: L, O' :: L', sc, ac, Ds) =
          ordle (GB, O, O', (* GEN BEGIN FUNCTION EXPRESSION *) fn Ds' => ordleSimul (GB, L, L', sc, ac, Ds') (* GEN END FUNCTION EXPRESSION *), ac, Ds) (* GEN END FUN BRANCH *)


    (* ordeq (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
    and (* GEN BEGIN FUN FIRST *) ordeq ((G, B), S.Arg (Us, Vs), S.Arg (Us' ,Vs'), sc, ac, Ds) =
        if Unify.unifiable (G, Vs, Vs') andalso Unify.unifiable (G, Us, Us') then sc Ds else Ds (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordeq (GB, S.Lex L, S.Lex L', sc, ac, Ds) = ordeqs (GB, L, L', sc, ac, Ds) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ordeq (GB, S.Simul L, S.Simul L', sc, ac, Ds) = ordeqs (GB, L, L', sc, ac, Ds) (* GEN END FUN BRANCH *)

    (* ordlteqs (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
    and (* GEN BEGIN FUN FIRST *) ordeqs (GB, nil, nil, sc, ac, Ds) = sc Ds (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ordeqs (GB, O :: L, O' :: L', sc, ac, Ds) =
          ordeq (GB, O, O', (* GEN BEGIN FUNCTION EXPRESSION *) fn Ds' => ordeqs (GB, L, L', sc, ac, Ds') (* GEN END FUNCTION EXPRESSION *), ac, Ds) (* GEN END FUN BRANCH *)

    (* ordeq (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
    and ordle (GB, O, O', sc, ac, Ds) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val Ds' = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => ordeq (GB, O, O', sc, ac, Ds) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          ordlt (GB, O, O', sc, ac, Ds')
        end


    (* skolem (n, (du, de), GB, w, F, sc) = (GB', s')

       Invariant:
       If   GB, Ds |- w : GB
       and  GB, G |- F formula
       and  du = #universal quantifiers in F
       and  de = #existential quantifiers in F
       and  sc is a continuation which
            for all GB, Ds |- s' : GB
            returns s''  of type  GB, Ds, G'[...] |- w'' : GB, G
            and     V''  mapping (GB, Ds, G'[...] |- V  type)  to (GB, Ds |- {G'[...]} V type)
            and     F''  mapping (GB, Ds, G'[...] |- F) to (GB, Ds |- {{G'[...]}} F formula)
       then GB' = GB, Ds'
       and  |Ds'| = de
       and  each declaration in Ds' corresponds to one existential quantifier in F
       and  GB' |- s' : GB
    *)

    fun (* GEN BEGIN FUN FIRST *) skolem ((du, de), GB, w, F.True, sc) = (GB, w) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) skolem ((du, de), GB, w, F.All (F.Prim D, F), sc) =
          skolem ((du+1, de), GB, w, F,
                  (* GEN BEGIN FUNCTION EXPRESSION *) fn (s, de') =>
                                        (* s'  :  GB, Ds |- s : GB   *)
                     let
                       (* GEN BEGIN TAG OUTSIDE LET *) val (s', V', F') = sc (s, de') (* GEN END TAG OUTSIDE LET *)
                                        (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
                                        (* V'  : maps (GB, Ds, G'[...] |- V type) to (GB, Ds |- {G'[...]} V type) *)
                                        (* F'  : maps (GB, Ds, G'[...] |- F for) to (GB, Ds |- {{G'[...]}} F for) *)
                     in
                       (I.dot1 s',
                                        (* _   : GB, Ds, G'[...], D[?] |- _ : GB, G, D *)
                        (* GEN BEGIN FUNCTION EXPRESSION *) fn V => V' (Abstract.piDepend ((Whnf.normalizeDec (D, s'), I.Meta), Whnf.normalize (V, I.id))) (* GEN END FUNCTION EXPRESSION *),
                                        (* _   : maps (GB, Ds, G'[....], D[?] |- V : type) to  (GB, Ds, |- {G[....], D[?]} V : type) *)
                        (* GEN BEGIN FUNCTION EXPRESSION *) fn F => F' (F.All (F.Prim (I.decSub (D, s')), F)) (* GEN END FUNCTION EXPRESSION *)
                                        (* _   : maps (GB, Ds, G'[....], D[?] |- F : for) to  (GB, Ds, |- {{G[....], D[?]}} F : for) *)
                        )
                     end (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) skolem ((du, de), (G, B), w, F.Ex (I.Dec (name, V), F), sc) =
                                        (* V   : GB, G |- V type *)
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (s', V', F') = sc (w, de) (* GEN END TAG OUTSIDE LET *)
                                        (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
                                        (* V'  : maps  (GB, Ds, G'[...] |- V : type)   to   (GB, Ds |- {G'[...]} V : type) *)
                                        (* F'  : maps  (GB, Ds, G'[...] |- F : for)    to   (GB, Ds |- {{G'[...]}} F : for) *)
      
            (* GEN BEGIN TAG OUTSIDE LET *) val V1 = I.EClo (V, s') (* GEN END TAG OUTSIDE LET *)
                                        (* V1  : GB, Ds, G'[...] |- V1 = V [s'] : type *)
            (* GEN BEGIN TAG OUTSIDE LET *) val V2 = Whnf.normalize (V' V1, I.id) (* GEN END TAG OUTSIDE LET *)
                                        (* V2  : GB, Ds |- {G'[...]} V2 : type *)
      
            (* GEN BEGIN TAG OUTSIDE LET *) val F1 = F.Ex (I.Dec (name, V1), F.True) (* GEN END TAG OUTSIDE LET *)
                                        (* F1  : GB, Ds, G'[...] |- F1 : for *)
            (* GEN BEGIN TAG OUTSIDE LET *) val F2 = F' F1 (* GEN END TAG OUTSIDE LET *)
                                        (* F2  : GB, Ds |- {{G'[...]}} F2 : for *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.doubleCheck then FunTypeCheck.isFor (G, F2) else () (* GEN END TAG OUTSIDE LET *)
      
            (* GEN BEGIN TAG OUTSIDE LET *) val D2 = I.Dec (NONE, V2) (* GEN END TAG OUTSIDE LET *)
                                        (* D2  : GB, Ds |- D2 : type *)
            (* GEN BEGIN TAG OUTSIDE LET *) val T2 = (case F2
                        of F.All _ => S.Lemma (S.RL)
                         | _ => S.Lemma (S.Splits (!MTPGlobal.maxSplit))) (* GEN END TAG OUTSIDE LET *)
                                        (* T2  : GB, Ds |- T2 : tag *)
          in
            skolem ((du, de+1), (I.Decl (G, D2), I.Decl (B, T2)), I.comp (w, I.shift), F,
                    (* GEN BEGIN FUNCTION EXPRESSION *) fn (s, de') =>
                                        (* s   : GB, Ds, D2 |- s : GB *)
                       let
                         (* GEN BEGIN TAG OUTSIDE LET *) val (s', V', F') = sc (s, de') (* GEN END TAG OUTSIDE LET *)
                                        (* s'  : GB, Ds, D2, G'[...] |- s' : GB, G *)
                                        (* V'  : maps (GB, Ds, D2, G'[...] |- V type) to (GB, Ds, D2 |- {G'[...]} V type) *)
                                        (* F'  : maps (GB, Ds, D2, G'[...] |- F for) to (GB, Ds, D2 |- {{G'[...]}} F for) *)
                          
                       in
                         (I.Dot (I.Exp (I.Root (I.BVar (du + (de' - de)), spine du)), s'),
                                        (* _ : GB, Ds, D2, G'[...] |- s'' : GB, G, D *)
                          V', F')
                       end (* GEN END FUNCTION EXPRESSION *))
          end (* GEN END FUN BRANCH *)


    (* updateState (S, (Ds, s))

       Invariant:
       G context
       G' |- S state
       G |- Ds new decs
       G' |- s : G
    *)
    fun (* GEN BEGIN FUN FIRST *) updateState (S, (nil, s)) = S (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) updateState (S as S.State (n, (G, B), (IH, OH), d, O, H, F), (Lemma (n', Frl') :: L, s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((G'', B''), s') = skolem ((0, 0), (G, B), I.id, F.forSub (Frl', s),
                                         (* GEN BEGIN FUNCTION EXPRESSION *) fn (s', _) => (s', (* GEN BEGIN FUNCTION EXPRESSION *) fn V' => V' (* GEN END FUNCTION EXPRESSION *), (* GEN BEGIN FUNCTION EXPRESSION *) fn F' => F' (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val s'' = I.comp (s, s') (* GEN END TAG OUTSIDE LET *)
        in
          updateState (S.State (n, (G'', B''), (IH, OH), d, S.orderSub (O, s'),
                                (n', F.forSub (Frl', s'')) ::
                                map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (n', F') => (n', F.forSub (F', s')) (* GEN END FUNCTION EXPRESSION *)) H, F.forSub (F, s')),
                       (L, s''))
        end (* GEN END FUN BRANCH *)


    (* selectFormula (n, G, (G0, F, O), S) = S'

       Invariant:
       If   G |- s : G0  and  G0 |- F formula and  G0 |- O order
       and  S is a state
       then S' is the state with
       sc returns with all addition assumptions/residual lemmas for a certain
       branch of the theorem.
    *)
    fun (* GEN BEGIN FUN FIRST *) selectFormula (n, (G0, F.All (F.Prim (D as I.Dec (_, V)), F), S.All (_, O)), S) =
          selectFormula (n, (I.Decl (G0, D), F, O), S) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) selectFormula (n, (G0, F.And (F1, F2), S.And (O1, O2)), S) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (n', S') = selectFormula (n, (G0, F1, O1), S) (* GEN END TAG OUTSIDE LET *)
        in
          selectFormula (n, (G0, F2, O2), S')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) selectFormula (nih, (Gall, Fex, Oex), S as S.State (ncurrent, (G0, B0), (_, _), _, Ocurrent, H, F)) =
        let
      
          (* GEN BEGIN TAG OUTSIDE LET *) val Ds = recursion ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), nil, Ocurrent, H, F)) (* GEN END TAG OUTSIDE LET *)
        in
          (nih+1, updateState (S, (Ds, I.id)))
        end (* GEN END FUN BRANCH *)

    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.doubleCheck) then FunTypeCheck.isState S else () (* GEN END TAG OUTSIDE LET *);
    
        (* GEN BEGIN TAG OUTSIDE LET *) val (_, S') = selectFormula (1, (I.Null, IH, OH), S) (* GEN END TAG OUTSIDE LET *)
      in
        S'
      end



    fun apply S =
      (if (!Global.doubleCheck) then FunTypeCheck.isState S else ();
       S)

    fun menu _ = "Recursion (calculates ALL new assumptions & residual lemmas)"

    fun handleExceptions f P =
        (f P) handle Order.Error s => raise Error s

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val expand = handleExceptions expand (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val apply = apply (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val menu = menu (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *); (* functor MTPRecursion *)
