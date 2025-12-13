(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga, Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) AbstractTabled ((*! structure IntSyn' : INTSYN !*)
                  structure Whnf    : WHNF
                  (*! sharing Whnf.IntSyn = IntSyn' !*)
                  structure Unify   : UNIFY
                  (*! sharing Unify.IntSyn = IntSyn' !*)
                  structure Constraints : CONSTRAINTS
                  (*! sharing Constraints.IntSyn = IntSyn' !*)
                  structure Subordinate : SUBORDINATE
                  (*! sharing Subordinate.IntSyn = IntSyn' !*)
                  structure Print : PRINT
                  (*! sharing Print.IntSyn = IntSyn' !*)
                  structure Conv    : CONV
                  (*! sharing Conv.IntSyn = IntSyn' !*)
                  (*! structure TableParam : TABLEPARAM !*)
                  (*! sharing TableParam.IntSyn = IntSyn' !*)
                      )
  : ABSTRACTTABLED =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure TableParam = TableParam !*)

  exception Error of string

  local
    structure I = IntSyn
    structure C = CompSyn

    datatype duplicates = AV of (I.exp * int) | FGN of int

    datatype seen_in = TypeLabel | Body

    datatype exist_vars = EV of I.exp

    fun (* GEN BEGIN FUN FIRST *) lengthSub (I.Shift n) = 0 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lengthSub (I.Dot(E, s)) = 1 + lengthSub s (* GEN END FUN BRANCH *)

    (*
       We write {{K}} for the context of K, where EVars have
       been translated to declarations and their occurrences to BVars.
       For each occurrence of EVar in U, we generate a distinct BVar together with
       a residual constraint. This enforces that the final abstraction of U is
       linear. However, we do not linearize the context G.

       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars in U are collected in K.
       In particular, . ||- U means U contains no EVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

    fun (* GEN BEGIN FUN FIRST *) compose'(IntSyn.Null, G) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) compose'(IntSyn.Decl(G', D), G) = IntSyn.Decl(compose'(G', G), D) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) isId (I.Shift(n)) = (n = 0) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isId (s as I.Dot(I.Idx n, s')) = isId' (s, 0) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isId (s as I.Dot(I.Undef, s')) = isId' (s, 0) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isId (I.Dot(I.Exp _ , s)) = false (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) isId' (I.Shift(n), k) = (n = k) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isId' (I.Dot(I.Idx(i), s), k) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val k' = k+1 (* GEN END TAG OUTSIDE LET *)
      in
        (i = k') andalso isId' (s, k')
      end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isId' (I.Dot(I.Undef, s), k) = isId' (s, k+1) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) equalCtx (I.Null, s, I.Null, s') = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) equalCtx (I.Decl(G, D), s, I.Decl(G', D'), s') =
      Conv.convDec((D, s), (D', s')) andalso (equalCtx (G, I.dot1 s, G', I.dot1 s')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalCtx (I.Decl(G, D), s, I.Null, s') = false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) equalCtx (I.Null, s, I.Decl(G', D'), s') = false (* GEN END FUN BRANCH *)


    (* eqEVar X Y = B
     where B iff X and Y represent same variable
     *)
    fun (* GEN BEGIN FUN FIRST *) eqEVarW (I.EVar (r1, _, _, _)) (EV (I.EVar (r2, _, _, _))) = (r1 = r2) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) eqEVarW _ _ = false (* GEN END FUN BRANCH *)

    fun eqEVar X1 (EV (X2)) =
      (* Sun Dec  1 14:04:17 2002 -bp  may raise exception
       if strengthening is applied,i.e. the substitution is not always id! *)
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (X1', s) = Whnf.whnf (X1, I.id) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (X2', s) = Whnf.whnf (X2, I.id) (* GEN END TAG OUTSIDE LET *)
      in
        eqEVarW X1' (EV (X2'))
      end

    (* a few helper functions to manage K *)
    (* member P K = B option *)
    fun member' P K =
        let fun (* GEN BEGIN FUN FIRST *) exists' (I.Null) = NONE (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) exists' (I.Decl(K',(l, EV(Y)))) = if P(EV(Y)) then SOME(l) else exists' (K') (* GEN END FUN BRANCH *)
        in
          exists' K
        end

    (* member P K = B option *)
    fun member P K =
        let fun (* GEN BEGIN FUN FIRST *) exists' (I.Null) = NONE (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) exists' (I.Decl(K',(i, Y))) = if P(Y) then SOME(i) else exists' (K') (* GEN END FUN BRANCH *)
        in
          exists' K
        end
    fun update' P K =
      let
        fun (* GEN BEGIN FUN FIRST *) update' (I.Null) = I.Null (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) update' (I.Decl(K',((label, Y)))) =
          if (P Y) then
            I.Decl(K', (Body, Y))
          else I.Decl(update' (K'), (label, Y)) (* GEN END FUN BRANCH *)
      in
        update' K
      end

    (* member P K = B option *)
    fun update P K =
      let
        fun (* GEN BEGIN FUN FIRST *) update' (I.Null) = I.Null (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) update' (I.Decl(K',((label, i), Y))) =
          if (P Y) then
            I.Decl(K', ((Body, i), Y))
          else I.Decl(update' (K'), ((label, i), Y)) (* GEN END FUN BRANCH *)
      in
        update' K
      end

    fun (* GEN BEGIN FUN FIRST *) or (I.Maybe, _) = I.Maybe (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) or (_, I.Maybe) = I.Maybe (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) or (I.Meta, _) = I.Meta (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) or (_, I.Meta) = I.Meta (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) or (I.No, I.No) = I.No (* GEN END FUN BRANCH *)


    (* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
    fun (* GEN BEGIN FUN FIRST *) occursInExp (k, I.Uni _) = I.No (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInExp (k, I.Pi (DP, V)) = or (occursInDecP (k, DP), occursInExp (k+1, V)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExp (k, I.Root (H, S)) = occursInHead (k, H, occursInSpine (k, S)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExp (k, I.Lam (D, V)) = or (occursInDec (k, D), occursInExp (k+1, V)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExp (k, I.FgnExp csfe) =
        I.FgnExpStd.fold csfe ((* GEN BEGIN FUNCTION EXPRESSION *) fn (U, DP) => or (DP, (occursInExp (k, Whnf.normalize (U, I.id)))) (* GEN END FUNCTION EXPRESSION *)) I.No (* GEN END FUN BRANCH *)
      (* no case for Redex, EVar, EClo *)

    and (* GEN BEGIN FUN FIRST *) occursInHead (k, I.BVar (k'), DP) =
        if (k = k') then I.Maybe
        else DP (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.Const _, DP) = DP (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.Def _, DP) = DP (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.FgnConst _, DP) = DP (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.Skonst _, I.No) = I.No (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.Skonst _, I.Meta) = I.Meta (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.Skonst _, I.Maybe) = I.Meta (* GEN END FUN BRANCH *)
      (* no case for FVar *)

    and (* GEN BEGIN FUN FIRST *) occursInSpine (_, I.Nil) = I.No (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInSpine (k, I.App (U, S)) = or (occursInExp (k, U), occursInSpine (k, S)) (* GEN END FUN BRANCH *)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    fun (* GEN BEGIN FUN FIRST *) piDepend (DPV as ((D, I.No), V)) = I.Pi DPV (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) piDepend (DPV as ((D, I.Meta), V)) = I.Pi DPV (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) piDepend ((D, I.Maybe), V) =
          I.Pi ((D, occursInExp (1, V)), V) (* GEN END FUN BRANCH *)

    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    fun (* GEN BEGIN FUN FIRST *) raiseType (I.Null, V) = V (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) reverseCtx (I.Null, G) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) reverseCtx (I.Decl(G, D), G') = reverseCtx(G, I.Decl(G', D)) (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) ctxToEVarSub (IntSyn.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxToEVarSub (IntSyn.Decl(G,IntSyn.Dec(_,A)), s) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = ctxToEVarSub (G, s) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X = IntSyn.newEVar (IntSyn.Null, I.EClo(A,s')) (* GEN END TAG OUTSIDE LET *)
      in
        IntSyn.Dot(IntSyn.Exp(X), s')
      end (* GEN END FUN BRANCH *)


    (* collectExpW ((Gs, ss), Gl, (U, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- U : V      (U,s) in whnf
                Gs |- ss : G  (Gs is the strengthened context and ss is the strengthening substitution)

       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K' contains all EVars in (U,s)
       and  DupVars' = DupVars, DupVars''
            where DupVars' contains all duplicates in (U,s)

      if flag = true
        then duplicates of EVars are collected in DupVars
        otherwise no duplicates are collected

      note : 1) we only need to collect duplicate occurrences of EVars
                if we need to linearize the term the EVars occur in.

             2) we do not linearize fgnExp
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    fun (* GEN BEGIN FUN FIRST *) collectExpW (Gss, Gl, (I.Uni L, s), K, DupVars, flag, d) = (K, DupVars) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectExpW (Gss, Gl, (I.Pi ((D, _), V), s), K, DupVars, flag, d) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (K',_) = collectDec (Gss, (D, s), (K, DupVars), d, false) (* GEN END TAG OUTSIDE LET *)
        in
          (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *)
          collectExp (Gss, I.Decl (Gl, I.decSub (D, s)), (V, I.dot1 s), K', DupVars, flag, d)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectExpW (Gss, Gl, (I.Root (_ , S), s), K, DupVars, flag, d) =
          collectSpine (Gss, Gl, (S, s), K, DupVars, flag, d) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) collectExpW (Gss, Gl, (I.Lam (D, U), s), K, DupVars, flag, d) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (K',_) = collectDec (Gss, (D, s), (K, DupVars), d, false) (* GEN END TAG OUTSIDE LET *)
          in
            collectExp (Gss, I.Decl (Gl, I.decSub (D, s)), (U, I.dot1 s), K', DupVars, flag, d+1)
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectExpW (Gss, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
          collectEVar (Gss, Gl, (X, s), K, DupVars, flag, d) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) collectExpW (Gss, Gl, (I.FgnExp csfe, s), K, DupVars, flag, d) =
        I.FgnExpStd.fold csfe
        ((* GEN BEGIN FUNCTION EXPRESSION *) fn (U, KD') =>
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val (K', Dup) = KD' (* GEN END TAG OUTSIDE LET *)
         in collectExp (Gss, Gl, (U, s), K', Dup, false, d)
         end (* GEN END FUNCTION EXPRESSION *)) (K, I.Decl(DupVars, FGN(d))) (* GEN END FUN BRANCH *)

      (* No other cases can occur due to whnf invariant *)


    (* collectExp (Gss, G, Gl, (U, s), K) = K'
       same as collectExpW  but  (U,s) need not to be in whnf
    *)
    and collectExp (Gss, Gl, Us, K, DupVars, flag, d) =
        collectExpW (Gss, Gl, Whnf.whnf Us, K, DupVars, flag, d)

    (* collectSpine (Gss, Gl, (S, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- S : V > P
                Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (S, s)
       and DupVars'' contains all duplicates in (S, s)
     *)
    and (* GEN BEGIN FUN FIRST *) collectSpine (Gss, Gl, (I.Nil, _), K, DupVars, flag, d) = (K, DupVars) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectSpine (Gss, Gl, (I.SClo(S, s'), s), K, DupVars, flag, d) =
          collectSpine (Gss, Gl, (S, I.comp (s', s)), K, DupVars, flag, d) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectSpine (Gss, Gl, (I.App (U, S), s), K, DupVars, flag, d) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val  (K', DupVars') =  collectExp (Gss, Gl, (U, s), K, DupVars, flag, d) (* GEN END TAG OUTSIDE LET *)
          in
            collectSpine (Gss, Gl, (S, s), K', DupVars', flag, d)
          end (* GEN END FUN BRANCH *)

    and collectEVarFapStr (Gss, Gl, ((X', V'), w), (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
        case member' (eqEVar X) K  of
          SOME(label) => (* we have seen X before *)
            (if flag
               then
                   collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   (* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar X) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *)
             (* since X has occurred before, we do not traverse its type V' *)
             else
               collectSub(Gss, Gl, s, K, DupVars, flag, d))
        | NONE =>
          let
    (*          val V' = raiseType (GX, V) (* inefficient! *)*)
            (* GEN BEGIN TAG OUTSIDE LET *) val label = if flag then Body else TypeLabel (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d) (* GEN END TAG OUTSIDE LET *)
          in
            collectSub(Gss, Gl, I.comp(w, s), I.Decl (K', (label, EV(X'))), DupVars', flag, d)
          end

    and collectEVarNFapStr (Gss, Gl, ((X', V'), w), (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
        case member' (eqEVar X) K  of
          SOME(label) =>
            (* we have seen X before, i.e. it was already strengthened *)
            (if flag
              then
                  collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                  (* -bp this is a possible optimization for the variant case
                   case label of
                   Body => (print "Collect DupVar\n"; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print "TypeLabel\n"
                      val K' = update' (eqEVar X) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*)
            else
              collectSub(Gss, Gl, s, K, DupVars, flag, d))
    
        | NONE =>
          let
            (* val V' = raiseType (GX, V) (* inefficient! *)*)
            (* GEN BEGIN TAG OUTSIDE LET *) val label = if flag then Body else TypeLabel (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d) (* GEN END TAG OUTSIDE LET *)
          in
            if flag
              then
                collectSub(Gss, Gl, I.comp(w, s), I.Decl(K', (label, EV(X'))), I.Decl(DupVars', AV(X', d)), flag, d)
            else
              collectSub(Gss, Gl, I.comp(w, s), I.Decl(K', (label, EV(X'))), DupVars', flag, d)
          end

    and collectEVarStr (Gss as (Gs, ss), Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val w = Subordinate.weaken (GX, I.targetFam V) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val iw = Whnf.invert w (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val GX' = Whnf.strengthen (iw, GX) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X' as I.EVar (r', _, _, _) = I.newEVar (GX', I.EClo (V, iw)) (* GEN END TAG OUTSIDE LET *) (* ? *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Unify.instantiateEVar (r, I.EClo (X', w), nil) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX', I.EClo (V, iw)) (* GEN END TAG OUTSIDE LET *)
      in
        if isId (I.comp(w, I.comp(ss, s))) (* equalCtx (Gs, I.id, GX', s) *)
          then (* fully applied *)
            collectEVarFapStr (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)
        else
          (* not fully applied *)
          collectEVarNFapStr (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)
      end

    (* X is fully applied pattern *)
    and collectEVarFap (Gss, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
        case (member (eqEVar X) K) of
          SOME(label) => (* we have seen X before *)
            (if flag
               then
                 collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 (*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *)
                (* since X has occurred before, we do not traverse its type V' *)
             else
                collectSub(Gss, Gl, s, K, DupVars, flag, d))
        | NONE =>
          let
            (* val _ = checkEmpty !cnstrs *)
            (* GEN BEGIN TAG OUTSIDE LET *) val label = if flag then Body else TypeLabel (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX, V) (* GEN END TAG OUTSIDE LET *) (* inefficient! *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d) (* GEN END TAG OUTSIDE LET *)
          in
            collectSub(Gss, Gl, s, I.Decl (K', (label, EV(X))), DupVars', flag, d)
          end

    and collectEVarNFap (Gss, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
        case member' (eqEVar X) K of
          SOME(label) =>
            (if flag
               then
                 collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 (* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *)
             else
               collectSub(Gss, Gl, s, K, DupVars, flag, d))
        | NONE =>
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val label = if flag then Body else TypeLabel (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX, V) (* GEN END TAG OUTSIDE LET *) (* inefficient! *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d) (* GEN END TAG OUTSIDE LET *)
          in
            if flag
              then
                collectSub(Gss, Gl, s, I.Decl(K', (label, EV(X))), I.Decl(DupVars, AV(X, d)), flag, d)
            else
              collectSub(Gss, Gl, s, I.Decl(K', (label, EV(X))), DupVars, flag, d)
          end

    and collectEVar (Gss, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
      if (!TableParam.strengthen) then
        collectEVarStr (Gss, Gl, (X, s), K, DupVars, flag, d)
      else
        if isId(s) (* equalCtx (compose'(Gl, G), s, GX, s)  *)
          then (* X is fully applied *)
            collectEVarFap (Gss, Gl, (X, s), K, DupVars, flag, d)
        else
          (* X is not fully applied *)
          collectEVarNFap (Gss, Gl, (X, s), K, DupVars, flag, d)

    (* collectDec (Gss, G, (x:V, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G |- s : G1     G1 |- V : L
            Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (V, s)
       and DupVars'' contains all duplicates in (S, s)
    *)
    and collectDec (Gss, (I.Dec (_, V), s), (K, DupVars), d, flag) =
      let
    (*      val (K',DupVars') =  collectExp (Gss, I.Null, (V, s), K, I.Null, false, d)*)
        (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') =  collectExp (Gss, I.Null, (V, s), K, DupVars, flag, d) (* GEN END TAG OUTSIDE LET *)
      in
        (K', DupVars')
      end


    (* collectSub (G, s, K, DupVars, flag) = (K', DupVars)

       Invariant:
       If    G |- s : G1

       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in s
       and DupVars'' contains all duplicates in s
    *)

    and (* GEN BEGIN FUN FIRST *) collectSub (Gss, Gl, I.Shift _, K, DupVars, flag, d) = (K, DupVars) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectSub (Gss, Gl, I.Dot (I.Idx _, s), K, DupVars, flag, d) =
        collectSub (Gss, Gl, s, K, DupVars, flag, d) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectSub (Gss, Gl, I.Dot (I.Exp (X as I.EVar (ref (SOME U), _, _, _)), s), K, DupVars, flag, d) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val U' = Whnf.normalize (U, I.id) (* GEN END TAG OUTSIDE LET *) (* inefficient? *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectExp (Gss, Gl, (U', I.id), K, DupVars, flag, d) (* GEN END TAG OUTSIDE LET *)
        in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
        end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) collectSub (Gss, Gl, I.Dot (I.Exp (U as I.AVar (ref (SOME U'))), s), K, DupVars, flag, d) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectExp (Gss, Gl, (U', I.id), K, DupVars, flag, d) (* GEN END TAG OUTSIDE LET *)
        in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
        end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) collectSub (Gss, Gl, I.Dot (I.Exp (I.EClo(U', s')), s), K, DupVars, flag, d) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val U = Whnf.normalize (U',s') (* GEN END TAG OUTSIDE LET *) (* inefficient? *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectExp (Gss, Gl, (U, I.id), K, DupVars, flag, d) (* GEN END TAG OUTSIDE LET *)
        in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
        end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) collectSub (Gss, Gl, I.Dot (I.Exp (U), s), K, DupVars, flag, d) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectExp (Gss, Gl, (U, I.id), K, DupVars, flag, d) (* GEN END TAG OUTSIDE LET *)
        in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectSub (Gss, Gl, I.Dot (I.Undef, s), K, DupVars, flag, d) =
        collectSub (Gss, Gl, s, K, DupVars, flag, d) (* GEN END FUN BRANCH *)

    (* collectCtx (Gss, G0, G, K) = (K', DupVars)
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars in G
    *)

    fun (* GEN BEGIN FUN FIRST *) collectCtx (Gss,C.DProg(I.Null, I.Null), (K, DupVars), d) =  (K, DupVars) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectCtx (Gss, C.DProg(I.Decl (G, D), I.Decl(dPool, C.Parameter)), (K, DupVars), d) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (K',DupVars') = collectCtx (Gss, C.DProg(G, dPool), (K, DupVars), d - 1) (* GEN END TAG OUTSIDE LET *)
        in
          collectDec (Gss, (D, I.id), (K', DupVars'), d - 1, false)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectCtx (Gss, C.DProg(I.Decl (G, D), I.Decl(dPool, C.Dec(r,s,Ha))), (K, DupVars), d) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectCtx (Gss, C.DProg(G, dPool), (K, DupVars), d - 1) (* GEN END TAG OUTSIDE LET *)
        in
          collectDec (Gss, (D, I.id), (K', DupVars'), d - 1, false)
        end (* GEN END FUN BRANCH *)


    (* abstractExpW (epos, apos, Vars, Gl, total, depth, (U, s), eqn) = (epos', apos', Vars', U', eqn')
      (abstraction and linearization of existential variables in (U,s))

       U' = {{U[s]}}_(K, Dup)

       Invariant:
       If     G, Gl |- U[s] : V and  U[s] is in whnf
       and   |Gl| = depth
             |Dup, K| = total

       and epos = (total(K) + l) - #replaced expressions in U    (generate no additional constraints)
       and apos = (total(Dup) + + total(K) + l) - #replaced expressions in U
                  (generate additional constraints (avars))

       and Vars'  = Vars, Vars''
           where Vars contains pairs ((label, i), EV X) of all EVars (EV X),
           where label refers to where we have seen the existential variable (typeLabel or body) and
           i corresponds to the bvar-index assigned to X in U[s]

       and   K ~ Vars (we can obtain K from Vars by dropping the first component of
             each pair (_, EV X) in Vars' )

       then   {{Dup}}, {{K}}  ||- U
       and {{Dup}} {{K}} , G, Gl |-  U' : V'
       and eqn' = eqn, eqn'' where eqn'' are residual equations relating between elements
           in {{K}} and {{Dup}}

       and . ||- Pi G. U'  and   U' is in nf

       if flag then linearize U else allow duplicates.

    *)

    fun (* GEN BEGIN FUN FIRST *) abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, (U as I.Uni (L), s), eqn) =
        (posEA, Vars, U, eqn) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, (I.Pi ((D, P), V), s), eqn) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', D, _) = abstractDec (Gs, posEA, Vars, Gl, total, depth, (D, s), NONE) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (posEA'', Vars'', V', eqn2) = abstractExp (flag, Gs, posEA', Vars', Gl, total, depth + 1, (V, I.dot1 s), eqn) (* GEN END TAG OUTSIDE LET *)
        in
          (posEA'', Vars'', piDepend ((D, P), V'),eqn2)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, (I.Root (H, S) ,s), eqn) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', S, eqn') = abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) (* GEN END TAG OUTSIDE LET *)
        in
          (posEA', Vars', I.Root (H, S), eqn')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, (I.Lam (D, U), s), eqn) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', D', _) = abstractDec (Gs, posEA, Vars, Gl, total, depth, (D, s), NONE) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (posEA'', Vars'', U', eqn2) = abstractExp (flag, Gs, posEA', Vars', I.Decl(Gl, D'), total, depth + 1, (U, I.dot1 s), eqn) (* GEN END TAG OUTSIDE LET *)
        in
          (posEA'', Vars'', I.Lam (D',U' ), eqn2)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (flag, Gs as (Gss, ss), posEA as (epos, apos), Vars, Gl, total, depth, (X as I.EVar (_, GX, VX, _), s), eqn) =
        (* X is possibly strengthened ! *)
        if  isId(I.comp(ss, s))
           then  (* X is fully applied *)
             abstractEVarFap (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn)
         else
           (* s =/= id, i.e. X is not fully applied *)
          abstractEVarNFap (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn) (* GEN END FUN BRANCH *)

(*      | abstractExpW (posEA, Vars, Gl, total, depth, (X as I.FgnExp (cs, ops), s), eqn) =  *)
(*      let
          val (X, _) = #map(ops) (fn U => abstractExp (posEA, Vars, Gl, total, depth, (U, s), eqn))
        in        abstractFgn (posEA, Vars, Gl, total, depth, X, eqn)
        end
*)

    (* abstractExp (posEA, Vars, Gl, total, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
    and abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, Us, eqn) =
        abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, Whnf.whnf Us, eqn)

    and abstractEVarFap (flag, Gs, posEA as (epos, apos), Vars, Gl, total, depth, (X, s), eqn) =
      case (member (eqEVar X) Vars) of
        SOME(label, i) =>  (* we have seen X before *)
          if flag then
            (* enforce linearization *)
            case label of
              Body =>
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val BV = I.BVar(apos + depth) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val BV' = I.BVar(i + depth) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val BV1 = I.BVar(apos + depth) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn) (* GEN END TAG OUTSIDE LET *)
                in
                  (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil), eqn1))
                end
            | TypeLabel =>
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val Vars' = update (eqEVar X) Vars (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn) (* GEN END TAG OUTSIDE LET *)
                in
                  (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                end
    
          else  (* do not enforce linearization -- used for type labels *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil, eqn) (* GEN END TAG OUTSIDE LET *)
            in
              (posEA', Vars', I.Root(I.BVar(i + depth), S), eqn1)
            end
         | NONE => (* we see X for the first time *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val label = if flag then Body else TypeLabel (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val BV = I.BVar(epos + depth) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val pos = (epos - 1, apos) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, pos, I.Decl(Vars, ((label, epos), EV X)), Gl, total, depth, s, I.Nil, eqn) (* GEN END TAG OUTSIDE LET *)
            in
              (posEA', Vars', I.Root(BV, S), eqn1)
            end

    and abstractEVarNFap (flag, Gs, posEA as (epos, apos), Vars, Gl, total, depth, (X, s), eqn) =
      case (member (eqEVar X) Vars) of
        SOME(label, i) =>  (* we have seen X before *)
          if flag then
            (* enforce linearization *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val BV = I.BVar(apos + depth) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val BV' = I.BVar(i + depth) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val BV1 = I.BVar(apos + depth) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn) (* GEN END TAG OUTSIDE LET *)
            in
              (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
            end
            (* (case label of
               Body =>
                 let
                  val _ = print "abstractEVarNFap -- flag true; we have seen X before\n"
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar X) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *)
          else (* do not enforce linearization -- used for type labels *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil, eqn) (* GEN END TAG OUTSIDE LET *)
            in
              (posEA', Vars', I.Root(I.BVar(i + depth), S), eqn1)
            end
         | NONE => (* we have not seen X before *)
           if flag then
             (* enforce linearization since X is not fully applied *)
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val label = if flag then Body else TypeLabel (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val BV = I.BVar(apos + depth) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val BV' = I.BVar(epos + depth) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val BV1 = I.BVar(apos + depth) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos - 1, apos - 1),  I.Decl(Vars, ((label, epos), EV X)), Gl, total, depth, s, I.Nil, eqn) (* GEN END TAG OUTSIDE LET *)
             in
               (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil), eqn1))
             end
           else (* do not enforce linearization -- used for type labels *)
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos - 1, apos),  I.Decl(Vars, ((TypeLabel, epos), EV X)), Gl, total, depth, s, I.Nil, eqn) (* GEN END TAG OUTSIDE LET *)
             in
               (posEA', Vars', I.Root(I.BVar(epos+depth), S), eqn1)
             end


    (* abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, S, eqn) = (posEA', Vars', S', eqn')

       (implicit raising)
       (for posEA, Vars, eqn explanation see above)

       let K* = K, Dup

       S' = {{s}}_K* @@ S

       Invariant:
       If    G, Gl |- s : G1
       and  |Gl| = depth

       and   {{Dup}} {{K}} ||- s
       then {{Dup}} {{K}}, G, Gl |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
    and (* GEN BEGIN FUN FIRST *) abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, I.Shift (k), S, eqn) =
        if k < depth
          then abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), S, eqn)
        else (* k = depth *) (posEA, Vars, S, eqn) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, I.Dot (I.Idx (k), s), S, eqn) =
          abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, I.App (I.Root (I.BVar (k), I.Nil), S), eqn) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, I.Dot (I.Exp (U), s), S, eqn) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', U', eqn') = abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, (U, I.id), eqn) (* GEN END TAG OUTSIDE LET *)
          in
            abstractSub (flag, Gs, posEA', Vars', Gl, total, depth, s, I.App (U', S), eqn')
          end (* GEN END FUN BRANCH *)


    (* abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) = (posEA', Vars', S', eqn')
       where S' = {{S[s]}}_K*   and K* = K, Dup

       Invariant:
       If   Gl, G |- s : G1     G1 |- S : V > P
       and  K* ||- S
       and  |G| = depth

       then {{K*}}, G, G |- S' : V' > P'
       and  . ||- S'
    *)

    and (* GEN BEGIN FUN FIRST *) abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (I.Nil, _), eqn)  =
        (posEA, Vars, I.Nil, eqn) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (I.SClo (S, s'), s), eqn) =
          abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, I.comp (s', s)), eqn) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (I.App (U, S), s), eqn) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', U', eqn') = abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, (U ,s), eqn) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (posEA'', Vars'', S', eqn'') = abstractSpine (flag, Gs, posEA', Vars', Gl, total, depth, (S, s), eqn') (* GEN END TAG OUTSIDE LET *)
          in
            (posEA'', Vars'', I.App (U', S'), eqn'')
          end (* GEN END FUN BRANCH *)


    (* abstractSub' (flag, Gs, epos, K, Gl, total, s) = (epos', K', s')      (implicit raising)

        Invariant:
        If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       and {{K}}, G |- {{s}}_K : G1
       then Gs, G |- s' : G1    where  s' == {{s}}_K

         *)

    and (* GEN BEGIN FUN FIRST *) abstractSub' (flag, Gs, epos, Vars, total, I.Shift (k)) =
        if k < 0
          then
            raise Error ("Substitution out of range\n")
        else
          (epos, Vars, I.Shift(k + total)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractSub' (flag, Gs, epos, Vars, total, I.Dot (I.Idx (k), s)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (epos', Vars', s') = abstractSub' (flag, Gs, epos, Vars, total, s) (* GEN END TAG OUTSIDE LET *)
          in
            (epos', Vars', I.Dot(I.Idx(k),s'))
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractSub' (flag, Gs, epos, Vars, total, I.Dot (I.Exp (U), s)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val ((ep, _), Vars', U', _) = abstractExp (false, Gs, (epos, 0), Vars, I.Null, total, 0, (U, I.id), TableParam.Trivial) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (epos'', Vars'', s') = abstractSub' (flag, Gs, ep, Vars', total, s) (* GEN END TAG OUTSIDE LET *)
          in
            (epos'', Vars'', I.Dot(I.Exp(U'), s'))
          end (* GEN END FUN BRANCH *)


    (* abstractDec (Gs, posEA, Vars, Gl, total, depth, (x:V, s)) = (posEA', Vars', x:V')
       where V = {{V[s]}}_K*

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K* ||- V
       and  |G| = depth

       then {{K*}}, G |- V' : L
       and  . ||- V'
    *)
    and (* GEN BEGIN FUN FIRST *) abstractDec (Gs, posEA, Vars, Gl, total, depth, (I.Dec (x, V), s), NONE) =
      let
    (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', V',eqn) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial) (* GEN END TAG OUTSIDE LET *)
      in
        (posEA', Vars', I.Dec (x, V'), eqn)
      end (* GEN END FUN FIRST *)

      | (* GEN BEGIN FUN BRANCH *) abstractDec (Gs, posEA, Vars, Gl, total, depth, (I.Dec (x, V), s), SOME(eqn)) =
      let
      (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
      
        (* GEN BEGIN TAG OUTSIDE LET *) val (posEA', Vars', V',eqn') = abstractExp (true, Gs, posEA, Vars, Gl, total, depth, (V, s), eqn) (* GEN END TAG OUTSIDE LET *)
      in
        (posEA', Vars', I.Dec (x, V'), eqn')
      end (* GEN END FUN BRANCH *)


    (* abstractCtx (Gs, epos, K, total, depth, C.DProg(G,dPool)) = (epos', K', G')
       where G' = {{G}}_K

       Invariants:
       If K ||- G
       and |G| = depth
       then {{K}} |- G' ctx
       and . ||- G'
       and epos = current epos

       note: we will linearize all dynamic assumptions in G.
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractCtx' (Gs, epos, Vars, total, depth, C.DProg(I.Null, I.Null), G', eqn) =
        (epos, Vars, G', eqn) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractCtx' (Gs, epos, Vars, total, depth, C.DProg(I.Decl (G, D), I.Decl(dPool, C.Parameter)), G', eqn) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val d = IntSyn.ctxLength (G) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((epos', _), Vars', D', _) = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), NONE) (* GEN END TAG OUTSIDE LET *)
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractCtx' (Gs, epos, Vars, total, depth, C.DProg(I.Decl (G, D), I.Decl(dPool, _)), G', eqn) =
      let
          (* GEN BEGIN TAG OUTSIDE LET *) val d = IntSyn.ctxLength (G) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ((epos', _), Vars', D', _) = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), NONE) (* GEN END TAG OUTSIDE LET *)
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn)
        end (* GEN END FUN BRANCH *)
(*        let
          val d = IntSyn.ctxLength (G)
          val ((epos', _), Vars', D', eqn') = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), SOME(eqn))
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn')
        end
*)
    fun abstractCtx (Gs, epos, Vars, total, depth, dProg) =
      abstractCtx' (Gs, epos, Vars, total, depth, dProg, I.Null, TableParam.Trivial)


    (* makeEVarCtx (Gs, Kall, D, K, eqn) = G'  *)
    fun (* GEN BEGIN FUN FIRST *) makeEVarCtx (Gs, Vars, DEVars, I.Null, total) = DEVars (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) makeEVarCtx (Gs, Vars, DEVars, I.Decl (K', (_, EV (E as I.EVar (_, GX, VX, _)))),total) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX, VX) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val ( _,Vars', V'', _) = abstractExp (false, Gs, (0, 0),  Vars, I.Null, 0,
                                                (total - 1), (V', I.id),  TableParam.Trivial) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val  DEVars' = makeEVarCtx (Gs, Vars', DEVars, K', total - 1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val DEVars'' = I.Decl (DEVars', I.Dec (NONE, V'')) (* GEN END TAG OUTSIDE LET *)
        in
          DEVars''
        end (* GEN END FUN BRANCH *)

    fun makeAVarCtx (Vars, DupVars) =
      let
        fun (* GEN BEGIN FUN FIRST *) avarCtx (Vars, I.Null, k) = I.Null (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) avarCtx (Vars, I.Decl (K', AV (E as I.EVar (ref NONE, GX, VX, _), d)), k) =
          I.Decl(avarCtx (Vars, K', k+1),
                 I.ADec (SOME("AVar "^Int.toString k ^ "--" ^ Int.toString d), d)) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) avarCtx (Vars, I.Decl (K', AV (E as I.EVar (_, GX, VX, _), d)), k) =
          I.Decl(avarCtx (Vars, K', k+1),
                 I.ADec (SOME("AVar "^Int.toString k ^ "--" ^ Int.toString d), d)) (* GEN END FUN BRANCH *)
      in
        avarCtx (Vars, DupVars, 0)
      end
      (* add case for foreign expressions ? *)

    (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
    fun (* GEN BEGIN FUN FIRST *) lowerEVar' (X, G, (I.Pi ((D',_), V'), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D'' = I.decSub (D', s') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (X', U) = lowerEVar' (X, I.Decl (G, D''), Whnf.whnf (V', I.dot1 s')) (* GEN END TAG OUTSIDE LET *)
        in
          (X', I.Lam (D'', U))
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lowerEVar' (X, G, Vs') =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val X' = X (* GEN END TAG OUTSIDE LET *)
        in
          (X', X')
        end (* GEN END FUN BRANCH *)
    (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
    and (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
      (* GEN BEGIN FUN FIRST *) lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (X', U) = lowerEVar' (X, G, (V,s)) (* GEN END TAG OUTSIDE LET *)
        in
          I.EVar(ref (SOME(U)), I.Null, V, ref nil)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lowerEVar1 (_, X, _) = X (* GEN END FUN BRANCH *)

    (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
    and
      (* GEN BEGIN FUN FIRST *) lowerEVar (E, X as I.EVar (r, G, V, ref nil)) = lowerEVar1 (E, X, Whnf.whnf (V, I.id)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lowerEVar (E, I.EVar _) =
        (* It is not clear if this case can happen *)
        (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
        raise Error "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified" (* GEN END FUN BRANCH *)


    (* evarsToSub (K, s') = s
      Invariant:
      if K = EV Xn ... EV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
    fun (* GEN BEGIN FUN FIRST *) evarsToSub (I.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) evarsToSub (I.Decl (K', (_, EV (E as I.EVar (I as (ref NONE), GX, VX, cnstr)))),s) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX, VX) (* GEN END TAG OUTSIDE LET *) (* redundant ? *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X = lowerEVar1 (E, I.EVar(I, I.Null, V', cnstr), Whnf.whnf(V', I.id)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = evarsToSub (K', s) (* GEN END TAG OUTSIDE LET *)
      in
        I.Dot(I.Exp(X), s')
      end (* GEN END FUN BRANCH *)

    (* evarsToSub (K, s') = s
      Invariant:
      if K = AV Xn ... AV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)

    fun (* GEN BEGIN FUN FIRST *) avarsToSub (I.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) avarsToSub (I.Decl (Vars', (AV (E as I.EVar (I, GX, VX, cnstr), d))), s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val s' = avarsToSub (Vars', s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X' as I.AVar(r) = I.newAVar () (* GEN END TAG OUTSIDE LET *)
        in
          I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s')
        end (* GEN END FUN BRANCH *)


  (* abstractEVarCtx (G, p, s) = (G', D', U', s')

     if G |- p[s] and s contains free variables X_n .... X_1
     then
       D' |- Pi  G' . U'
       where D' is the abstraction over the free vars X_n .... X_1

       and s' is a substitution the free variables
            X_n .... X_1, s.t.

       . |- s' : D'

       . |- (Pi G' .U' )[s']  is equivalent to . |- Pi G . p[s]

       Note: G' and U' are possibly strengthened
   *)

    fun abstractEVarCtx (dp as C.DProg(G,dPool), p, s) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (Gs, ss, d) =  (if (!TableParam.strengthen) then
                              let
                                (* GEN BEGIN TAG OUTSIDE LET *) val w' = Subordinate.weaken (G, I.targetFam p) (* GEN END TAG OUTSIDE LET *)
                                (* GEN BEGIN TAG OUTSIDE LET *) val iw = Whnf.invert w' (* GEN END TAG OUTSIDE LET *)
                                (* GEN BEGIN TAG OUTSIDE LET *) val G' = Whnf.strengthen (iw, G) (* GEN END TAG OUTSIDE LET *)
                                (* GEN BEGIN TAG OUTSIDE LET *) val d' = I.ctxLength (G') (* GEN END TAG OUTSIDE LET *)
                              in
                                (G', iw, d')
                              end
                            else
                              (G, I.id, I.ctxLength(G))) (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (K, DupVars) = collectCtx ((Gs, ss), dp, (I.Null, I.Null), d) (* GEN END TAG OUTSIDE LET *)
         (* K ||- G i.e. K contains all EVars in G *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (K', DupVars') = collectExp((Gs, ss), I.Null, (p, s), K, DupVars, true, d) (* GEN END TAG OUTSIDE LET *)
         (* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and G and
                                         DupVars' contains all duplicate EVars p[s] *)
         (* GEN BEGIN TAG OUTSIDE LET *) val epos = I.ctxLength(K') (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val apos = I.ctxLength(DupVars') (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val total = epos + apos (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (epos', Vars', G', eqn) = abstractCtx ((Gs,ss), epos, I.Null, total , d, dp) (* GEN END TAG OUTSIDE LET *)
         (* {{G}}_Vars' , i.e. abstract over the existential variables in G*)
         (* GEN BEGIN TAG OUTSIDE LET *) val (posEA'' (* = 0 *), Vars'', U', eqn') = abstractExp (true, (Gs, ss), (epos', total), Vars', I.Null,
                                                                  total, d, (p,s), eqn) (* GEN END TAG OUTSIDE LET *)
         (* abstract over existential variables in p[s] and linearize the expression *)
         (* GEN BEGIN TAG OUTSIDE LET *) val DAVars = makeAVarCtx (Vars'', DupVars') (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val DEVars = makeEVarCtx ((Gs, ss), Vars'', I.Null, Vars'', 0 (* depth *)) (* GEN END TAG OUTSIDE LET *)
         (* note: depth will become negative during makeEVarCtx *)
    
         (* GEN BEGIN TAG OUTSIDE LET *) val s' = avarsToSub (DupVars', I.id) (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val s'' = evarsToSub (Vars'', s') (* GEN END TAG OUTSIDE LET *)
    
         (* GEN BEGIN TAG OUTSIDE LET *) val G'' = reverseCtx (G', I.Null) (* GEN END TAG OUTSIDE LET *)
       in
         if (!TableParam.strengthen) then
           let
             (* GEN BEGIN TAG OUTSIDE LET *) val w' = Subordinate.weaken (G'', I.targetFam U') (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val iw = Whnf.invert w' (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val Gs' = Whnf.strengthen (iw, G'') (* GEN END TAG OUTSIDE LET *)
           in
             (Gs', DAVars, DEVars, U', eqn', s'')
           end
         else
           (G'', DAVars, DEVars, U', eqn', s'')
       end


  in

    (* GEN BEGIN TAG OUTSIDE LET *) val abstractEVarCtx = abstractEVarCtx (* GEN END TAG OUTSIDE LET *)

  (* abstractAnswSub s = (D', s')

   if  |- s : Delta' and s may contain free variables and
     D |- Pi G. U  and  |- s : D and  |- (Pi G . U)[s]
    then

    D' |- s' : D   where D' contains all the
    free variables from s
   *)

    (* GEN BEGIN TAG OUTSIDE LET *) val abstractAnswSub =
      ((* GEN BEGIN FUNCTION EXPRESSION *) fn s =>
       let
         (* no linearization for answer substitution *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (K, _ ) = collectSub((I.Null, I.id), I.Null, s, I.Null, I.Null, false, 0) (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val epos = I.ctxLength K (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (_ (*0 *), Vars, s') = abstractSub' (false, (I.Null, I.id), epos, I.Null, epos (* total *), s) (* GEN END TAG OUTSIDE LET *)
          
         (* GEN BEGIN TAG OUTSIDE LET *) val DEVars = makeEVarCtx ((I.Null, I.id), Vars, I.Null, Vars,  0) (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val s1' = ctxToEVarSub (DEVars, I.id) (* GEN END TAG OUTSIDE LET *)
       in
         (DEVars, s')
       end (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val raiseType = ((* GEN BEGIN FUNCTION EXPRESSION *) fn (G, U) =>
                       raiseType (G, U) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

  end
end (* GEN END FUNCTOR DECL *);  (* functor AbstractTabled *)



