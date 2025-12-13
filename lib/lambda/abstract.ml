(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) Abstract ((*! structure IntSyn' : INTSYN !*)
                  structure Whnf    : WHNF
                  (*! sharing Whnf.IntSyn = IntSyn' !*)
                  structure Unify   : UNIFY
                  (*! sharing Unify.IntSyn = IntSyn' !*)
                  structure Constraints : CONSTRAINTS
                    )
  : ABSTRACT =
struct

  exception Error of string

  local

    structure I = IntSyn
    structure T = Tomega
    structure C = Constraints
    structure O = Order

    (* Intermediate Data Structure *)

    datatype efl_var =
      EV of I.exp                       (* Y ::= X         for  GX |- X : VX *)
    | FV of string * I.exp              (*     | (F, V)        if . |- F : V *)
    | LV of I.block                     (*     | L             if . |- L in W *)
    | PV of T.prg                       (*     | P                            *)

    (*
       We write {{K}} for the context of K, where EVars, FVars, LVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and FVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or FVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

    (* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)
    fun (* GEN BEGIN FUN FIRST *) collectConstraints (I.Null) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectConstraints (I.Decl (G, FV _)) = collectConstraints G (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectConstraints (I.Decl (G, EV (I.EVar (_, _, _, ref nil)))) = collectConstraints G (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectConstraints (I.Decl (G, EV (I.EVar (_, _, _, ref cnstrL)))) =
        (C.simplify cnstrL) @ collectConstraints G (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectConstraints (I.Decl (G, LV _)) = collectConstraints G (* GEN END FUN BRANCH *)

    (* checkConstraints (K) = ()
       Effect: raises Constraints.Error(C) if K contains unresolved constraints
    *)
    fun checkConstraints (K) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val constraints = collectConstraints K (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = case constraints
                    of nil => ()
                     | _ => raise C.Error (constraints) (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end

    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    (*
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
           of nil => ()
            | _ => raise Error "Typing ambiguous -- unresolved constraints")
    *)
    (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
    fun (* GEN BEGIN FUN FIRST *) eqEVar (I.EVar (r1, _, _, _)) (EV (I.EVar (r2, _, _, _))) = (r1 = r2) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) eqEVar _ _ = false (* GEN END FUN BRANCH *)

    (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
    fun (* GEN BEGIN FUN FIRST *) eqFVar (I.FVar (n1, _, _)) (FV (n2,  _)) = (n1 = n2) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) eqFVar _ _ = false (* GEN END FUN BRANCH *)

    (* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)
    fun (* GEN BEGIN FUN FIRST *) eqLVar (I.LVar ((r1, _, _))) (LV (I.LVar ((r2, _, _)))) = (r1 = r2) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) eqLVar _ _ = false (* GEN END FUN BRANCH *)


    (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
    fun exists P K =
        let fun (* GEN BEGIN FUN FIRST *) exists' (I.Null) = false (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) exists' (I.Decl(K',Y)) = P(Y) orelse exists' (K') (* GEN END FUN BRANCH *)
        in
          exists' K
        end

    (* this should be non-strict *)
    (* perhaps the whole repeated traversal are now a performance
       bottleneck in PCC applications where logic programming search
       followed by abstraction creates certificates.  such certificates
       are large, so the quadratic algorithm is not really acceptable.
       possible improvement, collect, abstract, then traverse one more
       time to determine status of all variables.
    *)
    (* Wed Aug  6 16:37:57 2003 -fp *)
    (* !!! *)
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
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.Proj _, DP) = DP (* GEN END FUN BRANCH *)
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

    (* raiseTerm (G, U) = [[G]] U

       Invariant:
       If G |- U : V
       then  . |- [[G]] U : {{G}} V

       All abstractions are potentially dependent.
    *)
    fun (* GEN BEGIN FUN FIRST *) raiseTerm (I.Null, U) = U (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) raiseTerm (I.Decl (G, D), U) = raiseTerm (G, I.Lam (D, U)) (* GEN END FUN BRANCH *)

    (* collectExpW (G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and FVars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    fun (* GEN BEGIN FUN FIRST *) collectExpW (G, (I.Uni L, s), K) = K (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectExpW (G, (I.Pi ((D, _), V), s), K) =
          collectExp (I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), collectDec (G, (D, s), K)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectExpW (G, (I.Root (F as I.FVar (name, V, s'), S), s), K) =
        if exists (eqFVar F) K
          then collectSpine (G, (S, s), K)
        else (* s' = ^|G| *)
          collectSpine (G, (S, s), I.Decl (collectExp (I.Null, (V, I.id), K), FV (name, V))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectExpW (G, (I.Root (I.Proj (L as I.LVar (ref NONE, sk, (l, t)), i), S), s), K) =
          collectSpine (G, (S, s), collectBlock (G, I.blockSub (L, s), K)) (* GEN END FUN BRANCH *)
          (* BUG : We forget to deref L.  use collectBlock instead
             FPCHECK
             -cs Sat Jul 24 18:48:59 2010
            was:
      | collectExpW (G, (I.Root (I.Proj (L as I.LVar (r, sk, (l, t)), i), S), s), K) =
        if exists (eqLVar L) K
          (* note: don't collect t again below *)
          (* was: collectSpine (G, (S, s), collectSub (I.Null, t, K)) *)
          (* Sun Dec 16 10:54:52 2001 -fp !!! *)
          then collectSpine (G, (S, s), K)
        else
          (* -fp Sun Dec  1 21:12:12 2002 *)
        (* collectSpine (G, (S, s), I.Decl (collectSub (G, I.comp(t,s), K), LV L)) *)
        (* was :
         collectSpine (G, (S, s), collectSub (G, I.comp(t,s), I.Decl (K, LV L)))
         July 22, 2010 -fp -cs
         *)
            collectSpine (G, (S, s), collectSub (G, I.comp(t,I.comp(sk,s)),
                                                 I.Decl (K, LV L)))
*)      | (* GEN BEGIN FUN BRANCH *) collectExpW (G, (I.Root (_ , S), s), K) =
          collectSpine (G, (S, s), K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectExpW (G, (I.Lam (D, U), s), K) =
          collectExp (I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), collectDec (G, (D, s), K)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectExpW (G, (X as I.EVar (r, GX, V, cnstrs), s), K) =
        if exists (eqEVar X) K
          then collectSub(G, s, K)
        else let
               (* val _ = checkEmpty !cnstrs *)
               (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX, V) (* GEN END TAG OUTSIDE LET *) (* inefficient *)
               (* GEN BEGIN TAG OUTSIDE LET *) val K' = collectExp (I.Null, (V', I.id), K) (* GEN END TAG OUTSIDE LET *)
             in
               collectSub(G, s, I.Decl (K', EV (X)))
             end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectExpW (G, (I.FgnExp csfe, s), K) =
          I.FgnExpStd.fold csfe ((* GEN BEGIN FUNCTION EXPRESSION *) fn (U, K) => collectExp (G, (U, s), K) (* GEN END FUNCTION EXPRESSION *)) K (* GEN END FUN BRANCH *)
      (* No other cases can occur due to whnf invariant *)

    (* collectExp (G, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
    and collectExp (G, Us, K) = collectExpW (G, Whnf.whnf Us, K)

    (* collectSpine (G, (S, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
    and (* GEN BEGIN FUN FIRST *) collectSpine (G, (I.Nil, _), K) = K (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectSpine (G, (I.SClo(S, s'), s), K) =
          collectSpine (G, (S, I.comp (s', s)), K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectSpine (G, (I.App (U, S), s), K) =
          collectSpine (G, (S, s), collectExp (G, (U, s), K)) (* GEN END FUN BRANCH *)

    (* collectDec (G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
    and (* GEN BEGIN FUN FIRST *) collectDec (G, (I.Dec (_, V), s), K) =
          collectExp (G, (V, s), K) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectDec (G, (I.BDec (_, (_, t)), s), K) =
          (* . |- t : Gsome, so do not compose with s *)
          (* Sat Dec  8 13:28:15 2001 -fp *)
          (* was: collectSub (I.Null, t, K) *)
          collectSub (G, I.comp(t,s), K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectDec (G, (I.NDec _, s), K) = K (* GEN END FUN BRANCH *)

    (* collectSub (G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
    and (* GEN BEGIN FUN FIRST *) collectSub (G, I.Shift _, K) = K (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectSub (G, I.Dot (I.Idx _, s), K) = collectSub (G, s, K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectSub (G, I.Dot (I.Exp (U), s), K) =
          collectSub (G, s, collectExp (G, (U, I.id), K)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectSub (G, I.Dot (I.Block B, s), K) =
          collectSub (G, s, collectBlock (G, B, K)) (* GEN END FUN BRANCH *)
    (* next case should be impossible *)
    (*
      | collectSub (G, I.Dot (I.Undef, s), K) =
          collectSub (G, s, K)
    *)

    (* collectBlock (G, B, K) where G |- B block *)
    and (* GEN BEGIN FUN FIRST *) collectBlock (G, I.LVar (ref (SOME B), sk , _), K) =
          collectBlock (G, I.blockSub (B, sk), K) (* GEN END FUN FIRST *)
          (* collectBlock (B, K) *)
          (* correct?? -fp Sun Dec  1 21:15:33 2002 *)
      | (* GEN BEGIN FUN BRANCH *) collectBlock (G, L as I.LVar (_, sk, (l, t)), K) =
        if exists (eqLVar L) K
          then collectSub (G, I.comp(t,sk), K)
        else I.Decl (collectSub (G, I.comp(t,sk), K), LV L) (* GEN END FUN BRANCH *)
    (* was: t in the two lines above, July 22, 2010, -fp -cs *)
    (* | collectBlock (G, I.Bidx _, K) = K *)
    (* should be impossible: Fronts of substitutions are never Bidx *)
    (* Sat Dec  8 13:30:43 2001 -fp *)

    (* collectCtx (G0, G, K) = (G0', K')
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars and FVars in G
    *)
    fun (* GEN BEGIN FUN FIRST *) collectCtx (G0, I.Null, K) = (G0, K) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectCtx (G0, I.Decl (G, D), K) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G0', K') = collectCtx (G0, G, K) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val K'' = collectDec (G0', (D, I.id), K') (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (G0, D), K'')
        end (* GEN END FUN BRANCH *)

    (* collectCtxs (G0, Gs, K) = K'
       Invariant: G0 |- G1,...,Gn ctx where Gs = [G1,...,Gn]
       and K' = K, K'' where K'' contains all EVars and FVars in G1,...,Gn
    *)
    fun (* GEN BEGIN FUN FIRST *) collectCtxs (G0, nil, K) = K (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectCtxs (G0, G::Gs, K) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G0', K') = collectCtx (G0, G, K) (* GEN END TAG OUTSIDE LET *)
        in
          collectCtxs (G0', Gs, K')
        end (* GEN END FUN BRANCH *)

    (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractEVar (I.Decl (K', EV (I.EVar(r',_,_,_))), depth, X as I.EVar (r, _, _, _)) =
        if r = r' then I.BVar (depth+1)
        else abstractEVar (K', depth+1, X) (* GEN END FUN FIRST *)
(*      | abstractEVar (I.Decl (K', FV (n', _)), depth, X) =
          abstractEVar (K', depth+1, X) remove later --cs*)
      | (* GEN BEGIN FUN BRANCH *) abstractEVar (I.Decl (K', _), depth, X) =
          abstractEVar (K', depth+1, X) (* GEN END FUN BRANCH *)

    (* abstractFVar (K, depth, F) = C'

       Invariant:
       If   G |- F : V
       and  |G| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractFVar (I.Decl(K', FV (n', _)), depth, F as I.FVar (n, _, _)) =
          if n = n' then I.BVar (depth+1)
          else abstractFVar (K', depth+1, F) (* GEN END FUN FIRST *)
(*      | abstractFVar (I.Decl(K', EV _), depth, F) =
          abstractFVar (K', depth+1, F) remove later --cs *)
      | (* GEN BEGIN FUN BRANCH *) abstractFVar (I.Decl(K', _), depth, F) =
          abstractFVar (K', depth+1, F) (* GEN END FUN BRANCH *)

    (* abstractLVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractLVar (I.Decl(K', LV (I.LVar (r', _, _))), depth, L as I.LVar (r, _, _)) =
          if r = r' then I.Bidx (depth+1)
          else abstractLVar (K', depth+1, L) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractLVar (I.Decl(K', _), depth, L) =
          abstractLVar (K', depth+1, L) (* GEN END FUN BRANCH *)

    (* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractExpW (K, depth, (U as I.Uni (L), s)) = U (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (K, depth, (I.Pi ((D, P), V), s)) =
          piDepend ((abstractDec (K, depth, (D, s)), P),
                    abstractExp (K, depth + 1, (V, I.dot1 s))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (K, depth, (I.Root (F as I.FVar _, S), s)) =
          I.Root (abstractFVar (K, depth, F),
                  abstractSpine (K, depth, (S, s))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (K, depth, (I.Root (I.Proj (L as I.LVar _, i), S), s)) =
          I.Root (I.Proj (abstractLVar (K, depth, L), i),
                  abstractSpine (K, depth, (S, s))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (K, depth, (I.Root (H, S) ,s)) =
          I.Root (H, abstractSpine (K, depth, (S, s))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (K, depth, (I.Lam (D, U), s)) =
          I.Lam (abstractDec (K, depth, (D, s)),
                 abstractExp (K, depth + 1, (U, I.dot1 s))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (K, depth, (X as I.EVar _, s)) =
          I.Root (abstractEVar (K, depth, X),
                  abstractSub (K, depth, s, I.Nil)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractExpW (K, depth, (I.FgnExp csfe, s)) =
          I.FgnExpStd.Map.apply csfe ((* GEN BEGIN FUNCTION EXPRESSION *) fn U => abstractExp (K, depth, (U, s)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN BRANCH *)

    (* abstractExp (K, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
    and abstractExp (K, depth, Us) = abstractExpW (K, depth, Whnf.whnf Us)

    (* abstractSub (K, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_K @@ S

       Invariant:
       If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       then {{K}}, G |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
    and (* GEN BEGIN FUN FIRST *) abstractSub (K, depth, I.Shift (k), S) =
        if k < depth
          then abstractSub (K, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), S)
        else (* k = depth *) S (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractSub (K, depth, I.Dot (I.Idx (k), s), S) =
          abstractSub (K, depth, s, I.App (I.Root (I.BVar (k), I.Nil), S)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractSub (K, depth, I.Dot (I.Exp (U), s), S) =
          abstractSub (K, depth, s, I.App (abstractExp (K, depth, (U, I.id)), S)) (* GEN END FUN BRANCH *)

    (* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- S : V > P
       and  K ||- S
       and  |G| = depth

       then {{K}}, G |- S' : V' > P'
       and  . ||- S'
    *)
    and (* GEN BEGIN FUN FIRST *) abstractSpine (K, depth, (I.Nil, _))  = I.Nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractSpine (K, depth, (I.SClo (S, s'), s)) =
          abstractSpine (K, depth, (S, I.comp (s', s))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractSpine (K, depth, (I.App (U, S), s)) =
          I.App (abstractExp (K, depth, (U ,s)),
                 abstractSpine (K, depth, (S, s))) (* GEN END FUN BRANCH *)

    (* abstractDec (K, depth, (x:V, s)) = x:V'
       where V = {{V[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K ||- V
       and  |G| = depth

       then {{K}}, G |- V' : L
       and  . ||- V'
    *)
    and abstractDec (K, depth, (I.Dec (x, V), s)) =
          I.Dec (x, abstractExp (K, depth, (V, s)))

    (* abstractSOME (K, s) = s'
       s' = {{s}}_K

       Invariant:
       If    . |- s : Gsome
       and   K is internal context in dependency order
       and   K ||- s
       then  {{K}} |- s' : Gsome  --- not changing domain of s'

       Update: modified for globality invariant of . |- t : Gsome
       Sat Dec  8 13:35:55 2001 -fp
       Above is now incorrect
       Sun Dec  1 22:36:50 2002 -fp
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractSOME (K, I.Shift 0) = (* n = 0 by invariant, check for now *)
          I.Shift (I.ctxLength(K)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractSOME (K, I.Shift (n)) = (* n > 0 *)
          I.Shift (I.ctxLength(K)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractSOME (K, I.Dot (I.Idx k, s)) =
          I.Dot (I.Idx k, abstractSOME (K, s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractSOME (K, I.Dot (I.Exp U, s)) =
          I.Dot (I.Exp (abstractExp (K, 0, (U, I.id))), abstractSOME (K, s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractSOME (K, I.Dot (I.Block (L as I.LVar _), s)) =
          I.Dot (I.Block (abstractLVar (K, 0, L)), abstractSOME (K, s)) (* GEN END FUN BRANCH *)
      (* I.Block (I.Bidx _) should be impossible as head of substitutions *)

    (* abstractCtx (K, depth, G) = (G', depth')
       where G' = {{G}}_K

       Invariants:
       If G0 |- G ctx
       and K ||- G
       and |G0| = depth
       then {{K}}, G0 |- G' ctx
       and . ||- G'
       and |G0,G| = depth'
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractCtx (K, depth, I.Null) = (I.Null, depth) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractCtx (K, depth, I.Decl (G, D)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', depth') = abstractCtx (K, depth, G) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = abstractDec (K, depth', (D, I.id)) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (G', D'), depth'+1)
        end (* GEN END FUN BRANCH *)

    (* abstractCtxlist (K, depth, [G1,...,Gn]) = [G1',...,Gn']
       where Gi' = {{Gi}}_K

       Invariants:
       if G0 |- G1,...,Gn ctx
       and K ||- G1,...,Gn
       and |G0| = depth
       then {{K}}, G0 |- G1',...,Gn' ctx
       and . ||- G1',...,Gn'
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractCtxlist (K, depth, nil) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractCtxlist (K, depth, G::Gs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', depth') = abstractCtx (K, depth, G) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Gs' = abstractCtxlist (K, depth', Gs) (* GEN END TAG OUTSIDE LET *)
        in
          G'::Gs'
        end (* GEN END FUN BRANCH *)

    (* dead code under new reconstruction -kw
    (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    *)
    fun getLevel (I.Uni _) = I.Kind
      | getLevel (I.Pi (_, U)) = getLevel U
      | getLevel (I.Root _)  = I.Type
      | getLevel (I.Redex (U, _)) = getLevel U
      | getLevel (I.Lam (_, U)) = getLevel U
      | getLevel (I.EClo (U,_)) = getLevel U

    (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    *)
    fun checkType V =
        (case getLevel V
           of I.Type => ()
            | _ => raise Error "Typing ambiguous -- free type variable")
    *)

    (* abstractKPi (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractKPi (I.Null, V) = V (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractKPi (I.Decl (K', EV (I.EVar (_, GX, VX, _))), V) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX, VX) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V'' = abstractExp (K', 0, (V', I.id)) (* GEN END TAG OUTSIDE LET *)
          (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        in
          abstractKPi (K', I.Pi ((I.Dec(NONE, V''), I.Maybe), V))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractKPi (I.Decl (K', FV (name,V')), V) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V'' = abstractExp (K', 0, (V', I.id)) (* GEN END TAG OUTSIDE LET *)
          (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        in
          abstractKPi (K', I.Pi ((I.Dec(SOME(name), V''), I.Maybe), V))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractKPi (I.Decl (K', LV (I.LVar (r, _, (l, t)))), V) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = abstractSOME (K', t) (* GEN END TAG OUTSIDE LET *)
        in
          abstractKPi (K', I.Pi ((I.BDec (NONE, (l, t')), I.Maybe), V))
        end (* GEN END FUN BRANCH *)

    (* abstractKLam (K, U) = U'
       where U' = [[K]] U

       Invariant:
       If   {{K}} |- U : V
       and  . ||- U
       and  . ||- V

       then U' = [[K]] U
       and  . |- U' : {{K}} V
       and  . ||- U'
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractKLam (I.Null, U) = U (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractKLam (I.Decl (K', EV (I.EVar (_, GX, VX, _))), U) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX, VX) (* GEN END TAG OUTSIDE LET *)
        in
          abstractKLam (K', I.Lam (I.Dec(NONE, abstractExp (K', 0, (V', I.id))), U))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractKLam (I.Decl (K', FV (name,V')), U) =
          abstractKLam (K', I.Lam (I.Dec(SOME(name), abstractExp (K', 0, (V', I.id))), U)) (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) abstractKCtx (I.Null) = I.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractKCtx (I.Decl (K', EV (I.EVar (_, GX, VX, _)))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX, VX) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V'' = abstractExp (K', 0, (V', I.id)) (* GEN END TAG OUTSIDE LET *)
          (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        in
          I.Decl (abstractKCtx K', I.Dec (NONE, V''))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractKCtx (I.Decl (K', FV (name, V'))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V'' = abstractExp (K', 0, (V', I.id)) (* GEN END TAG OUTSIDE LET *)
          (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        in
          I.Decl (abstractKCtx K', I.Dec (SOME(name), V''))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractKCtx (I.Decl (K', LV (I.LVar (r, _, (l, t))))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = abstractSOME (K', t) (* GEN END TAG OUTSIDE LET *)
        in
          I.Decl (abstractKCtx K', I.BDec (NONE, (l, t')))
        end (* GEN END FUN BRANCH *)


    (* abstractDecImp V = (k', V')   (* rename --cs  (see above) *)

       Invariant:
       If    . |- V : L
       and   K ||- V

       then  . |- V' : L
       and   V' = {{K}} V
       and   . ||- V'
       and   k' = |K|
    *)
    fun abstractDecImp V =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val K = collectExp (I.Null, (V, I.id), I.Null) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkConstraints (K) (* GEN END TAG OUTSIDE LET *)
        in
          (I.ctxLength K, abstractKPi (K, abstractExp (K, 0, (V, I.id))))
        end

    (* abstractDef  (U, V) = (k', (U', V'))

       Invariant:
       If    . |- V : L
       and   . |- U : V
       and   K1 ||- V
       and   K2 ||- U
       and   K = K1, K2

       then  . |- V' : L
       and   V' = {{K}} V
       and   . |- U' : V'
       and   U' = [[K]] U
       and   . ||- V'
       and   . ||- U'
       and   k' = |K|
    *)
    fun abstractDef (U, V) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val K = collectExp (I.Null, (U, I.id), collectExp (I.Null, (V, I.id), I.Null)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkConstraints K (* GEN END TAG OUTSIDE LET *)
        in
          (I.ctxLength K, (abstractKLam (K, abstractExp (K, 0, (U, I.id))),
                           abstractKPi  (K, abstractExp (K, 0, (V, I.id)))))
        end


    fun abstractSpineExt (S, s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val K = collectSpine (I.Null, (S, s), I.Null) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkConstraints (K) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G = abstractKCtx (K) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val S = abstractSpine (K, 0, (S, s)) (* GEN END TAG OUTSIDE LET *)
        in
          (G, S)
        end

    (* abstractCtxs [G1,...,Gn] = G0, [G1',...,Gn']
       Invariants:
       If . |- G1,...,Gn ctx
          K ||- G1,...,Gn for some K
       then G0 |- G1',...,Gn' ctx for G0 = {{K}}
       and G1',...,Gn' nf
       and . ||- G1',...,Gn' ctx
    *)
    fun abstractCtxs (Gs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val K = collectCtxs (I.Null, Gs, I.Null) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkConstraints K (* GEN END TAG OUTSIDE LET *)
        in
          (abstractKCtx (K), abstractCtxlist (K, 0, Gs))
        end

    (* closedDec (G, D) = true iff D contains no EVar or FVar *)
    fun closedDec (G, (I.Dec (_, V), s)) =
      case collectExp (G, (V, s), I.Null)
        of I.Null => true
         | _ => false

    fun (* GEN BEGIN FUN FIRST *) closedSub (G, I.Shift _) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) closedSub (G, I.Dot (I.Idx _, s)) = closedSub (G, s) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) closedSub (G, I.Dot (I.Exp U, s)) =
        (case collectExp (G, (U, I.id), I.Null)
           of I.Null => closedSub (G, s)
            | _ => false) (* GEN END FUN BRANCH *)

    fun closedExp (G, (U, s)) =
      case collectExp (G, (U, I.id), I.Null)
        of I.Null => true
         | _ => false

    fun (* GEN BEGIN FUN FIRST *) closedCtx I.Null = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) closedCtx (I.Decl (G, D)) =
          closedCtx G andalso closedDec (G, (D, I.id)) (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) closedFor (Psi, T.True) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) closedFor (Psi, T.All ((D, _), F)) =
          closedDEC (Psi, D) andalso closedFor (I.Decl (Psi, D), F) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) closedFor (Psi, T.Ex ((D, _), F)) =
          closedDec (T.coerceCtx Psi, (D, I.id)) andalso closedFor (I.Decl (Psi, T.UDec D), F) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) closedDEC (Psi, T.UDec D) = closedDec (T.coerceCtx Psi, (D, I.id)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) closedDEC (Psi, T.PDec (_, F, _, _)) =  closedFor (Psi, F) (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) closedCTX I.Null = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) closedCTX (I.Decl (Psi,  D)) =
          closedCTX Psi andalso closedDEC (Psi, D) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) evarsToK (nil) = I.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) evarsToK (X::Xs) = I.Decl (evarsToK (Xs), EV(X)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) KToEVars (I.Null) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) KToEVars (I.Decl (K, EV(X))) = X::KToEVars (K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) KToEVars (I.Decl (K, _)) = KToEVars (K) (* GEN END FUN BRANCH *)

    (* collectEVars (G, U[s], Xs) = Xs'
       Invariants:
         G |- U[s] : V
         Xs' extends Xs by new EVars in U[s]
    *)
    fun collectEVars (G, Us, Xs) =
          KToEVars (collectExp (G, Us, evarsToK (Xs)))

    fun collectEVarsSpine (G, (S, s), Xs) =
          KToEVars (collectSpine (G, (S, s), evarsToK (Xs)))


    (* for the theorem prover:
       collect and abstract in subsitutions  including residual lemmas
       pending approval of Frank.
    *)
    fun (* GEN BEGIN FUN FIRST *) collectPrg (_, P as T.EVar (Psi, r, F, _, _, _), K) =
          I.Decl (K, PV P) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectPrg (Psi, T.Unit, K) = K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectPrg (Psi, T.PairExp (U, P), K) =
          collectPrg (Psi, P, collectExp (T.coerceCtx Psi, (U, I.id), K)) (* GEN END FUN BRANCH *)


    (* abstractPVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun (* GEN BEGIN FUN FIRST *) abstractPVar (I.Decl(K', PV (T.EVar (_, r', _, _, _, _))), depth, P as T.EVar (_, r, _, _, _, _)) =
          if r = r' then T.Var (depth+1)
          else abstractPVar (K', depth+1, P) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractPVar (I.Decl(K', _), depth, P) =
          abstractPVar (K', depth+1, P) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) abstractPrg (K, depth, X as T.EVar _) =
          abstractPVar (K, depth, X) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractPrg (K, depth, T.Unit) = T.Unit (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractPrg (K, depth, T.PairExp (U, P)) =
           T.PairExp (abstractExp (K, depth, (U, I.id)), abstractPrg (K, depth, P)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) collectTomegaSub (T.Shift 0) = I.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) collectTomegaSub (T.Dot (T.Exp U, t)) =
          collectExp (I.Null, (U, I.id), collectTomegaSub t) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectTomegaSub (T.Dot (T.Block B, t)) =
          collectBlock (I.Null, B, collectTomegaSub t) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) collectTomegaSub (T.Dot (T.Prg P, t)) =
          collectPrg (I.Null, P, collectTomegaSub t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) abstractOrder (K, depth, O.Arg (Us1, Us2)) =
          O.Arg ((abstractExp (K, depth, Us1), I.id),
                 (abstractExp (K, depth, Us2), I.id)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractOrder (K, depth, O.Simul (Os)) =
          O.Simul (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => abstractOrder (K, depth, O) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractOrder (K, depth, O.Lex (Os)) =
          O.Lex (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => abstractOrder (K, depth, O) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) abstractTC (K, depth, T.Abs (D, TC)) =
          T.Abs (abstractDec (K, depth, (D, I.id)),
                 abstractTC (K, depth, TC)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractTC (K, depth, T.Conj (TC1, TC2)) =
          T.Conj (abstractTC (K, depth, TC1),
                  abstractTC (K, depth, TC2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractTC (K, depth, T.Base (O)) =
          T.Base (abstractOrder (K, depth, O)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) abstractTCOpt (K, depth, NONE) = NONE (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractTCOpt (K, depth, SOME TC) =
          SOME (abstractTC (K, depth, TC)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) abstractMetaDec (K, depth, T.UDec D) = T.UDec (abstractDec (K, depth, (D, I.id))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractMetaDec (K, depth, T.PDec (xx, F, TC1, TC2)) = T.PDec (xx, abstractFor (K, depth, F), TC1, TC2) (* GEN END FUN BRANCH *)
         (* TC cannot contain free FVAR's or EVars'
            --cs  Fri Apr 30 13:45:50 2004 *)

    (* Argument must be in normal form *)
    and (* GEN BEGIN FUN FIRST *) abstractFor (K, depth, T.True) = T.True (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractFor (K, depth, T.All ((MD, Q), F)) =
          T.All ((abstractMetaDec (K, depth, MD), Q), abstractFor (K, depth, F)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractFor (K, depth, T.Ex ((D, Q), F)) =
          T.Ex ((abstractDec (K, depth, (D, I.id)), Q), abstractFor (K, depth, F)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractFor (K, depth, T.And (F1, F2)) =
          T.And (abstractFor (K, depth, F1), abstractFor (K, depth, F2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractFor (K, depth, T.World (W, F)) =
          T.World (W, abstractFor (K, depth, F)) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) abstractPsi (I.Null) = I.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractPsi (I.Decl (K', EV (I.EVar (_, GX, VX, _)))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = raiseType (GX, VX) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V'' = abstractExp (K', 0, (V', I.id)) (* GEN END TAG OUTSIDE LET *)
          (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        in
          I.Decl (abstractPsi K', T.UDec (I.Dec (NONE, V'')))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractPsi (I.Decl (K', FV (name, V'))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V'' = abstractExp (K', 0, (V', I.id)) (* GEN END TAG OUTSIDE LET *)
          (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        in
          I.Decl (abstractPsi K', T.UDec (I.Dec (SOME(name), V'')))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractPsi (I.Decl (K', LV (I.LVar (r, _, (l, t))))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = abstractSOME (K', t) (* GEN END TAG OUTSIDE LET *)
        in
          I.Decl (abstractPsi K', T.UDec (I.BDec (NONE, (l, t'))))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractPsi (I.Decl (K', PV (T.EVar (GX, _, FX, TC1, TC2, _)))) =
        (* What's happening with GX? *)
        (* What's happening with TCs? *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val F' = abstractFor (K', 0, T.forSub (FX, T.id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val TC1' = abstractTCOpt (K', 0, TC1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val TC2' = abstractTCOpt (K', 0, TC2) (* GEN END TAG OUTSIDE LET *)
        in
          I.Decl (abstractPsi K', T.PDec (NONE, F', TC1, TC2))
        end (* GEN END FUN BRANCH *)

    fun abstractTomegaSub t =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val K = collectTomegaSub t (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val t' = abstractTomegaSub' (K, 0, t) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Psi = abstractPsi K (* GEN END TAG OUTSIDE LET *)
      in
        (Psi, t')
      end

    and (* GEN BEGIN FUN FIRST *) abstractTomegaSub' (K, depth, T.Shift 0) = T.Shift depth (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) abstractTomegaSub' (K, depth, T.Dot (T.Exp U, t)) =
          (T.Dot (T.Exp (abstractExp (K, depth, (U, I.id))),
                  abstractTomegaSub' (K, depth, t))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractTomegaSub' (K, depth, T.Dot (T.Block B, t)) =
          (T.Dot (T.Block (abstractLVar (K, depth, B)),
                  abstractTomegaSub' (K, depth, t))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) abstractTomegaSub' (K, depth, T.Dot (T.Prg P, t)) =
          (T.Dot (T.Prg (abstractPrg (K, depth, P)),
                  abstractTomegaSub' (K, depth, t))) (* GEN END FUN BRANCH *)

    fun abstractTomegaPrg P =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val K = collectPrg (I.Null, P, I.Null) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val P' = abstractPrg (K, 0, P) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Psi = abstractPsi K (* GEN END TAG OUTSIDE LET *)
      in
        (Psi, P')
      end


    (* just added to abstract over residual lemmas  -cs *)
    (* Tomorrow: Make collection in program values a priority *)
    (* Then just traverse the Tomega by abstraction to get to the types of those
       variables. *)


  in
    (* GEN BEGIN TAG OUTSIDE LET *) val raiseType = raiseType (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val raiseTerm = raiseTerm (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val piDepend = piDepend (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val closedDec = closedDec (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val closedSub = closedSub (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val closedExp = closedExp (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val abstractDecImp = abstractDecImp (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val abstractDef = abstractDef (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val abstractCtxs = abstractCtxs (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val abstractTomegaSub = abstractTomegaSub (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val abstractTomegaPrg = abstractTomegaPrg (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val abstractSpine = abstractSpineExt (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val collectEVars = collectEVars (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val collectEVarsSpine = collectEVarsSpine (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val closedCtx = closedCtx (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val closedCTX = closedCTX (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *);  (* functor Abstract *)
