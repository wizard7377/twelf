(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

module Abstract ((*! module IntSyn' : INTSYN !*)
                  module Whnf    : WHNF
                  (*! sharing Whnf.IntSyn = IntSyn' !*)
                  module Unify   : UNIFY
                  (*! sharing Unify.IntSyn = IntSyn' !*)
                  (Constraints : CONSTRAINTS): ABSTRACT =
struct

  exception Error of string

  local

    module I = IntSyn
    module T = Tomega
    module C = Constraints
    module O = Order

    (* Intermediate Data Structure *)

    type eFLVar =
      EV of I.Exp                       (* Y ::= X         for  GX |- X : VX *)
    | FV of string * I.Exp              (*     | (F, V)        if . |- F : V *)
    | LV of I.Block                     (*     | L             if . |- L in W *)
    | PV of T.Prg                       (*     | P                            *)

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
    let rec collectConstraints = function (I.Null) -> nil
      | (I.Decl (G, FV _)) -> collectConstraints G
      | (I.Decl (G, EV (I.EVar (_, _, _, ref nil)))) -> collectConstraints G
      | (I.Decl (G, EV (I.EVar (_, _, _, ref cnstrL)))) -> 
        (C.simplify cnstrL) @ collectConstraints G
      | (I.Decl (G, LV _)) -> collectConstraints G

    (* checkConstraints (K) = ()
       Effect: raises Constraints.Error(C) if K contains unresolved constraints
    *)
    let rec checkConstraints (K) =
        let
          let constraints = collectConstraints K
          let _ = case constraints
                    of nil => ()
                     | _ => raise C.Error (constraints)
        in
          ()
        end

    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    (*
    let rec checkEmpty = function (nil) -> ()
      | (Cnstr) -> 
        (case C.simplify Cnstr
           of nil => ()
            | _ => raise Error "Typing ambiguous -- unresolved constraints")
    *)
    (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
    let rec eqEVar = function (I.EVar (r1, _, _, _)) (EV (I.EVar (r2, _, _, _))) -> (r1 = r2)
      | _ _ -> false

    (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
    let rec eqFVar = function (I.FVar (n1, _, _)) (FV (n2,  _)) -> (n1 = n2)
      | _ _ -> false

    (* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)
    let rec eqLVar = function (I.LVar ((r1, _, _))) (LV (I.LVar ((r2, _, _)))) -> (r1 = r2)
      | _ _ -> false


    (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
    let rec exists P K =
        let fun exists' (I.Null) = false
              | exists' (I.Decl(K',Y)) = P(Y) orelse exists' (K')
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
    let rec or = function (I.Maybe, _) -> I.Maybe
      | (_, I.Maybe) -> I.Maybe
      | (I.Meta, _) -> I.Meta
      | (_, I.Meta) -> I.Meta
      | (I.No, I.No) -> I.No

    (* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
    let rec occursInExp = function (k, I.Uni _) -> I.No
      | (k, I.Pi (DP, V)) -> or (occursInDecP (k, DP), occursInExp (k+1, V))
      | (k, I.Root (H, S)) -> occursInHead (k, H, occursInSpine (k, S))
      | (k, I.Lam (D, V)) -> or (occursInDec (k, D), occursInExp (k+1, V))
      | (k, I.FgnExp csfe) -> 
        I.FgnExpStd.fold csfe (fn (U, DP) => or (DP, (occursInExp (k, Whnf.normalize (U, I.id))))) I.No

      (* no case for Redex, EVar, EClo *)

    and occursInHead (k, I.BVar (k'), DP) =
        if (k = k') then I.Maybe
        else DP
      | occursInHead (k, I.Const _, DP) = DP
      | occursInHead (k, I.Def _, DP) = DP
      | occursInHead (k, I.Proj _, DP) = DP
      | occursInHead (k, I.FgnConst _, DP) = DP
      | occursInHead (k, I.Skonst _, I.No) = I.No
      | occursInHead (k, I.Skonst _, I.Meta) = I.Meta
      | occursInHead (k, I.Skonst _, I.Maybe) = I.Meta
      (* no case for FVar *)

    and occursInSpine (_, I.Nil) = I.No
      | occursInSpine (k, I.App (U, S)) = or (occursInExp (k, U), occursInSpine (k, S))
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    let rec piDepend = function (DPV as ((D, I.No), V)) -> I.Pi DPV
      | (DPV as ((D, I.Meta), V)) -> I.Pi DPV
      | ((D, I.Maybe), V) -> 
          I.Pi ((D, occursInExp (1, V)), V)

    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    let rec raiseType = function (I.Null, V) -> V
      | (I.Decl (G, D), V) -> raiseType (G, I.Pi ((D, I.Maybe), V))

    (* raiseTerm (G, U) = [[G]] U

       Invariant:
       If G |- U : V
       then  . |- [[G]] U : {{G}} V

       All abstractions are potentially dependent.
    *)
    let rec raiseTerm = function (I.Null, U) -> U
      | (I.Decl (G, D), U) -> raiseTerm (G, I.Lam (D, U))

    (* collectExpW (G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and FVars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    let rec collectExpW = function (G, (I.Uni L, s), K) -> K
      | (G, (I.Pi ((D, _), V), s), K) -> 
          collectExp (I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), collectDec (G, (D, s), K))
      | (G, (I.Root (F as I.FVar (name, V, s'), S), s), K) -> 
        if exists (eqFVar F) K
          then collectSpine (G, (S, s), K)
        else (* s' = ^|G| *)
          collectSpine (G, (S, s), I.Decl (collectExp (I.Null, (V, I.id), K), FV (name, V)))
      | (G, (I.Root (I.Proj (L as I.LVar (ref NONE, sk, (l, t)), i), S), s), K) -> 
          collectSpine (G, (S, s), collectBlock (G, I.blockSub (L, s), K))
          (* BUG : We forget to deref L.  use collectBlock instead
             FPCHECK
             -cs Sat Jul 24 18:48:59 2010
            was:
      | (G, (I.Root (I.Proj (L as I.LVar (r, sk, (l, t)), i), S), s), K) -> 
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
*)      | collectExpW (G, (I.Root (_ , S), s), K) =
          collectSpine (G, (S, s), K)
      | collectExpW (G, (I.Lam (D, U), s), K) =
          collectExp (I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), collectDec (G, (D, s), K))
      | collectExpW (G, (X as I.EVar (r, GX, V, cnstrs), s), K) =
        if exists (eqEVar X) K
          then collectSub(G, s, K)
        else let
               (* let _ = checkEmpty !cnstrs *)
               let V' = raiseType (GX, V) (* inefficient *)
               let K' = collectExp (I.Null, (V', I.id), K)
             in
               collectSub(G, s, I.Decl (K', EV (X)))
             end
      | collectExpW (G, (I.FgnExp csfe, s), K) =
          I.FgnExpStd.fold csfe (fn (U, K) => collectExp (G, (U, s), K)) K
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
    and collectSpine (G, (I.Nil, _), K) = K
      | collectSpine (G, (I.SClo(S, s'), s), K) =
          collectSpine (G, (S, I.comp (s', s)), K)
      | collectSpine (G, (I.App (U, S), s), K) =
          collectSpine (G, (S, s), collectExp (G, (U, s), K))

    (* collectDec (G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
    and collectDec (G, (I.Dec (_, V), s), K) =
          collectExp (G, (V, s), K)
      | collectDec (G, (I.BDec (_, (_, t)), s), K) =
          (* . |- t : Gsome, so do not compose with s *)
          (* Sat Dec  8 13:28:15 2001 -fp *)
          (* was: collectSub (I.Null, t, K) *)
          collectSub (G, I.comp(t,s), K)
      | collectDec (G, (I.NDec _, s), K) = K

    (* collectSub (G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
    and collectSub (G, I.Shift _, K) = K
      | collectSub (G, I.Dot (I.Idx _, s), K) = collectSub (G, s, K)
      | collectSub (G, I.Dot (I.Exp (U), s), K) =
          collectSub (G, s, collectExp (G, (U, I.id), K))
      | collectSub (G, I.Dot (I.Block B, s), K) =
          collectSub (G, s, collectBlock (G, B, K))
    (* next case should be impossible *)
    (*
      | collectSub (G, I.Dot (I.Undef, s), K) =
          collectSub (G, s, K)
    *)

    (* collectBlock (G, B, K) where G |- B block *)
    and collectBlock (G, I.LVar (ref (SOME B), sk , _), K) =
          collectBlock (G, I.blockSub (B, sk), K)
          (* collectBlock (B, K) *)
          (* correct?? -fp Sun Dec  1 21:15:33 2002 *)
      | collectBlock (G, L as I.LVar (_, sk, (l, t)), K) =
        if exists (eqLVar L) K
          then collectSub (G, I.comp(t,sk), K)
        else I.Decl (collectSub (G, I.comp(t,sk), K), LV L)
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
    let rec collectCtx = function (G0, I.Null, K) -> (G0, K)
      | (G0, I.Decl (G, D), K) -> 
        let
          let (G0', K') = collectCtx (G0, G, K)
          let K'' = collectDec (G0', (D, I.id), K')
        in
          (I.Decl (G0, D), K'')
        end

    (* collectCtxs (G0, Gs, K) = K'
       Invariant: G0 |- G1,...,Gn ctx where Gs = [G1,...,Gn]
       and K' = K, K'' where K'' contains all EVars and FVars in G1,...,Gn
    *)
    let rec collectCtxs = function (G0, nil, K) -> K
      | (G0, G::Gs, K) -> 
        let
          let (G0', K') = collectCtx (G0, G, K)
        in
          collectCtxs (G0', Gs, K')
        end

    (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    let rec abstractEVar (I.Decl (K', EV (I.EVar(r',_,_,_))), depth, X as I.EVar (r, _, _, _)) =
        if r = r' then I.BVar (depth+1)
        else abstractEVar (K', depth+1, X)
(*      | abstractEVar (I.Decl (K', FV (n', _)), depth, X) =
          abstractEVar (K', depth+1, X) remove later --cs*)
      | abstractEVar (I.Decl (K', _), depth, X) =
          abstractEVar (K', depth+1, X)

    (* abstractFVar (K, depth, F) = C'

       Invariant:
       If   G |- F : V
       and  |G| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    let rec abstractFVar (I.Decl(K', FV (n', _)), depth, F as I.FVar (n, _, _)) =
          if n = n' then I.BVar (depth+1)
          else abstractFVar (K', depth+1, F)
(*      | abstractFVar (I.Decl(K', EV _), depth, F) =
          abstractFVar (K', depth+1, F) remove later --cs *)
      | abstractFVar (I.Decl(K', _), depth, F) =
          abstractFVar (K', depth+1, F)

    (* abstractLVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
    let rec abstractLVar = function (I.Decl(K', LV (I.LVar (r', _, _))), depth, L as I.LVar (r, _, _)) -> 
          if r = r' then I.Bidx (depth+1)
          else abstractLVar (K', depth+1, L)
      | (I.Decl(K', _), depth, L) -> 
          abstractLVar (K', depth+1, L)

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
    let rec abstractExpW = function (K, depth, (U as I.Uni (L), s)) -> U
      | (K, depth, (I.Pi ((D, P), V), s)) -> 
          piDepend ((abstractDec (K, depth, (D, s)), P),
                    abstractExp (K, depth + 1, (V, I.dot1 s)))
      | (K, depth, (I.Root (F as I.FVar _, S), s)) -> 
          I.Root (abstractFVar (K, depth, F),
                  abstractSpine (K, depth, (S, s)))
      | (K, depth, (I.Root (I.Proj (L as I.LVar _, i), S), s)) -> 
          I.Root (I.Proj (abstractLVar (K, depth, L), i),
                  abstractSpine (K, depth, (S, s)))
      | (K, depth, (I.Root (H, S) ,s)) -> 
          I.Root (H, abstractSpine (K, depth, (S, s)))
      | (K, depth, (I.Lam (D, U), s)) -> 
          I.Lam (abstractDec (K, depth, (D, s)),
                 abstractExp (K, depth + 1, (U, I.dot1 s)))
      | (K, depth, (X as I.EVar _, s)) -> 
          I.Root (abstractEVar (K, depth, X),
                  abstractSub (K, depth, s, I.Nil))
      | (K, depth, (I.FgnExp csfe, s)) -> 
          I.FgnExpStd.Map.apply csfe (fun U -> abstractExp (K, depth, (U, s)))

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
    and abstractSub (K, depth, I.Shift (k), S) =
        if k < depth
          then abstractSub (K, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), S)
        else (* k = depth *) S
      | abstractSub (K, depth, I.Dot (I.Idx (k), s), S) =
          abstractSub (K, depth, s, I.App (I.Root (I.BVar (k), I.Nil), S))
      | abstractSub (K, depth, I.Dot (I.Exp (U), s), S) =
          abstractSub (K, depth, s, I.App (abstractExp (K, depth, (U, I.id)), S))

    (* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- S : V > P
       and  K ||- S
       and  |G| = depth

       then {{K}}, G |- S' : V' > P'
       and  . ||- S'
    *)
    and abstractSpine (K, depth, (I.Nil, _))  = I.Nil
      | abstractSpine (K, depth, (I.SClo (S, s'), s)) =
          abstractSpine (K, depth, (S, I.comp (s', s)))
      | abstractSpine (K, depth, (I.App (U, S), s)) =
          I.App (abstractExp (K, depth, (U ,s)),
                 abstractSpine (K, depth, (S, s)))

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
    let rec abstractSOME = function (K, I.Shift 0) -> (* n = 0 by invariant, check for now *)
          I.Shift (I.ctxLength(K))
      | (K, I.Shift (n)) -> (* n > 0 *)
          I.Shift (I.ctxLength(K))
      | (K, I.Dot (I.Idx k, s)) -> 
          I.Dot (I.Idx k, abstractSOME (K, s))
      | (K, I.Dot (I.Exp U, s)) -> 
          I.Dot (I.Exp (abstractExp (K, 0, (U, I.id))), abstractSOME (K, s))
      | (K, I.Dot (I.Block (L as I.LVar _), s)) -> 
          I.Dot (I.Block (abstractLVar (K, 0, L)), abstractSOME (K, s))
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
    let rec abstractCtx = function (K, depth, I.Null) -> (I.Null, depth)
      | (K, depth, I.Decl (G, D)) -> 
        let
          let (G', depth') = abstractCtx (K, depth, G)
          let D' = abstractDec (K, depth', (D, I.id))
        in
          (I.Decl (G', D'), depth'+1)
        end

    (* abstractCtxlist (K, depth, [G1,...,Gn]) = [G1',...,Gn']
       where Gi' = {{Gi}}_K

       Invariants:
       if G0 |- G1,...,Gn ctx
       and K ||- G1,...,Gn
       and |G0| = depth
       then {{K}}, G0 |- G1',...,Gn' ctx
       and . ||- G1',...,Gn'
    *)
    let rec abstractCtxlist = function (K, depth, nil) -> nil
      | (K, depth, G::Gs) -> 
        let
          let (G', depth') = abstractCtx (K, depth, G)
          let Gs' = abstractCtxlist (K, depth', Gs)
        in
          G'::Gs'
        end

    (* dead code under new reconstruction -kw
    (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    *)
    let rec getLevel = function (I.Uni _) -> I.Kind
      | (I.Pi (_, U)) -> getLevel U
      | (I.Root _) -> I.Type
      | (I.Redex (U, _)) -> getLevel U
      | (I.Lam (_, U)) -> getLevel U
      | (I.EClo (U,_)) -> getLevel U

    (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    *)
    let rec checkType V =
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
    let rec abstractKPi = function (I.Null, V) -> V
      | (I.Decl (K', EV (I.EVar (_, GX, VX, _))), V) -> 
        let
          let V' = raiseType (GX, VX)
          let V'' = abstractExp (K', 0, (V', I.id))
          (* enforced by reconstruction -kw
          let _ = checkType V'' *)
        in
          abstractKPi (K', I.Pi ((I.Dec(NONE, V''), I.Maybe), V))
        end
      | (I.Decl (K', FV (name,V')), V) -> 
        let
          let V'' = abstractExp (K', 0, (V', I.id))
          (* enforced by reconstruction -kw
          let _ = checkType V'' *)
        in
          abstractKPi (K', I.Pi ((I.Dec(SOME(name), V''), I.Maybe), V))
        end
      | (I.Decl (K', LV (I.LVar (r, _, (l, t)))), V) -> 
        let
          let t' = abstractSOME (K', t)
        in
          abstractKPi (K', I.Pi ((I.BDec (NONE, (l, t')), I.Maybe), V))
        end

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
    let rec abstractKLam = function (I.Null, U) -> U
      | (I.Decl (K', EV (I.EVar (_, GX, VX, _))), U) -> 
        let
          let V' = raiseType (GX, VX)
        in
          abstractKLam (K', I.Lam (I.Dec(NONE, abstractExp (K', 0, (V', I.id))), U))
        end
      | (I.Decl (K', FV (name,V')), U) -> 
          abstractKLam (K', I.Lam (I.Dec(SOME(name), abstractExp (K', 0, (V', I.id))), U))


    let rec abstractKCtx = function (I.Null) -> I.Null
      | (I.Decl (K', EV (I.EVar (_, GX, VX, _)))) -> 
        let
          let V' = raiseType (GX, VX)
          let V'' = abstractExp (K', 0, (V', I.id))
          (* enforced by reconstruction -kw
          let _ = checkType V'' *)
        in
          I.Decl (abstractKCtx K', I.Dec (NONE, V''))
        end
      | (I.Decl (K', FV (name, V'))) -> 
        let
          let V'' = abstractExp (K', 0, (V', I.id))
          (* enforced by reconstruction -kw
          let _ = checkType V'' *)
        in
          I.Decl (abstractKCtx K', I.Dec (SOME(name), V''))
        end
      | (I.Decl (K', LV (I.LVar (r, _, (l, t))))) -> 
        let
          let t' = abstractSOME (K', t)
        in
          I.Decl (abstractKCtx K', I.BDec (NONE, (l, t')))
        end


    (* abstractDecImp V = (k', V')   (* rename --cs  (see above) *)

       Invariant:
       If    . |- V : L
       and   K ||- V

       then  . |- V' : L
       and   V' = {{K}} V
       and   . ||- V'
       and   k' = |K|
    *)
    let rec abstractDecImp V =
        let
          let K = collectExp (I.Null, (V, I.id), I.Null)
          let _ = checkConstraints (K)
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
    let rec abstractDef (U, V) =
        let
          let K = collectExp (I.Null, (U, I.id), collectExp (I.Null, (V, I.id), I.Null))
          let _ = checkConstraints K
        in
          (I.ctxLength K, (abstractKLam (K, abstractExp (K, 0, (U, I.id))),
                           abstractKPi  (K, abstractExp (K, 0, (V, I.id)))))
        end


    let rec abstractSpineExt (S, s) =
        let
          let K = collectSpine (I.Null, (S, s), I.Null)
          let _ = checkConstraints (K)
          let G = abstractKCtx (K)
          let S = abstractSpine (K, 0, (S, s))
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
    let rec abstractCtxs (Gs) =
        let
          let K = collectCtxs (I.Null, Gs, I.Null)
          let _ = checkConstraints K
        in
          (abstractKCtx (K), abstractCtxlist (K, 0, Gs))
        end

    (* closedDec (G, D) = true iff D contains no EVar or FVar *)
    let rec closedDec (G, (I.Dec (_, V), s)) =
      case collectExp (G, (V, s), I.Null)
        of I.Null => true
         | _ => false

    let rec closedSub = function (G, I.Shift _) -> true
      | (G, I.Dot (I.Idx _, s)) -> closedSub (G, s)
      | (G, I.Dot (I.Exp U, s)) -> 
        (case collectExp (G, (U, I.id), I.Null)
           of I.Null => closedSub (G, s)
            | _ => false)

    let rec closedExp (G, (U, s)) =
      case collectExp (G, (U, I.id), I.Null)
        of I.Null => true
         | _ => false

    let rec closedCtx = function I.Null -> true
      | (I.Decl (G, D)) -> 
          closedCtx G andalso closedDec (G, (D, I.id))


    let rec closedFor = function (Psi, T.True) -> true
      | (Psi, T.All ((D, _), F)) -> 
          closedDEC (Psi, D) andalso closedFor (I.Decl (Psi, D), F)
      | (Psi, T.Ex ((D, _), F)) -> 
          closedDec (T.coerceCtx Psi, (D, I.id)) andalso closedFor (I.Decl (Psi, T.UDec D), F)

    and closedDEC (Psi, T.UDec D) = closedDec (T.coerceCtx Psi, (D, I.id))
      | closedDEC (Psi, T.PDec (_, F, _, _)) =  closedFor (Psi, F)


    let rec closedCTX = function I.Null -> true
      | (I.Decl (Psi,  D)) -> 
          closedCTX Psi andalso closedDEC (Psi, D)

    let rec evarsToK = function (nil) -> I.Null
      | (X::Xs) -> I.Decl (evarsToK (Xs), EV(X))

    let rec KToEVars = function (I.Null) -> nil
      | (I.Decl (K, EV(X))) -> X::KToEVars (K)
      | (I.Decl (K, _)) -> KToEVars (K)

    (* collectEVars (G, U[s], Xs) = Xs'
       Invariants:
         G |- U[s] : V
         Xs' extends Xs by new EVars in U[s]
    *)
    let rec collectEVars (G, Us, Xs) =
          KToEVars (collectExp (G, Us, evarsToK (Xs)))

    let rec collectEVarsSpine (G, (S, s), Xs) =
          KToEVars (collectSpine (G, (S, s), evarsToK (Xs)))


    (* for the theorem prover:
       collect and abstract in subsitutions  including residual lemmas
       pending approval of Frank.
    *)
    let rec collectPrg = function (_, P as T.EVar (Psi, r, F, _, _, _), K) -> 
          I.Decl (K, PV P)
      | (Psi, T.Unit, K) -> K
      | (Psi, T.PairExp (U, P), K) -> 
          collectPrg (Psi, P, collectExp (T.coerceCtx Psi, (U, I.id), K))


    (* abstractPVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
    let rec abstractPVar = function (I.Decl(K', PV (T.EVar (_, r', _, _, _, _))), depth, P as T.EVar (_, r, _, _, _, _)) -> 
          if r = r' then T.Var (depth+1)
          else abstractPVar (K', depth+1, P)
      | (I.Decl(K', _), depth, P) -> 
          abstractPVar (K', depth+1, P)

    let rec abstractPrg = function (K, depth, X as T.EVar _) -> 
          abstractPVar (K, depth, X)
      | (K, depth, T.Unit) -> T.Unit
      | (K, depth, T.PairExp (U, P)) -> 
           T.PairExp (abstractExp (K, depth, (U, I.id)), abstractPrg (K, depth, P))

    let rec collectTomegaSub = function (T.Shift 0) -> I.Null
      | (T.Dot (T.Exp U, t)) -> 
          collectExp (I.Null, (U, I.id), collectTomegaSub t)
      | (T.Dot (T.Block B, t)) -> 
          collectBlock (I.Null, B, collectTomegaSub t)
      | (T.Dot (T.Prg P, t)) -> 
          collectPrg (I.Null, P, collectTomegaSub t)

    let rec abstractOrder = function (K, depth, O.Arg (Us1, Us2)) -> 
          O.Arg ((abstractExp (K, depth, Us1), I.id),
                 (abstractExp (K, depth, Us2), I.id))
      | (K, depth, O.Simul (Os)) -> 
          O.Simul (map (fun O -> abstractOrder (K, depth, O)) Os)
      | (K, depth, O.Lex (Os)) -> 
          O.Lex (map (fun O -> abstractOrder (K, depth, O)) Os)

    let rec abstractTC = function (K, depth, T.Abs (D, TC)) -> 
          T.Abs (abstractDec (K, depth, (D, I.id)),
                 abstractTC (K, depth, TC))
      | (K, depth, T.Conj (TC1, TC2)) -> 
          T.Conj (abstractTC (K, depth, TC1),
                  abstractTC (K, depth, TC2))
      | (K, depth, T.Base (O)) -> 
          T.Base (abstractOrder (K, depth, O))

    let rec abstractTCOpt = function (K, depth, NONE) -> NONE
      | (K, depth, SOME TC) -> 
          SOME (abstractTC (K, depth, TC))

    let rec abstractMetaDec = function (K, depth, T.UDec D) -> T.UDec (abstractDec (K, depth, (D, I.id)))
      | (K, depth, T.PDec (xx, F, TC1, TC2)) -> T.PDec (xx, abstractFor (K, depth, F), TC1, TC2)
         (* TC cannot contain free FVAR's or EVars'
            --cs  Fri Apr 30 13:45:50 2004 *)

    (* Argument must be in normal form *)
    and abstractFor (K, depth, T.True) = T.True
      | abstractFor (K, depth, T.All ((MD, Q), F)) =
          T.All ((abstractMetaDec (K, depth, MD), Q), abstractFor (K, depth, F))
      | abstractFor (K, depth, T.Ex ((D, Q), F)) =
          T.Ex ((abstractDec (K, depth, (D, I.id)), Q), abstractFor (K, depth, F))
      | abstractFor (K, depth, T.And (F1, F2)) =
          T.And (abstractFor (K, depth, F1), abstractFor (K, depth, F2))
      | abstractFor (K, depth, T.World (W, F)) =
          T.World (W, abstractFor (K, depth, F))

    let rec abstractPsi = function (I.Null) -> I.Null
      | (I.Decl (K', EV (I.EVar (_, GX, VX, _)))) -> 
        let
          let V' = raiseType (GX, VX)
          let V'' = abstractExp (K', 0, (V', I.id))
          (* enforced by reconstruction -kw
          let _ = checkType V'' *)
        in
          I.Decl (abstractPsi K', T.UDec (I.Dec (NONE, V'')))
        end
      | (I.Decl (K', FV (name, V'))) -> 
        let
          let V'' = abstractExp (K', 0, (V', I.id))
          (* enforced by reconstruction -kw
          let _ = checkType V'' *)
        in
          I.Decl (abstractPsi K', T.UDec (I.Dec (SOME(name), V'')))
        end
      | (I.Decl (K', LV (I.LVar (r, _, (l, t))))) -> 
        let
          let t' = abstractSOME (K', t)
        in
          I.Decl (abstractPsi K', T.UDec (I.BDec (NONE, (l, t'))))
        end
      | (I.Decl (K', PV (T.EVar (GX, _, FX, TC1, TC2, _)))) -> 
        (* What's happening with GX? *)
        (* What's happening with TCs? *)
        let
          let F' = abstractFor (K', 0, T.forSub (FX, T.id))
          let TC1' = abstractTCOpt (K', 0, TC1)
          let TC2' = abstractTCOpt (K', 0, TC2)
        in
          I.Decl (abstractPsi K', T.PDec (NONE, F', TC1, TC2))
        end

    let rec abstractTomegaSub t =
      let
        let K = collectTomegaSub t
        let t' = abstractTomegaSub' (K, 0, t)
        let Psi = abstractPsi K
      in
        (Psi, t')
      end

    and abstractTomegaSub' (K, depth, T.Shift 0) = T.Shift depth
      | abstractTomegaSub' (K, depth, T.Dot (T.Exp U, t)) =
          (T.Dot (T.Exp (abstractExp (K, depth, (U, I.id))),
                  abstractTomegaSub' (K, depth, t)))
      | abstractTomegaSub' (K, depth, T.Dot (T.Block B, t)) =
          (T.Dot (T.Block (abstractLVar (K, depth, B)),
                  abstractTomegaSub' (K, depth, t)))
      | abstractTomegaSub' (K, depth, T.Dot (T.Prg P, t)) =
          (T.Dot (T.Prg (abstractPrg (K, depth, P)),
                  abstractTomegaSub' (K, depth, t)))

    let rec abstractTomegaPrg P =
      let
        let K = collectPrg (I.Null, P, I.Null)
        let P' = abstractPrg (K, 0, P)
        let Psi = abstractPsi K
      in
        (Psi, P')
      end


    (* just added to abstract over residual lemmas  -cs *)
    (* Tomorrow: Make collection in program values a priority *)
    (* Then just traverse the Tomega by abstraction to get to the types of those
       variables. *)


  in
    let raiseType = raiseType
    let raiseTerm = raiseTerm

    let piDepend = piDepend
    let closedDec = closedDec
    let closedSub = closedSub
    let closedExp = closedExp

    let abstractDecImp = abstractDecImp
    let abstractDef = abstractDef
    let abstractCtxs = abstractCtxs
    let abstractTomegaSub = abstractTomegaSub
    let abstractTomegaPrg = abstractTomegaPrg
    let abstractSpine = abstractSpineExt

    let collectEVars = collectEVars
    let collectEVarsSpine = collectEVarsSpine

    let closedCtx = closedCtx
    let closedCTX = closedCTX
  end
end;; (* functor Abstract *)
