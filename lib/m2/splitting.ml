(* Splitting *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Splitting (structure Global : GLOBAL
                   structure MetaSyn' : METASYN
                   structure MetaAbstract : METAABSTRACT
                   structure MetaPrint : METAPRINT
                   sharing MetaPrint.MetaSyn = MetaSyn'
                   sharing MetaAbstract.MetaSyn = MetaSyn'
                   structure ModeTable : MODETABLE
                   (*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                   structure Index : INDEX
                   (*! sharing Index.IntSyn = MetaSyn'.IntSyn !*)
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                   structure Unify : UNIFY
                   (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
                   (*! structure CSManager : CS_MANAGER !*)
                   (*! sharing CSManager.IntSyn = MetaSyn'.IntSyn !*)
                     )
  : SPLITTING =
struct
  structure MetaSyn = MetaSyn'

  exception Error of string

  (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as "Active", and cases where there were
     leftover constraints after unification as "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases.
  *)
  datatype 'a flag =
    Active of 'a | InActive

  type operator = (MetaSyn.state * int) *
                   MetaSyn.state flag list

  local
    structure M = MetaSyn
    structure I = IntSyn


    (* constCases (G, (V, s), I, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases from I
    *)
    fun (* GEN BEGIN FUN FIRST *) constCases (G, Vs, nil, abstract, ops) = ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) constCases (G, Vs, I.Const c::Sgn, abstract, ops) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (U, Vs') = M.createAtomConst (G, I.Const c) (* GEN END TAG OUTSIDE LET *)
        in
          constCases (G, Vs, Sgn, abstract,
                      CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                                   (if Unify.unifiable (G, Vs, Vs')
                                      then Active (abstract (I.conDecName (I.sgnLookup c) ^ "/", U))
                                           :: ops
                                    else ops)
                                   handle MetaAbstract.Error _ => InActive :: ops (* GEN END FUNCTION EXPRESSION *)))
        end (* GEN END FUN BRANCH *)

    (* paramCases (G, (V, s), k, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases introduced by parameters <= k in G
    *)
    fun (* GEN BEGIN FUN FIRST *) paramCases (G, Vs, 0, abstract, ops) = ops (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) paramCases (G, Vs, k, abstract, ops) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (U, Vs') = M.createAtomBVar (G, k) (* GEN END TAG OUTSIDE LET *)
        in
          paramCases (G, Vs, k-1, abstract,
                      CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                                   (if Unify.unifiable (G, Vs, Vs')
                                      then Active (abstract (Int.toString k ^ "/", U)) :: ops
                                    else ops)
                                   handle MetaAbstract.Error _ => InActive  :: ops (* GEN END FUNCTION EXPRESSION *)))
        end (* GEN END FUN BRANCH *)

    (* lowerSplitDest (G, (V, s'), abstract) = C'

       Invariant:
       If   G0, G |- s' : G1  G1 |- V: type
       and  G is the context of local parameters
       and  abstract abstraction function
       then C' is a list of all cases unifying with V[s']
            (it contains constant and parameter cases)
    *)
    fun (* GEN BEGIN FUN FIRST *) lowerSplitDest (G, (V as I.Root (I.Const c, _), s'), abstract) =
          constCases (G, (V, s'), Index.lookup c, abstract,
                      paramCases (G, (V, s'), I.ctxLength G, abstract, nil)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lowerSplitDest (G, (I.Pi ((D, P), V), s'), abstract) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.decSub (D, s') (* GEN END TAG OUTSIDE LET *)
          in
            lowerSplitDest (I.Decl (G, D'), (V, I.dot1 s'),
                            (* GEN BEGIN FUNCTION EXPRESSION *) fn (name, U) => abstract (name, I.Lam (D', U)) (* GEN END FUNCTION EXPRESSION *))
          end (* GEN END FUN BRANCH *)

    (* split ((G, M), (x:D, s), abstract) = C'

       Invariant :
       If   |- G ctx
       and  G |- M mtx
       and  G |- s : G1   and  G1 |- D : L
       and  abstract abstraction function
       then C' = (C1, ... Cn) are resulting cases from splitting D[s]
    *)
    fun split (M.Prefix (G, M, B), (D as I.Dec (_, V), s), abstract) =
           lowerSplitDest (I.Null, (V, s),
                           (* GEN BEGIN FUNCTION EXPRESSION *) fn (name', U') => abstract (name', M.Prefix (G, M, B),
                                                       I.Dot (I.Exp (U'), s)) (* GEN END FUNCTION EXPRESSION *))

    (* rename to add N prefix? *)
    (* occursIn (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
    fun (* GEN BEGIN FUN FIRST *) occursInExp (k, I.Uni _) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInExp (k, I.Pi (DP, V)) = occursInDecP (k, DP) orelse occursInExp (k+1, V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExp (k, I.Root (C, S)) = occursInCon (k, C) orelse occursInSpine (k, S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExp (k, I.Lam (D,V)) = occursInDec (k, D) orelse occursInExp (k+1, V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExp (k, I.FgnExp csfe) =
        I.FgnExpStd.fold csfe ((* GEN BEGIN FUNCTION EXPRESSION *) fn (U,B) => B orelse occursInExp (k, Whnf.normalize (U, I.id)) (* GEN END FUNCTION EXPRESSION *)) false (* GEN END FUN BRANCH *)
      (* no case for Redex, EVar, EClo *)

    and (* GEN BEGIN FUN FIRST *) occursInCon (k, I.BVar (k')) = (k = k') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInCon (k, I.Const _) = false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInCon (k, I.Def _) = false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInCon (k, I.Skonst _) = false (* GEN END FUN BRANCH *)
      (* no case for FVar *)

    and (* GEN BEGIN FUN FIRST *) occursInSpine (_, I.Nil) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInSpine (k, I.App (U, S)) = occursInExp (k, U) orelse occursInSpine (k, S) (* GEN END FUN BRANCH *)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    fun isIndexInit k = false
    fun isIndexSucc (D, isIndex) k = occursInDec (k, D) orelse isIndex (k+1)
    fun isIndexFail (D, isIndex) k = isIndex (k+1)

    (* checkExp (M, U) = B

       Invariant:
       If   G |- M
       and  G |- U : V
       and  U in nf
       then B holds iff U does not contain any Bot variables
    *)

    fun (* GEN BEGIN FUN FIRST *) checkVar (I.Decl (M, M.Top), 1) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkVar (I.Decl (M, M.Bot), 1) = false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkVar (I.Decl (M, _), k) = checkVar (M, k-1) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) checkExp (M, I.Uni _) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkExp (M, I.Pi ((D, P), V)) =
          checkDec (M, D) andalso checkExp (I.Decl (M, M.Top), V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkExp (M, I.Lam (D, V)) =
          checkDec (M, D) andalso checkExp (I.Decl (M, M.Top), V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkExp (M, I.Root (I.BVar k, S)) =
          checkVar (M, k) andalso checkSpine (M, S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkExp (M, I.Root (_, S)) =
          checkSpine (M, S) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) checkSpine (M, I.Nil) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkSpine (M, I.App (U, S)) =
          checkExp (M, U) andalso checkSpine (M, S) (* GEN END FUN BRANCH *)

    and checkDec (M, I.Dec (_, V)) = checkExp (M, V)


    (* copied from meta-abstract *)
    (* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)
    fun (* GEN BEGIN FUN FIRST *) modeEq (ModeSyn.Marg (ModeSyn.Plus, _), M.Top) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) modeEq (ModeSyn.Marg (ModeSyn.Minus, _), M.Bot) = true (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) modeEq _ = false (* GEN END FUN BRANCH *)

    (*
       The inherit functions below copy the splitting depth attribute
       between successive states, using a simultaneous traversal
       in mode dependency order.

       Invariant:
       (G,M,B) |- V type
       G = G0, G1, G2
       |G2| = k       (length of local context)
       d = |G1, G2|   (last BVar seen)
       let n < |G|
       if   n>d then n is an index of a variable already seen in mdo
       if   n=d then n is an index of a variable now seen for the first
                     time
       if   n<=k then n is a local parameter
       it is impossible for     k < n < d
    *)
    (* invariants on inheritXXX functions? -fp *)
    fun (* GEN BEGIN FUN FIRST *) inheritBelow (b', k', I.Lam (D', U'), Bdd') =
          inheritBelow (b', k'+1, U',
                        inheritBelowDec (b', k', D', Bdd')) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inheritBelow (b', k', I.Pi ((D',_), V'), Bdd') =
          inheritBelow (b', k'+1, V',
                        inheritBelowDec (b', k', D', Bdd')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inheritBelow (b', k', I.Root (I.BVar(n'), S'), (B', d, d')) =
        if n' = k'+d' andalso n' > k' (* necessary for d' = 0 *)
          then inheritBelowSpine (b', k', S', (I.Decl (B', b'), d, d'-1))
        else inheritBelowSpine (b', k', S', (B', d, d')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inheritBelow (b', k', I.Root (C, S'), Bdd') =
          inheritBelowSpine (b', k', S', Bdd') (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) inheritBelowSpine (b', k', I.Nil, Bdd') = Bdd' (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inheritBelowSpine (b', k', I.App (U', S'), Bdd') =
          inheritBelowSpine (b', k', S', inheritBelow (b', k', U', Bdd')) (* GEN END FUN BRANCH *)
    and inheritBelowDec (b', k', I.Dec(x, V'), Bdd') =
          inheritBelow (b', k', V', Bdd')

    (* skip *)
    fun (* GEN BEGIN FUN FIRST *) skip (k, I.Lam (D, U), Bdd') =
          skip (k+1, U, skipDec (k, D, Bdd')) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) skip (k, I.Pi ((D,_), V), Bdd') =
          skip (k+1, V, skipDec (k, D, Bdd')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) skip (k, I.Root (I.BVar(n), S), (B', d, d')) =
        if n = k+d andalso n > k (* necessary for d = 0 *)
          then skipSpine (k, S, (B', d-1, d'))
        else skipSpine (k, S, (B', d, d')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) skip (k, I.Root (C, S), Bdd') =
          skipSpine (k, S, Bdd') (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) skipSpine (k, I.Nil, Bdd') = Bdd' (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) skipSpine (k, I.App (U, S), Bdd') =
          skipSpine (k, S, skip (k, U, Bdd')) (* GEN END FUN BRANCH *)
    and skipDec (k, I.Dec(x, V), Bdd') =
          skip (k, V, Bdd')

    (* Uni impossible *)
    fun (* GEN BEGIN FUN FIRST *) inheritExp (B, k, I.Lam (D, U), k', I.Lam (D', U'), Bdd') =
           inheritExp (B, k+1, U, k'+1, U',
                       inheritDec (B, k, D, k', D', Bdd')) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inheritExp (B, k, I.Pi ((D, _), V), k', I.Pi ((D', _), V'), Bdd') =
           inheritExp (B, k+1, V, k'+1, V',
                       inheritDec (B, k, D, k', D', Bdd')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inheritExp (B, k, V as I.Root (I.BVar (n), S), k', V', (B', d, d')) =
        if n = k+d andalso n > k (* new original variable *)
          then (* inheritBelow (I.ctxLookup (B, n-k) - 1, k', V', (B', d-1, d')) *)
            skipSpine (k, S, inheritNewRoot (B, I.ctxLookup (B, n-k), k, V, k', V', (B', d, d')))
        else if n > k+d (* already seen original variable *)
               (* then (B', d, d') *)
               (* previous line avoids redundancy,
                  but may violate invariant outside pattern fragment *)
               then skipSpine (k, S, inheritBelow (I.ctxLookup (B, n-k)-1, k', V', (B', d, d')))
             else (* must correspond *)
               let
                 (* GEN BEGIN TAG OUTSIDE LET *) val I.Root (C', S') = V' (* GEN END TAG OUTSIDE LET *) (* C' = BVar (n) *)
               in
                 inheritSpine (B, k, S, k', S', (B', d, d'))
               end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) inheritExp (B, k, I.Root (C, S), k', I.Root (C', S'), Bdd') =
          (* C ~ C' *)
          inheritSpine (B, k, S, k', S', Bdd') (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) inheritNewRoot (B, b, k, I.Root (I.BVar (n), S),
                        k', V' as I.Root (I.BVar (n'), S'), (B', d, d')) =
        (* n = k+d *)
        if n' = k'+d' andalso n' > k'
          (* n' also new --- same variable: do not decrease *)
          then inheritBelow (b, k', V', (B', d-1, d'))
        else inheritBelow (b-1, k', V', (B', d-1, d')) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inheritNewRoot (B, b, k, V, k', V', (B', d, d')) =
          (* n' not new --- decrease the splitting depth of all variables in V' *)
          inheritBelow (b-1, k', V', (B', d-1, d')) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) inheritSpine (B, k, I.Nil, k', I.Nil, Bdd') = Bdd' (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inheritSpine (B, k, I.App (U, S), k', I.App (U', S'), Bdd') =
          inheritSpine (B, k, S, k', S', inheritExp (B, k, U, k', U', Bdd')) (* GEN END FUN BRANCH *)

    and inheritDec (B, k, I.Dec(_, V), k', I.Dec(_, V'), Bdd') =
          inheritExp (B, k, V, k', V', Bdd')

    fun (* GEN BEGIN FUN FIRST *) inheritDTop (B, k, I.Pi ((I.Dec (_, V1), I.No), V2),
                     k', I.Pi ((I.Dec (_, V1'), I.No), V2'),
                     Bdd') =
          inheritG (B, k, V1, k', V1',
                    inheritDTop (B, k+1, V2, k'+1, V2', Bdd')) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inheritDTop (B, k, V as I.Root (I.Const(cid), S),
                     k', V' as I.Root (I.Const(cid'), S'), Bdd') =
        (* cid = cid' *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val mS = valOf (ModeTable.modeLookup (cid)) (* GEN END TAG OUTSIDE LET *)
        in
          inheritSpineMode (M.Top, mS, B, k, S, k', S', Bdd')
        end (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) inheritDBot (B, k, I.Pi ((I.Dec (_, V1), I.No), V2),
                     k', I.Pi ((I.Dec (_, V1'), I.No), V2'),
                     Bdd') =
          inheritDBot (B, k+1, V2, k'+1, V2', Bdd') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inheritDBot (B, k, I.Root (I.Const(cid), S),
                     k', I.Root (I.Const (cid'), S'), Bdd') =
          (* cid = cid' *)
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val mS = valOf (ModeTable.modeLookup (cid)) (* GEN END TAG OUTSIDE LET *)
          in
            inheritSpineMode (M.Bot, mS, B, k, S, k', S', Bdd')
          end (* GEN END FUN BRANCH *)

    and inheritG (B, k, I.Root (I.Const (cid), S),
                  k', V' as I.Root (I.Const (cid'), S'), Bdd') =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val mS = valOf (ModeTable.modeLookup (cid)) (* GEN END TAG OUTSIDE LET *)
        in
          (* mode dependency in Goal: first M.Top, then M.Bot *)
          inheritSpineMode (M.Bot, mS, B, k, S, k', S',
                           inheritSpineMode (M.Top, mS, B, k, S, k', S', Bdd'))
        end

    and (* GEN BEGIN FUN FIRST *) inheritSpineMode (mode, ModeSyn.Mnil, B, k, I.Nil, k', I.Nil, Bdd') = Bdd' (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inheritSpineMode (mode, ModeSyn.Mapp (m, mS), B, k, I.App (U, S),
                          k', I.App (U', S'), Bdd') =
          if modeEq (m, mode)
            then inheritSpineMode (mode, mS, B, k, S, k', S',
                                   inheritExp (B, k, U, k', U', Bdd'))
          else inheritSpineMode (mode, mS, B, k, S, k', S', Bdd') (* GEN END FUN BRANCH *)

    fun inheritSplitDepth (S as M.State (_, M.Prefix (G, M, B), V),
                           S' as M.State (name', M.Prefix (G', M', B'), V')) =
        (* S' *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val d = I.ctxLength G (* GEN END TAG OUTSIDE LET *)         (* current first occurrence depth in V *)
          (* GEN BEGIN TAG OUTSIDE LET *) val d' = I.ctxLength G' (* GEN END TAG OUTSIDE LET *)       (* current first occurrence depth in V' *)
          (* mode dependency in Clause: first M.Top then M.Bot *)
          (* check proper traversal *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V = Whnf.normalize (V, I.id) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = Whnf.normalize (V', I.id) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (B'', 0, 0) = inheritDBot (B, 0, V, 0, V',
                                            inheritDTop (B, 0, V, 0, V', (I.Null, d, d'))) (* GEN END TAG OUTSIDE LET *)
        in
          M.State (name', M.Prefix (G', M', B''), V')
        end

    (* abstractInit (M.State (name, M.Prefix (G, M, B), V)) = F'

       State is the state before splitting, to inherit splitting depths.
       Invariant:
       If   G |- V : L
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   following holds: S' = F' (name', G', M', s')
                                    S' is a new state
    *)
    fun abstractInit (M.State (name, GM, V)) (name', M.Prefix (G', M', B'), s') =
          inheritSplitDepth
          (M.State (name, GM, V),
           MetaAbstract.abstract (M.State (name ^ name', M.Prefix (G', M', B'), I.EClo (V, s'))))

    (* abstractInit (x:D, mode, F) = F'

       Invariant:
       If   G |- D : L
       and  forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   S' = F (name', G', M', s')
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            then   following holds: S' = F (name', (G', D[s]) , (M', mode) , 1 . s' o ^)
                                    is a new state
    *)
    fun abstractCont ((D, mode, b), abstract) (name', M.Prefix (G', M', B'), s') =
          abstract (name', M.Prefix (I.Decl (G', I.decSub (D, s')), I.Decl (M', mode),
                                     I.Decl (B', b)),
                    I.dot1 s')

    fun makeAddressInit S k = (S, k)
    fun makeAddressCont makeAddress k = makeAddress (k+1)

    (* expand' (M.Prefix (G, M), isIndex, abstract, makeAddress) = (M.Prefix (G', M'), s', ops')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract, dynamic abstraction function
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then |- G' ctx
       and  G' |- M' mtx
       and  G' is a subcontext of G where all Top variables have been replaced
            by EVars'
       and  G' |- s' : G
       and  ops' is a list of all possiblie splitting operators
    *)
    fun (* GEN BEGIN FUN FIRST *) expand' (M.Prefix (I.Null, I.Null, I.Null), isIndex, abstract, makeAddress) =
          (M.Prefix (I.Null, I.Null, I.Null), I.id, nil) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) expand' (M.Prefix (I.Decl (G, D), I.Decl (M, mode as M.Top), I.Decl (B, b)),
                 isIndex, abstract, makeAddress) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (M.Prefix (G', M', B'), s', ops) =
                expand' (M.Prefix (G, M, B), isIndexSucc (D, isIndex),
                         abstractCont ((D, mode, b), abstract),
                         makeAddressCont makeAddress) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (xOpt, V) = D (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G', I.EClo (V, s')) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val ops' = if b > 0 (* check if splitting bound > 0 *)
                andalso not (isIndex 1) andalso checkDec (M, D)
                           then
                               (makeAddress 1, split (M.Prefix (G', M', B'), (D, s'), abstract))
                               :: ops
                       else ops (* GEN END TAG OUTSIDE LET *)
          in
            (M.Prefix (G', M', B'), I.Dot (I.Exp (X), s'), ops')
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) expand' (M.Prefix (I.Decl (G, D), I.Decl (M, mode as M.Bot), I.Decl (B, b)),
                 isIndex, abstract, makeAddress) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (M.Prefix (G', M', B'), s', ops) =
                expand' (M.Prefix (G, M, B), isIndexSucc (D, isIndex), (* -###- *)
                         abstractCont ((D, mode, b), abstract),
                         makeAddressCont makeAddress) (* GEN END TAG OUTSIDE LET *)
          in
            (M.Prefix (I.Decl (G', I.decSub (D, s')), I.Decl (M', M.Bot),
                       I.Decl (B', b)), (* b = 0 *)
             I.dot1 s', ops)
          end (* GEN END FUN BRANCH *)

    (* expand ((G, M), V) = ops'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : L
       then ops' is a list of all possiblie splitting operators
    *)
    fun expand (S as M.State (name, M.Prefix (G, M, B), V)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (_, _, ops) =
          expand' (M.Prefix (G, M, B), isIndexInit, abstractInit S, makeAddressInit S) (* GEN END TAG OUTSIDE LET *)
      in
        ops
      end

    (* index (Op) = k

       Invariant:
       If   Op = (_, S) then k = |S|
    *)
    fun index (_, Sl) = List.length Sl


    (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl) then Sl' = Sl
    *)
    fun apply (_, Sl) =
      map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (Active S) => S
            | InActive => raise Error "Not applicable: leftover constraints" (* GEN END FUNCTION EXPRESSION *))
      Sl


    (* menu (Op) = s'

       Invariant:
       If   Op = ((G, D), Sl)
       and  G |- D : L
       then s' = string describing the operator
    *)
    fun menu (Op as ((M.State (name, M.Prefix (G, M, B), V), i), Sl)) =
        let
          fun (* GEN BEGIN FUN FIRST *) active (nil, n) = n (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) active (InActive :: L, n) = active (L, n) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) active ((Active _) :: L, n) = active (L, n+1) (* GEN END FUN BRANCH *)
    
          fun (* GEN BEGIN FUN FIRST *) inactive (nil, n) = n (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) inactive (InActive :: L, n) = inactive (L, n+1) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) inactive ((Active _) :: L, n) = inactive (L, n) (* GEN END FUN BRANCH *)
    
          fun (* GEN BEGIN FUN FIRST *) indexToString 0 = "zero cases" (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) indexToString 1 = "1 case" (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) indexToString n = (Int.toString n) ^ " cases" (* GEN END FUN BRANCH *)
    
          fun (* GEN BEGIN FUN FIRST *) flagToString (_, 0) = "" (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) flagToString (n, m) = " [active: " ^(Int.toString n) ^
                " inactive: " ^ (Int.toString m) ^ "]" (* GEN END FUN BRANCH *)
        in
          "Splitting : " ^ Print.decToString (G, I.ctxDec (G, i))
          ^ " (" ^ (indexToString (index Op)) ^
           (flagToString (active (Sl, 0), inactive (Sl, 0))) ^ ")"
        end

    fun var ((_, i), _) = i

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val expand = expand (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val apply = apply (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val var = var (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val index = index (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val menu = menu (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *);  (* functor Splitting *)
