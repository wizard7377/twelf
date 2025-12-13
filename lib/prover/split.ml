(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Split
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)
   structure Constraints : CONSTRAINTS
   (*! sharing Constraints.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (*! sharing Abstract.Tomega = Tomega' !*)
   structure Index : INDEX
   (*! sharing Index.IntSyn = IntSyn' !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)
       ) : SPLIT =

struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error of string

  local
    structure T = Tomega
    structure I = IntSyn
    structure S = State'

    datatype operator =
      Split of T.prg option ref * T.prg * string

    (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
    fun (* GEN BEGIN FUN FIRST *) weaken (I.Null, a) = I.id (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) weaken (I.Decl (G', D as I.Dec (name, V)), a) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val w' = weaken (G', a) (* GEN END TAG OUTSIDE LET *)
        in
          if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
          else I.comp (w', I.shift)
        end (* GEN END FUN BRANCH *)
      (* added next case, probably should not arise *)
      (* Sun Dec 16 10:42:05 2001 -fp !!! *)
      (*
      | weaken (I.Decl (G', D as I.BDec _), a) =
           I.dot1 (weaken (G', a))
      *)

    (* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *)
    fun createEVar (G, V) =
        let (* G |- V : L *)
          (* GEN BEGIN TAG OUTSIDE LET *) val w = weaken (G, I.targetFam V) (* GEN END TAG OUTSIDE LET *)       (* G  |- w  : G'    *)
          (* GEN BEGIN TAG OUTSIDE LET *) val iw = Whnf.invert w (* GEN END TAG OUTSIDE LET *)                  (* G' |- iw : G     *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G' = Whnf.strengthen (iw, G) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X' = I.newEVar (G', I.EClo (V, iw)) (* GEN END TAG OUTSIDE LET *) (* G' |- X' : V[iw] *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.EClo (X', w) (* GEN END TAG OUTSIDE LET *)                  (* G  |- X  : V     *)
        in
          X
        end


    (* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)
    fun instEVars (Vs, p, XsRev) = instEVarsW (Whnf.whnf Vs, p, XsRev)
    and (* GEN BEGIN FUN FIRST *) instEVarsW (Vs, 0, XsRev) = (Vs, XsRev) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) instEVarsW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), p, XsRev) =
        let (* p > 0 *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X1 = I.newEVar (I.Null, I.EClo (V1, s)) (* GEN END TAG OUTSIDE LET *) (* all EVars are global *)
        in
          instEVars ((V2, I.Dot (I.Exp (X1), s)), p-1, SOME(X1)::XsRev)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) instEVarsW ((I.Pi ((I.BDec (_, (l, t)), _), V2), s), p, XsRev) =
        (* G0 |- t : Gsome *)
        (* . |- s : G0 *)
        let (* p > 0 *)
          (* GEN BEGIN TAG OUTSIDE LET *) val L1 = I.newLVar (I.Shift(0), (l, I.comp(t,s))) (* GEN END TAG OUTSIDE LET *) (* --cs Sun Dec  1 06:33:27 2002 *)
        in
          instEVars ((V2, I.Dot (I.Block (L1), s)), p-1, NONE::XsRev)
        end (* GEN END FUN BRANCH *)

    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    local
      (* GEN BEGIN TAG OUTSIDE LET *) val caseList : (T.dec I.ctx * T.sub) list ref = ref nil (* GEN END TAG OUTSIDE LET *)
    in
      fun resetCases () = (caseList := nil)
      fun addCase (Psi, t) = (caseList := (Psi, t) :: !caseList)
      fun getCases () = (!caseList)
    end

    (* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
    fun createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)
    and (* GEN BEGIN FUN FIRST *) createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs) (* GEN END FUN FIRST *)   (* s = id *)
      | (* GEN BEGIN FUN BRANCH *) createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
        let (* G |- V1[s] : L *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X = createEVar (G, I.EClo (V1, s)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s))) (* GEN END TAG OUTSIDE LET *)
        in
          (I.App (X, S), Vs)
        end (* GEN END FUN BRANCH *)
      (* Uni or other cases should be impossible *)

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomConst (G, H as I.Const (cid)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V = I.constType cid (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (S, Vs) = createEVarSpine (G, (V, I.id)) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Root (H, S), Vs)
        end

    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomBVar (G, k) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V) = I.ctxDec (G, k) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (S, Vs) = createEVarSpine (G, (V, I.id)) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Root (I.BVar (k), S), Vs)
        end


    (* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomProj (G, H, (V, s)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (S, Vs') = createEVarSpine (G, (V, s)) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Root (H, S), Vs')
        end

    fun (* GEN BEGIN FUN FIRST *) constCases (G, Vs, nil, sc) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) constCases (G, Vs, I.Const(c)::sgn', sc) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (U, Vs') = createAtomConst (G, I.Const c) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                                   if Unify.unifiable (G, Vs, Vs')
                                     then sc U
                                   else () (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          constCases (G, Vs, sgn', sc)
        end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) paramCases (G, Vs, 0, sc) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) paramCases (G, Vs, k, sc) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (U, Vs') = createAtomBVar (G, k) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                                   if Unify.unifiable (G, Vs, Vs')
                                     then sc U
                                   else () (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          paramCases (G, Vs, k-1, sc)
        end (* GEN END FUN BRANCH *)

    (* createEVarSub G' = s

       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
    fun (* GEN BEGIN FUN FIRST *) createEVarSub (I.Null) = I.id (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createEVarSub (I.Decl(G', D as I.Dec (_, V))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val s = createEVarSub G' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = I.EClo (V, s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (I.Null, V') (* GEN END TAG OUTSIDE LET *)
        in
          I.Dot (I.Exp X, s)
        end (* GEN END FUN BRANCH *)

    (* hack *)
    fun blockName (cid) = I.conDecName (I.sgnLookup (cid))

    (* blockCases (G, Vs, B, (Gsome, piDecs), sc) =

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
    fun blockCases (G, Vs, cid, (Gsome, piDecs), sc) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createEVarSub Gsome (* GEN END TAG OUTSIDE LET *)   (* accounts for subordination *)
          (* . |- t : Gsome *)
          (* GEN BEGIN TAG OUTSIDE LET *) val sk = I.Shift (I.ctxLength(G)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = I.comp (t, sk) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val lvar = I.newLVar (sk, (cid, t')) (* GEN END TAG OUTSIDE LET *)  (* --cs Sun Dec  1 06:33:41 2002 *)
          (* G |- t' : Gsome *)
        in
          blockCases' (G, Vs, (lvar, 1), (t', piDecs), sc)
        end
    and (* GEN BEGIN FUN FIRST *) blockCases' (G, Vs, (lvar, i), (t, nil), sc) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) blockCases' (G, Vs, (lvar, i), (t, I.Dec (_, V')::piDecs), sc) =
        let
          (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
          (* so G |- V'[t'] : type *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (U, Vs') = createAtomProj (G, I.Proj (lvar, i), (V', t)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = CSManager.trail ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => if Unify.unifiable (G, Vs, Vs')
                                              then sc U
                                            else () (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = I.Dot (I.Exp (I.Root (I.Proj (lvar, i), I.Nil)), t) (* GEN END TAG OUTSIDE LET *)
        in
          blockCases' (G, Vs, (lvar, i+1), (t', piDecs), sc)
        end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) worldCases (G, Vs, T.Worlds (nil), sc) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) worldCases (G, Vs, T.Worlds (cid::cids), sc) =
          ( blockCases (G, Vs, cid, I.constBlock cid, sc) ;
            worldCases (G, Vs, T.Worlds (cids), sc) ) (* GEN END FUN BRANCH *)

    fun lowerSplit (G, Vs, W, sc) = lowerSplitW (G, Whnf.whnf Vs, W, sc)
    and lowerSplitW (G, Vs as (I.Root (I.Const a, _), s), W, sc) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = constCases (G, Vs, Index.lookup a, sc) (* GEN END TAG OUTSIDE LET *) (* will trail *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = paramCases (G, Vs, I.ctxLength G, sc) (* GEN END TAG OUTSIDE LET *) (* will trail *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = worldCases (G, Vs, W, sc) (* GEN END TAG OUTSIDE LET *) (* will trail *)
        in
          ()
        end
 (*     | lowerSplitW (G, (I.Pi ((D, P), V), s), W, sc) =
        let
          val D' = I.decSub (D, s)
        in
          lowerSplit (I.Decl (G, D'), (V, I.dot1 s), W, fn U => sc (I.Lam (D', U)))
        end
      we assume that all EVars are lowere :-)
*)

    (* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *)
    fun splitEVar ((X as I.EVar (_, GX, V, _)), W, sc) = (* GX = I.Null *)
          lowerSplit (I.Null, (V, I.id), W,
                      (* GEN BEGIN FUNCTION EXPRESSION *) fn U => if Unify.unifiable (I.Null, (X, I.id), (U, I.id))
                                then sc ()
                              else () (* GEN END FUNCTION EXPRESSION *))

    (* createSub (Psi) = s

       Invariant:
       If   Psi is a meta context
       then s = Xp...X1.id, all Xi are new EVars/LVars/MVars
       and  . |- s : Psi
    *)
    fun (* GEN BEGIN FUN FIRST *) createSub (I.Null) = (T.id) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createSub (I.Decl (Psi, T.UDec (I.Dec (xOpt, V1)))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (t') = createSub Psi (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (I.Null, I.EClo (Whnf.whnf (V1, T.coerceSub t'))) (* GEN END TAG OUTSIDE LET *) (* all EVars are global and lowered *)
        in
           (T.Dot (T.Exp X, t'))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) createSub (I.Decl (Psi, T.UDec (I.BDec (_, (l, s))))) =
        (* Psi0 |- t : Gsome *)
        (* . |- s : Psi0 *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (t') = createSub Psi (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val L = I.newLVar (I.Shift(0), (l, I.comp(s, T.coerceSub t'))) (* GEN END TAG OUTSIDE LET *)
                                        (* --cs Sun Dec  1 06:34:00 2002 *)
        in
          (T.Dot (T.Block L, t'))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) createSub (I.Decl (Psi, T.PDec (_, F, TC1, TC2))) =
        let (* p > 0 *)
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = createSub Psi (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Y = T.newEVarTC (I.Null, T.FClo (F, t'), TC1, TC2) (* GEN END TAG OUTSIDE LET *)
        in
          (T.Dot (T.Prg Y, t'))
        end (* GEN END FUN BRANCH *)


    (* mkCases L F= Ss

       Invariant:
       If   L is a list of cases (Psi1, t1) .... (Psin, tn)
       and  Psii |- ti : Psi
       and  Psi  |- F formula
       then Ss is a list of States S1 ... Sn
       and  Si = (Psii, Fi)
       where  Psii |- Fi = F [ti]  formula
    *)

    fun (* GEN BEGIN FUN FIRST *) mkCases (nil, F) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) mkCases ((Psi, t) :: cs, F) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val X = T.newEVar (Psi, T.FClo (F, t)) (* GEN END TAG OUTSIDE LET *)
        in
          (Psi, t, X) :: mkCases (cs, F)
        end (* GEN END FUN BRANCH *)


    (* split S = S1 ... Sn

       Invariant:
       If   S = (P |> F)
       then Si = (Pi |> Fi)
       s.t. there exists substitution si
            and  Pi |- si : P
            and  Pi |- Fi = F[si]
            and  for every G |- t : P,

                 there ex. an i among 1..n
                 and a substitution t',
                 s.t. G |- t' : Pi
                 and  t = t' [si]
    *)

    fun split (S.Focus (T.EVar (Psi, r, F, NONE, NONE, _), W)) =
      let
    
        (* splitXs (G, i) (Xs, F, W, sc) = Os
           Invariant:
           If   Psi is a CONTEXT
           and  G ~ Psi a context,
           and  G |- i : V
           and  Psi |- F formula
           and  Xs are all logic variables
           then Os is a list of splitting operators
        *)
        fun (* GEN BEGIN FUN FIRST *) splitXs (G, i) (nil, _, _, _) = nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) splitXs (G, i) (X :: Xs, F, W, sc) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 6
                        then print ("Split " ^ Print.expToString (I.Null, X) ^ ".\n")
                      else () (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Os = splitXs (G,i+1) (Xs, F, W, sc) (* GEN END TAG OUTSIDE LET *)    (* returns a list of operators *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = resetCases () (* GEN END TAG OUTSIDE LET *)
              (*            val I.Dec (SOME s, _) = I.ctxLookup (G, i) *)
              (* GEN BEGIN TAG OUTSIDE LET *) val s = Print.expToString (G, X) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Os' = (splitEVar (X, W, sc);
                         Split (r, T.Case (T.Cases (mkCases (getCases (), F))), s) :: Os)
                handle  Constraints.Error (constrs) =>
                  (if !Global.chatter >= 6
                     then print ("Inactive split:\n" ^ Print.cnstrsToString (constrs) ^ "\n")
                   else ();
                     Os) (* GEN END TAG OUTSIDE LET *)
            in
              Os'
            end (* GEN END FUN BRANCH *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val t = createSub Psi (* GEN END TAG OUTSIDE LET *)  (* . |- t :: Psi *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Xs = State.collectLFSub t (* GEN END TAG OUTSIDE LET *)
        fun init () = (addCase (Abstract.abstractTomegaSub t))
        (* GEN BEGIN TAG OUTSIDE LET *) val G = T.coerceCtx Psi (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Os = splitXs (G, 1) (Xs, F, W, init) (* GEN END TAG OUTSIDE LET *)
      in
        Os
      end

    fun expand (S as S.Focus (T.EVar (Psi, r, F, NONE, NONE, _), W)) =
      if Abstract.closedCTX Psi then split S else []

    (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)
    fun apply (Split (r, P, s)) = (r := SOME P)    (* trailing required -cs Thu Apr 22 12:05:04 2004 *)
    fun menu (Split (_, _, s)) = "Split " ^ s
  in
    type operator = operator

    (* GEN BEGIN TAG OUTSIDE LET *) val expand = expand (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val apply = apply (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val menu = menu (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *) (* functor Split *)