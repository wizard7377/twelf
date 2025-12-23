(* Splitting: Version 1.4 *)

(* Author: Carsten Schuermann *)

module type SPLIT = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure Tomega : Tomega.TOMEGA !*)
  module State : State.STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end

(* signature Split *)
(* State definition for_sml Proof Search *)

(* Author: Carsten Schuermann *)

module Split
    (Global : Global.GLOBAL)
    (State' : State.STATE)
    (Whnf : Whnf.WHNF)
    (Unify : Unify.UNIFY)
    (Constraints : Constraints.CONSTRAINTS)
    (Abstract : Abstract.ABSTRACT)
    (Index : Index.INDEX)
    (Print : Print.PRINT)
    (TypeCheck : Typecheck.TYPECHECK)
    (Subordinate : Subordinate.SUBORDINATE) : SPLIT = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  module State = State'

  exception Error of string

  module T = Tomega
  module I = IntSyn
  module S = State'

  type operator = Split of T.prg option ref * T.prg * string
  (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)

  let rec weaken = function
    | I.Null, a -> I.id
    | I.Decl (G', D), a ->
        let w' = weaken (G', a) in
        if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
        else I.comp (w', I.shift)
  (* added next case, probably should not arise *)

  (* Sun Dec 16 10:42:05 2001 -fp !!! *)

  (*
      | weaken (I.Decl (G', I.BDec _), a) =
           I.dot1 (weaken (G', a))
      *)

  (* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *)

  let rec createEVar (G, V) =
    (* G |- V : L *)
    (* G  |- w  : G'    *)
    (* G' |- iw : G     *)
    (* G' |- X' : V[iw] *)
    (* G  |- X  : V     *)
    let w = weaken (G, I.targetFam V) in
    let iw = Whnf.invert w in
    let G' = Whnf.strengthen (iw, G) in
    let X' = I.newEVar (G', I.EClo (V, iw)) in
    let X = I.EClo (X', w) in
    X
  (* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)

  let rec instEVars (Vs, p, XsRev) = instEVarsW (Whnf.whnf Vs, p, XsRev)

  and instEVarsW = function
    | Vs, 0, XsRev -> (Vs, XsRev)
    | (I.Pi ((I.Dec (xOpt, V1), _), V2), s), p, XsRev ->
        (* p > 0 *)
        (* all EVars are global *)
        let X1 = I.newEVar (I.Null, I.EClo (V1, s)) in
        instEVars ((V2, I.Dot (I.Exp X1, s)), p - 1, Some X1 :: XsRev)
    | (I.Pi ((I.BDec (_, (l, t)), _), V2), s), p, XsRev ->
        (* p > 0 *)
        (* --cs Sun Dec  1 06:33:27 2002 *)
        let L1 = I.newLVar (I.Shift 0, (l, I.comp (t, s))) in
        instEVars ((V2, I.Dot (I.Block L1, s)), p - 1, None :: XsRev)
  (* caseList is a list of possibilities for_sml a variables
       to be split.  a mutable reference so it
       can be updated in the success continuation.
    *)

  let caseList : T.dec I.ctx * T.sub list ref = ref []
  let rec resetCases () = caseList := []
  let rec addCase (Psi, t) = caseList := (Psi, t) :: !caseList
  let rec getCases () = !caseList
  (* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)

  let rec createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)

  and createEVarSpineW = function
    | G, Vs -> (I.Nil, Vs)
    | G, (I.Pi ((D, _), V2), s) ->
        (* G |- V1[s] : L *)
        let X = createEVar (G, I.EClo (V1, s)) in
        let S, Vs = createEVarSpine (G, (V2, I.Dot (I.Exp X, s))) in
        (I.App (X, S), Vs)
  (* Uni or other cases should be impossible *)

  (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)

  let rec createAtomConst (G, H) =
    let V = I.constType cid in
    let S, Vs = createEVarSpine (G, (V, I.id)) in
    (I.Root (H, S), Vs)
  (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)

  let rec createAtomBVar (G, k) =
    let (I.Dec (_, V)) = I.ctxDec (G, k) in
    let S, Vs = createEVarSpine (G, (V, I.id)) in
    (I.Root (I.BVar k, S), Vs)
  (* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)

  let rec createAtomProj (G, H, (V, s)) =
    let S, Vs' = createEVarSpine (G, (V, s)) in
    (I.Root (H, S), Vs')

  let rec constCases = function
    | G, Vs, [], sc -> ()
    | G, Vs, I.Const c :: sgn', sc ->
        let U, Vs' = createAtomConst (G, I.Const c) in
        let _ =
          Cs.CSManager.trail (fun () ->
              if Unify.unifiable (G, Vs, Vs') then sc U else ())
        in
        constCases (G, Vs, sgn', sc)

  let rec paramCases = function
    | G, Vs, 0, sc -> ()
    | G, Vs, k, sc ->
        let U, Vs' = createAtomBVar (G, k) in
        let _ =
          Cs.CSManager.trail (fun () ->
              if Unify.unifiable (G, Vs, Vs') then sc U else ())
        in
        paramCases (G, Vs, k - 1, sc)
  (* createEVarSub G' = s

       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)

  let rec createEVarSub = function
    | I.Null -> I.id
    | I.Decl (G', D) ->
        let s = createEVarSub G' in
        let V' = I.EClo (V, s) in
        let X = I.newEVar (I.Null, V') in
        I.Dot (I.Exp X, s)
  (* hack *)

  let rec blockName cid = I.conDecName (I.sgnLookup cid)
  (* blockCases (G, Vs, B, (Gsome, piDecs), sc) =

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for_sml any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)

  let rec blockCases (G, Vs, cid, (Gsome, piDecs), sc) =
    (* accounts for_sml subordination *)
    (* . |- t : Gsome *)
    (* --cs Sun Dec  1 06:33:41 2002 *)
    (* G |- t' : Gsome *)
    let t = createEVarSub Gsome in
    let sk = I.Shift (I.ctxLength G) in
    let t' = I.comp (t, sk) in
    let lvar = I.newLVar (sk, (cid, t')) in
    blockCases' (G, Vs, (lvar, 1), (t', piDecs), sc)

  and blockCases' = function
    | G, Vs, (lvar, i), (t, []), sc -> ()
    | G, Vs, (lvar, i), (t, I.Dec (_, V') :: piDecs), sc ->
        (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
        (* so G |- V'[t'] : type *)
        let U, Vs' = createAtomProj (G, I.Proj (lvar, i), (V', t)) in
        let _ =
          Cs.CSManager.trail (fun () ->
              if Unify.unifiable (G, Vs, Vs') then sc U else ())
        in
        let t' = I.Dot (I.Exp (I.Root (I.Proj (lvar, i), I.Nil)), t) in
        blockCases' (G, Vs, (lvar, i + 1), (t', piDecs), sc)

  let rec worldCases = function
    | G, Vs, T.Worlds [], sc -> ()
    | G, Vs, T.Worlds (cid :: cids), sc ->
        blockCases (G, Vs, cid, I.constBlock cid, sc);
        worldCases (G, Vs, T.Worlds cids, sc)

  let rec lowerSplit (G, Vs, W, sc) = lowerSplitW (G, Whnf.whnf Vs, W, sc)

  and lowerSplitW (G, Vs, W, sc) =
    (* will trail *)
    (* will trail *)
    (* will trail *)
    let _ = constCases (G, Vs, Index.lookup a, sc) in
    let _ = paramCases (G, Vs, I.ctxLength G, sc) in
    let _ = worldCases (G, Vs, W, sc) in
    ()
  (*     | lowerSplitW (G, (I.Pi ((D, P), V), s), W, sc) =
        let
          val D' = I.decSub (D, s)
        in
          lowerSplit (I.Decl (G, D'), (V, I.dot1 s), W, fn U => sc (I.Lam (D', U)))
        end
      we assume that all EVars are lowere :-)
*)

  (* splitEVar (X, W, sc) = ()

       calls sc () for_sml all cases, after instantiation of X
       W are the currently possible worlds
    *)

  let rec splitEVar (X, W, sc) =
    (* GX = I.Null *)
    lowerSplit
      ( I.Null,
        (V, I.id),
        W,
        fun U ->
          if Unify.unifiable (I.Null, (X, I.id), (U, I.id)) then sc () else ()
      )
  (* createSub (Psi) = s

       Invariant:
       If   Psi is a meta context
       then s = Xp...X1.id, all Xi are new EVars/LVars/MVars
       and  . |- s : Psi
    *)

  let rec createSub = function
    | I.Null -> T.id
    | I.Decl (Psi, T.UDec (I.Dec (xOpt, V1))) ->
        (* all EVars are global and lowered *)
        let t' = createSub Psi in
        let X = I.newEVar (I.Null, I.EClo (Whnf.whnf (V1, T.coerceSub t'))) in
        T.Dot (T.Exp X, t')
    | I.Decl (Psi, T.UDec (I.BDec (_, (l, s)))) ->
        (* --cs Sun Dec  1 06:34:00 2002 *)
        let t' = createSub Psi in
        let L = I.newLVar (I.Shift 0, (l, I.comp (s, T.coerceSub t'))) in
        T.Dot (T.Block L, t')
    | I.Decl (Psi, T.PDec (_, F, TC1, TC2)) ->
        (* p > 0 *)
        let t' = createSub Psi in
        let Y = T.newEVarTC (I.Null, T.FClo (F, t'), TC1, TC2) in
        T.Dot (T.Prg Y, t')
  (* mkCases L F= Ss

       Invariant:
       If   L is a list of cases (Psi1, t1) .... (Psin, tn)
       and  Psii |- ti : Psi
       and  Psi  |- F formula
       then Ss is a list of States S1 ... Sn
       and  Si = (Psii, Fi)
       where  Psii |- Fi = F [ti]  formula
    *)

  let rec mkCases = function
    | [], F -> []
    | (Psi, t) :: cs, F ->
        let X = T.newEVar (Psi, T.FClo (F, t)) in
        (Psi, t, X) :: mkCases (cs, F)
  (* split S = S1 ... Sn

       Invariant:
       If   S = (P |> F)
       then Si = (Pi |> Fi)
       s.t. there exists substitution si
            and  Pi |- si : P
            and  Pi |- Fi = F[si]
            and  for_sml every G |- t : P,

                 there ex. an i among 1..n
                 and a substitution t',
                 s.t. G |- t' : Pi
                 and  t = t' [si]
    *)

  let rec split (S.Focus (T.EVar (Psi, r, F, None, None, _), W)) =
    (* splitXs (G, i) (Xs, F, W, sc) = Os
           Invariant:
           If   Psi is a CONTEXT
           and  G ~ Psi a context,
           and  G |- i : V
           and  Psi |- F formula
           and  Xs are all logic variables
           then Os is a list of splitting operators
        *)
    (* . |- t :: Psi *)
    let rec splitXs = function
      | (G, i), ([], _, _, _) -> []
      | (G, i), (X :: Xs, F, W, sc) ->
          (* returns a list of operators *)
          (*            val I.Dec (SOME s, _) = I.ctxLookup (G, i) *)
          let _ =
            if !Global.chatter >= 6 then
              print ("Split " ^ Print.expToString (I.Null, X) ^ ".\n")
            else ()
          in
          let Os = splitXs (G, i + 1) (Xs, F, W, sc) in
          let _ = resetCases () in
          let s = Print.expToString (G, X) in
          let Os' =
            try
              splitEVar (X, W, sc);
              Split (r, T.Case (T.Cases (mkCases (getCases (), F))), s) :: Os
            with Constraints.Error constrs ->
              if !Global.chatter >= 6 then
                print ("Inactive split:\n" ^ Print.cnstrsToString constrs ^ "\n")
              else ();
              Os
          in
          Os'
    in
    let t = createSub Psi in
    let Xs = State.collectLFSub t in
    let rec init () = addCase (Abstract.abstractTomegaSub t) in
    let G = T.coerceCtx Psi in
    let Os = splitXs (G, 1) (Xs, F, W, init) in
    Os

  let rec expand S = if Abstract.closedCTX Psi then split S else []
  (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)

  let rec apply (Split (r, P, s)) = r := Some P
  (* trailing required -cs Thu Apr 22 12:05:04 2004 *)

  let rec menu (Split (_, _, s)) = "Split " ^ s

  type operator = operator

  let expand = expand
  let apply = apply
  let menu = menu
end

(* functor Split *)
