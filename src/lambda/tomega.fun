(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao, Adam Poswolsky *)

functor Tomega (structure Whnf : WHNF
                structure Conv : CONV) : TOMEGA =
struct
  exception Error of string

  type label = int
  type lemma = int

  datatype worlds = Worlds of IntSyn.cid list

  datatype quantifier = Implicit | Explicit

  datatype tc   =                       (* Terminiation Condition     *)
    Abs of IntSyn.dec * tc              (* T ::= {{D}} O              *)
  | Conj of tc * tc                     (*     | O1 ^ O2              *)
  | Base of ((IntSyn.exp * IntSyn.sub) *
             (IntSyn.exp * IntSyn.sub)) Order.order

  datatype for                          (* Formulas                   *)
  = World of worlds * for               (* F ::= World l1...ln. F     *)
  | All of (dec * quantifier) * for     (*     | All LD. F            *)
  | Ex  of (IntSyn.dec * quantifier) * for
                                        (*     | Ex  D. F             *)
  | True                                (*     | T                    *)
  | And of for * for                    (*     | F1 ^ F2              *)
  | FClo of for * sub                   (*     | F [t]                *)
  | FVar of (dec IntSyn.ctx * for option ref)
                                        (*     | F (G)                *)

  and dec =                             (* Declaration:               *)
    UDec of IntSyn.dec                  (* D ::= x:A                  *)
  | PDec of string option * for * tc option * tc option
                                        (*     | xx :: F              *)

  and prg =                             (* Programs:                  *)
    Box of worlds * prg                 (*     | box W. P             *)
  | Lam of dec * prg                    (*     | lam LD. P            *)
  | New of prg                          (*     | new P                *)
  | Choose of prg                       (*     | choose P             *)
  | PairExp of IntSyn.exp * prg         (*     | <M, P>               *)
  | PairBlock of IntSyn.block * prg     (*     | <rho, P>             *)
  | PairPrg of prg * prg                (*     | <P1, P2>             *)
  | Unit                                (*     | <>                   *)
  | Redex of prg * spine
  | Rec of dec * prg                    (*     | mu xx. P             *)
  | Case of cases                       (*     | case t of O          *)
  | PClo of prg * sub                   (*     | P [t]                *)
  | Let of dec * prg * prg              (*     | let D = P1 in P2     *)
  | EVar of dec IntSyn.ctx * prg option ref * for * tc option * tc option * IntSyn.exp
                                        (*     | E (G, F, TC)         *)
  | Const of lemma                      (* P ::= cc                   *)
  | Var of int                          (*     | xx                   *)
  | LetPairExp of IntSyn.dec * dec * prg * prg
  | LetUnit of prg * prg

  and spine =                           (* Spines:                    *)
    Nil                                 (* S ::= Nil                  *)
  | AppExp of IntSyn.exp * spine        (*     | P U                  *)
  | AppBlock of IntSyn.block * spine    (*     | P rho                *)
  | AppPrg of prg * spine               (*     | P1 P2                *)
  | SClo of spine * sub                 (*     | S [t]                *)

  and sub =                             (* t ::=                      *)
    Shift of int                        (*       ^n                   *)
  | Dot of front * sub                  (*     | F . t                *)

  and front =                           (* F ::=                      *)
    Idx of int                          (*     | i                    *)
  | Prg of prg                          (*     | p                    *)
  | Exp of IntSyn.exp                   (*     | U                    *)
  | Block of IntSyn.block               (*     | _x                   *)
  | Undef                               (*     | _                    *)

  and cases =                           (* Cases                      *)
    Cases of (dec IntSyn.ctx * sub * prg) list
                                        (* C ::= (Psi' |> s |-> P)    *)

  datatype con_dec =                     (* ConDec                     *)
    ForDec of string * for              (* CD ::= f :: F              *)
  | ValDec of string * prg * for        (*      | f == P              *)

  exception NoMatch

  local
    structure I = IntSyn
    structure O = Order

    val maxLemma = Global.maxCid
    val lemmaArray = Array.array (maxLemma+1, ForDec ("", True))
                   : con_dec Array.array
    val nextLemma = ref 0

    fun lemmaLookup lemma = Array.sub (lemmaArray, lemma)
    fun lemmaAdd (lemmaDec) =
        let
          val lemma = !nextLemma
        in
          if lemma > maxLemma
            then raise Error ("Global signature size " ^ Int.toString (maxLemma+1) ^ " exceeded")
          else (Array.update (lemmaArray, lemma, lemmaDec) ;
                nextLemma := lemma + 1;
                lemma)
        end
    fun lemmaSize () = (!nextLemma)
    fun lemmaDef lemma =
        case (lemmaLookup lemma)
          of ValDec (_, P, _) => P
    fun lemmaFor lemma =
        case (lemmaLookup lemma)
          of ForDec (_, F) => F
           | ValDec (_, _, F) => F

    fun lemmaName s = lemmaName' (!nextLemma) s
    and lemmaName' ~1 s = raise Error "Function name not found"
      | (* GEN CASE BRANCH *) lemmaName' n s =
        (case lemmaLookup n
           of ForDec (s', F) => if s=s' then n
                               else lemmaName' (n-1) s
            | ValDec (s', P, F) => if s=s' then n
                                   else lemmaName' (n-1) s)
           (* not very efficient, improve !!! *)


    (* coerceFront F = F'

       Invariant:
       If    Psi |- F front
       and   G = mu G. G \in Psi
       then  G   |- F' front
    *)
    fun coerceFront (Idx k) = I.Idx k
      | (* GEN CASE BRANCH *) coerceFront (Prg P) = I.Undef
      | (* GEN CASE BRANCH *) coerceFront (Exp M) = I.Exp M
      | (* GEN CASE BRANCH *) coerceFront (Block B) = I.Block B
      | (* GEN CASE BRANCH *) coerceFront (Undef) = I.Undef
    (* --Yu Liao Why cases: Block, Undef aren't defined *)

    (* embedFront F = F'

       Invariant:
       If    Psi |- F front
       and   G = mu G. G \in Psi
       then  G   |- F' front
    *)
    fun embedFront (I.Idx k) = Idx k
      | (* GEN CASE BRANCH *) embedFront (I.Exp U) = Exp U
      | (* GEN CASE BRANCH *) embedFront (I.Block B) = Block B
      | (* GEN CASE BRANCH *) embedFront (I.Undef) = Undef


    (* coerceSub t = s

       Invariant:
       If    Psi |- t : Psi'
       then  G   |- s : G'
       where G = mu G. G \in Psi
       and   G' = mu G. G \in Psi'
    *)
    fun coerceSub (Shift n) = I.Shift n
      | (* GEN CASE BRANCH *) coerceSub (Dot (Ft, t)) =
          I.Dot (coerceFront Ft, coerceSub t)

    fun embedSub (I.Shift n) = Shift n
      | (* GEN CASE BRANCH *) embedSub (I.Dot (Ft, s)) =
          Dot (embedFront Ft, embedSub s)


    (* Definition:
       |- Psi ctx[block] holds iff Psi = _x_1 : (L1, t1), ... _x_n : (Ln, tn)
    *)

    fun revCoerceFront (I.Idx k) = Idx k
      | (* GEN CASE BRANCH *) revCoerceFront (I.Exp M) = Exp M
      | (* GEN CASE BRANCH *) revCoerceFront (I.Block b) = Block b
      | (* GEN CASE BRANCH *) revCoerceFront I.Undef = Undef


    (* revCoerceSub t = s
    coerce substitution in LF level t ==> s in Tomega level *)
    fun revCoerceSub (I.Shift n) = Shift n
      | (* GEN CASE BRANCH *) revCoerceSub (I.Dot (Ft, t)) = Dot(revCoerceFront Ft, revCoerceSub t)


    (* Invariant Yu? *)
    fun revCoerceCtx I.Null = I.Null
      | (* GEN CASE BRANCH *) revCoerceCtx (I.Decl (Psi, D as I.BDec (_, (L, t)))) =
          I.Decl (revCoerceCtx (Psi), UDec D)



    val id = Shift 0

    (* dotEta (Ft, s) = s'

       Invariant:
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)
    fun dotEta (Ft as Idx _, s) = Dot (Ft, s)
      | (* GEN CASE BRANCH *) dotEta (Ft as Exp (U), s) =
        let
          val Ft' = Idx (Whnf.etaContract U)
                   handle Eta => Ft
        in
          Dot (Ft', s)
        end
      | (* GEN CASE BRANCH *) dotEta (Ft as Undef, s) = Dot (Ft, s)


    (* embedCtx G = Psi

       Invariant:
       If   G is an LF ctx
       then Psi is G, embedded into Tomega
    *)
    fun embedCtx I.Null = I.Null
      | (* GEN CASE BRANCH *) embedCtx (I.Decl (G, D)) =
          I.Decl (embedCtx G, UDec D)



      (* orderSub (O, s) = O'

         Invariant:
         If   G' |- O order    and    G |- s : G'
         then G |- O' order
         and  G |- O' == O[s] order
      *)
      fun orderSub (O.Arg ((U, s1), (V, s2)), s) =
            O.Arg ((U,  I.comp (s1, s)), (V, I.comp (s2, s)))
        | (* GEN CASE BRANCH *) orderSub (O.Lex Os, s) = O.Lex (map (fn O => orderSub (O, s)) Os)
        | (* GEN CASE BRANCH *) orderSub (O.Simul Os, s) = O.Simul (map (fn O => orderSub (O, s)) Os)

      fun TCSub (Base O, s) = Base (orderSub (O, s))
        | (* GEN CASE BRANCH *) TCSub (Conj (TC1, TC2), s) = Conj (TCSub (TC1, s), TCSub (TC2, s))
        | (* GEN CASE BRANCH *) TCSub (Abs (D, TC), s) = Abs (I.decSub (D, s), TCSub (TC, I.dot1 s))

      fun TCSubOpt (NONE, s) = NONE
        | (* GEN CASE BRANCH *) TCSubOpt (SOME TC, s) = SOME (TCSub (TC, s))

      (* normalizeTC (O) = O'

         Invariant:
         If   G |- O TC
         then G |- O' TC
         and  G |- O = O' TC
         and  each sub term of O' is in normal form.
      *)
      fun normalizeTC' (O.Arg (Us, Vs)) =
            O.Arg ((Whnf.normalize Us, I.id), (Whnf.normalize Vs, I.id))
        | (* GEN CASE BRANCH *) normalizeTC' (O.Lex Os) = O.Lex (map normalizeTC' Os)
        | (* GEN CASE BRANCH *) normalizeTC' (O.Simul Os) = O.Simul (map normalizeTC' Os)

      fun normalizeTC (Base  O) = Base (normalizeTC' O)
        | (* GEN CASE BRANCH *) normalizeTC (Conj (TC1, TC2)) = Conj (normalizeTC TC1, normalizeTC TC2)
        | (* GEN CASE BRANCH *) normalizeTC (Abs (D, TC)) = Abs (Whnf.normalizeDec (D, I.id), normalizeTC TC)

      fun normalizeTCOpt (NONE) = NONE
        | (* GEN CASE BRANCH *) normalizeTCOpt (SOME TC) = SOME (normalizeTC TC)

      (* convTC (O1, O2) = B'

         Invariant:
         If   G |- O1 TC
         and  G |- O2 TC
         then B' holds iff G |- O1 == O2 TC
      *)
      fun convTC' (O.Arg (Us1, _), O.Arg (Us2, _ )) = Conv.conv (Us1, Us2)
        | (* GEN CASE BRANCH *) convTC' (O.Lex Os1, O.Lex Os2) = convTCs (Os1, Os2)
        | (* GEN CASE BRANCH *) convTC' (O.Simul Os1, O.Simul Os2) = convTCs (Os1, Os2)
      and convTCs (nil, nil) = true
        | (* GEN CASE BRANCH *) convTCs (O1 :: L1, O2 :: L2) =
            convTC' (O1, O2) andalso convTCs (L1, L2)

      fun convTC (Base  O, Base O') =  convTC' (O, O')
        | (* GEN CASE BRANCH *) convTC (Conj (TC1, TC2), Conj (TC1', TC2')) = convTC (TC1, TC1')
                     andalso convTC (TC2, TC2')
        | (* GEN CASE BRANCH *) convTC (Abs (D, TC), Abs (D', TC')) = Conv.convDec ((D, I.id), (D', I.id)) andalso
                     convTC (TC, TC')
        | (* GEN CASE BRANCH *) convTC _ = false

      fun convTCOpt (NONE, NONE) = true
        | (* GEN CASE BRANCH *) convTCOpt (SOME TC1, SOME TC2) = convTC (TC1, TC2)
        | (* GEN CASE BRANCH *) convTCOpt _ = false

    fun transformTC' (G, O.Arg k) =
        let
          val k' = (I.ctxLength G) -k+1
          val I.Dec (_, V) = I.ctxDec (G, k')
        in
          O.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
        end
      | (* GEN CASE BRANCH *) transformTC' (G, O.Lex Os) =
          O.Lex (map (fn O => transformTC' (G, O)) Os)
      | (* GEN CASE BRANCH *) transformTC' (G, O.Simul Os) =
          O.Simul (map (fn O => transformTC' (G, O)) Os)

    fun transformTC (G, All ((UDec D, _), F), Os) =
          Abs (D, transformTC (I.Decl (G, D), F, Os))
      | (* GEN CASE BRANCH *) transformTC (G, And (F1, F2), O :: Os) =
          Conj (transformTC (G, F1, [O]),
                 transformTC (G, F2, Os))
      | (* GEN CASE BRANCH *) transformTC (G, Ex _, [O]) = Base (transformTC' (G, O))





    (* bvarSub (n, t) = Ft'

       Invariant:
       If    Psi |- t : Psi'    Psi' |- n :: F
       then  Ft' = Ftn          if  t = Ft1 .. Ftn .. ^k
         or  Ft' = ^(n+k)       if  t = Ft1 .. Ftm ^k   and m<n
       and   Psi |- Ft' :: F [t]
    *)
    fun varSub (1, Dot(Ft, t)) = Ft
      | (* GEN CASE BRANCH *) varSub (n, Dot(Ft, t)) = varSub (n-1, t)
      | (* GEN CASE BRANCH *) varSub (n, Shift(k))  = Idx (n+k)




    (* frontSub (Ft, t) = Ft'

       Invariant:
       If   Psi |- Ft :: F
       and  Psi' |- t :: Psi
       then Ft' = Ft[t]
       and  Psi' |- Ft' :: F[t]
    *)
    and frontSub (Idx (n), t) = varSub (n, t)
      | (* GEN CASE BRANCH *) frontSub (Exp (U), t) = Exp (I.EClo (U, coerceSub t))
      | (* GEN CASE BRANCH *) frontSub (Prg (P), t) = Prg (PClo (P, t))
      | (* GEN CASE BRANCH *) frontSub (Block B, t) = Block (I.blockSub (B, coerceSub t))
     (* Block case is missing --cs *)


    (* comp (t1, t2) = t

       Invariant:
       If   Psi'' |- t2 :: Psi'
       and  Psi' |- t1 :: Psi
       then t = t1 o t2
       and  Psi'' |- t1 o t2 :: Psi'
    *)
    and comp (Shift (0), t) = t
      | (* GEN CASE BRANCH *) comp (t, Shift (0)) = t
      | (* GEN CASE BRANCH *) comp (Shift (n), Dot (Ft, t)) = comp (Shift (n-1), t)
      | (* GEN CASE BRANCH *) comp (Shift (n), Shift (m)) = Shift (n+m)
      | (* GEN CASE BRANCH *) comp (Dot (Ft, t), t') = Dot (frontSub (Ft, t'), comp (t, t'))




    (* dot1 (t) = t'

       Invariant:
       If   G |- t : G'
       then t' = 1. (t o ^)
       and  for all V t.t.  G' |- V : L
            G, V[t] |- t' : G', V

       If t patsub then t' patsub
    *)
    fun dot1 (t as Shift (0)) = t
      | (* GEN CASE BRANCH *) dot1 t = Dot (Idx(1), comp(t, Shift 1))

    val id = Shift 0
    val shift = Shift 1

    (* weakenSub (Psi) = w

       Invariant:
       If   Psi is a context
       then G is embed Psi
       and  Psi |- w : G
    *)
    fun weakenSub (I.Null) = id
      | (* GEN CASE BRANCH *) weakenSub (I.Decl (Psi, D as UDec _)) =
          dot1 (weakenSub Psi)
      | (* GEN CASE BRANCH *) weakenSub (I.Decl (Psi, D as PDec _)) =
          comp (weakenSub Psi, shift)


    (* forSub (F, t) = F'

       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- F' = F[t] for
    *)
    fun forSub (All ((D, Q), F), t) =
          All ((decSub (D, t), Q),
                 forSub (F, dot1 t))
      | (* GEN CASE BRANCH *) forSub (Ex ((D, Q), F), t) =
          Ex ((I.decSub (D, coerceSub t), Q),
                 forSub (F, dot1 t))
      | (* GEN CASE BRANCH *) forSub (And (F1, F2), t) =
          And (forSub (F1, t),
                 forSub (F2, t))
      | (* GEN CASE BRANCH *) forSub (FClo (F, t1), t2) =
          forSub (F, comp (t1, t2))
      | (* GEN CASE BRANCH *) forSub (World (W, F), t) =
          World (W, forSub (F, t))
      | (* GEN CASE BRANCH *) forSub (True, _) = True



    (* decSub (x::F, t) = D'

       Invariant:
       If   Psi  |- t : Psi'    Psi' |- F formula
       then D' = x:F[t]
       and  Psi  |- F[t] formula
    *)
    and decSub (PDec (x, F, TC1, NONE), t) =
        let
          val s = coerceSub t
        in
          PDec (x, forSub (F, t), TCSubOpt (TC1, s), NONE)
        end
      | (* GEN CASE BRANCH *) decSub (UDec D, t) = UDec (I.decSub (D, coerceSub t))


    (* invertSub s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)
    fun invertSub s =
      let
        (* returns NONE if not found *)
        fun getFrontIndex (Idx k) = SOME(k)
          | (* GEN CASE BRANCH *) getFrontIndex (Prg P) = getPrgIndex(P)
          | (* GEN CASE BRANCH *) getFrontIndex (Exp U) = getExpIndex(U)
          | (* GEN CASE BRANCH *) getFrontIndex (Block B) = getBlockIndex(B)
          | (* GEN CASE BRANCH *) getFrontIndex (Undef) = NONE
    
    
        (* getPrgIndex returns NONE if it is not an index *)
        and getPrgIndex (Redex (Var k, Nil )) = SOME(k)
          | (* GEN CASE BRANCH *) getPrgIndex (Redex (P, Nil)) = getPrgIndex(P)
    
          (* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
          | (* GEN CASE BRANCH *) getPrgIndex (PClo (P,t)) =
               (case getPrgIndex(P) of
                  NONE => NONE
                | SOME i => getFrontIndex (varSub (i, t)))
          | (* GEN CASE BRANCH *) getPrgIndex _ = NONE
    
        (* getExpIndex returns NONE if it is not an index *)
        and getExpIndex (I.Root (I.BVar k, I.Nil)) = SOME(k)
          | (* GEN CASE BRANCH *) getExpIndex (I.Redex (U, I.Nil)) = getExpIndex(U)
          | (* GEN CASE BRANCH *) getExpIndex (I.EClo (U, t)) =
               (case getExpIndex(U) of
                  NONE => NONE
                | SOME i => getFrontIndex (revCoerceFront(I.bvarSub(i, t))))
    
          | (* GEN CASE BRANCH *) getExpIndex (U as I.Lam (I.Dec (_, U1), U2)) = (SOME ( Whnf.etaContract(U) )  handle Whnf.Eta => NONE)
          | (* GEN CASE BRANCH *) getExpIndex _ = NONE
    
        (* getBlockIndex returns NONE if it is not an index *)
        and getBlockIndex (I.Bidx k) = SOME(k)
          | (* GEN CASE BRANCH *) getBlockIndex _ = NONE
    
    
        fun lookup (n, Shift _, p) = NONE
          | (* GEN CASE BRANCH *) lookup (n, Dot (Undef, s'), p) = lookup (n+1, s', p)
          | (* GEN CASE BRANCH *) lookup (n, Dot (Idx k, s'), p) =
            if k = p then SOME n
            else lookup (n+1, s', p)
    
        (* Suggested by ABP
         * If you do not want this, remove the getFrontIndex and other
          | lookup (n, Dot (Ft, s'), p) =
              (case getFrontIndex(Ft) of
                 NONE => lookup (n+1, s', p)
               | SOME k => if (k=p) then SOME n else lookup (n+1, s', p))
        *)
    
        fun invertSub'' (0, si) = si
          | (* GEN CASE BRANCH *) invertSub'' (p, si) =
            (case (lookup (1, s, p))
               of SOME k => invertSub'' (p-1, Dot (Idx k, si))
                | NONE => invertSub'' (p-1, Dot (Undef, si)))
    
        fun invertSub' (n, Shift p) = invertSub'' (p, Shift n)
          | (* GEN CASE BRANCH *) invertSub' (n, Dot (_, s')) = invertSub' (n+1, s')
      in
        invertSub' (0, s)
      end


    (* coerceCtx (Psi) = G

       Invariant:
       If   |- Psi ctx[block]
       then |- G lf-ctx[block]
       and  |- Psi == G
    *)
    fun coerceCtx I.Null = I.Null
      | (* GEN CASE BRANCH *) coerceCtx (I.Decl (Psi, UDec D)) =
          I.Decl (coerceCtx Psi, D)
      | (* GEN CASE BRANCH *) coerceCtx (I.Decl (Psi, PDec (x, _, _, _))) =
          I.Decl (coerceCtx Psi, I.NDec x)



    (* coerceCtx (Psi) = (G, s)

       Invariant:
       If   |- Psi ctx[block]
       then |- G lf-ctx[block]
       and  |- Psi == G
       and  G |- s : Psi
    *)
    fun strengthenCtx Psi =
        let
          val w = weakenSub Psi
          val s = invertSub w
        in
          (coerceCtx Psi, w, s)
        end

    (* convFor ((F1, t1), (F2, t2)) = B

       Invariant:
       If   G |- t1 : G1
       and  G1 |- F1 : formula
       and  G |- t2 : G2
       and  G2 |- F2 : formula
       and  (F1, F2 do not contain abstraction over contextblocks )
       then B holds iff G |- F1[s1] = F2[s2] formula
    *)

    fun convFor ((True, _), (True, _)) = true
      | (* GEN CASE BRANCH *) convFor ((All ((D1, _), F1), t1),
                 (All ((D2, _), F2), t2)) =
          convDec ((D1, t1), (D2, t2))
          andalso convFor ((F1, dot1 t1), (F2, dot1 t2))
      | (* GEN CASE BRANCH *) convFor ((Ex ((D1, _), F1), t1),
                 (Ex ((D2, _), F2), t2)) =
          Conv.convDec ((D1, coerceSub t1), (D2, coerceSub t2))
          andalso convFor ((F1, dot1 t1), (F2, dot1 t2))
      | (* GEN CASE BRANCH *) convFor ((And (F1, F1'), t1), (And (F2, F2'), t2)) =
          convFor ((F1, t1), (F2, t2))
          andalso convFor ((F1', t1), (F2', t2))
      | (* GEN CASE BRANCH *) convFor _ = false
    and convDec ((UDec D1, t1), (UDec D2, t2)) =
          Conv.convDec ((D1, coerceSub t1), (D2, coerceSub t2))
      | (* GEN CASE BRANCH *) convDec ((PDec (_, F1, TC1, TC1'), t1), (PDec (_, F2, TC2, TC2'), t2)) =
          (convFor ((F1, t1), (F2, t2));
           convTCOpt (TC1, TC1');
           convTCOpt (TC2, TC2'))


  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)
  fun newEVar (Psi, F) = EVar(Psi, ref NONE, F, NONE, NONE, I.newEVar (coerceCtx Psi, I.Uni I.Type))
  fun newEVarTC (Psi, F, TC, TC') = EVar (Psi, ref NONE, F, TC, TC', I.newEVar (coerceCtx Psi, I.Uni I.Type))

  fun exists (x, []) = false
    | (* GEN CASE BRANCH *) exists (x, y :: W2) = (x = y) orelse exists (x, W2)

  fun subset ([], _) = true
    | (* GEN CASE BRANCH *) subset (x :: W1, W2) = exists (x, W2) andalso subset (W1, W2)

  fun eqWorlds (Worlds W1, Worlds W2) =
      subset (W1, W2) andalso subset (W2, W1)


  (* ctxDec (G, k) = x:V
     Invariant:
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)
    fun ctxDec (G, k) =
      let (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
        fun ctxDec' (I.Decl (G', UDec (I.Dec(x, V'))), 1) = UDec (I.Dec(x, I.EClo (V', I.Shift (k))))
          | (* GEN CASE BRANCH *) ctxDec' (I.Decl (G', UDec (I.BDec (l, (c, s)))), 1) = UDec (I.BDec (l, (c, I.comp (s, I.Shift (k)))))
          | (* GEN CASE BRANCH *) ctxDec' (I.Decl (G', PDec (x, F, TC1, TC2)), 1) =
              PDec(x, forSub (F, Shift(k)),  TCSubOpt (TC1, I.Shift k), TCSubOpt (TC2, I.Shift k))
          | (* GEN CASE BRANCH *) ctxDec' (I.Decl (G', _), k') = ctxDec' (G', k'-1)
         (* ctxDec' (Null, k')  should not occur by invariant *)
      in
        ctxDec' (G, k)
      end


     (* mkInst (n) = iota

        Invariant:
        iota = n.n-1....1
     *)
    fun mkInst (0) = nil
      | (* GEN CASE BRANCH *) mkInst (n) = I.Root (I.BVar (n), I.Nil) :: mkInst (n-1)


    (* deblockify G = (G', t')

       Invariant:
       If   |- G ctx
       then G' |- t' : G
    *)
    fun deblockify  (I.Null) = (I.Null, id)
      | (* GEN CASE BRANCH *) deblockify  (I.Decl (G, I.BDec (x, (c, s)))) =
        let
          val (G', t') = deblockify  G
                                        (* G' |- t' : G *)
          val (_, L) = I.constBlock c
          val n = List.length L
          val G'' = append (G', (L, I.comp (s, coerceSub t')))
                                        (* G'' = G', V1 ... Vn *)
          val t'' = comp (t', Shift n)
                                        (* G'' |- t'' : G *)
          val I = I.Inst (mkInst n)
                                        (* I = (n, n-1 ... 1)  *)
          val t''' = Dot (Block I, t'')
                                        (* G'' |- t''' : G, x:(c,s) *)
        in
          (G'', t''')
        end
    and append (G', (nil, s)) = G'
      | (* GEN CASE BRANCH *) append (G', (D :: L, s)) =
          append (I.Decl (G', I.decSub (D, s)), (L, I.dot1 s))


    (* whnfFor (F, t) = (F', t')

       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- t' : Psi''
       and   Psi'' |- F' :for
       and   Psi' |- F'[t'] = F[t] for
    *)
    fun whnfFor (Ft as (All (D, _), t)) = Ft
      | (* GEN CASE BRANCH *) whnfFor (Ft as (Ex (D, F), t)) = Ft
      | (* GEN CASE BRANCH *) whnfFor (Ft as (And (F1, F2), t)) = Ft
      | (* GEN CASE BRANCH *) whnfFor (FClo (F, t1), t2) =
          whnfFor (F, comp (t1, t2))
      | (* GEN CASE BRANCH *) whnfFor (Ft as (World (W, F), t)) = Ft
      | (* GEN CASE BRANCH *) whnfFor (Ft as (True, _)) = Ft



    (* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- V :: F
       and  Psi' |- V value
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)

    fun normalizePrg (Var n, t) =
        (case varSub (n, t)
           of (Prg P) => P
           | (Idx _) => raise Domain
           | (Exp _) => raise Domain
           | (Block _) => raise Domain
           | (Undef) => raise Domain
             )
      |  (* GEN CASE BRANCH *) normalizePrg (PairExp (U, P'), t) =
          PairExp (Whnf.normalize (U, coerceSub t), normalizePrg (P', t))
      | (* GEN CASE BRANCH *) normalizePrg (PairBlock (B, P'), t) =
          PairBlock (I.blockSub (B, coerceSub t), normalizePrg (P', t))
      | (* GEN CASE BRANCH *) normalizePrg (PairPrg (P1, P2), t) =
          PairPrg (normalizePrg (P1, t), normalizePrg (P2, t))
      | (* GEN CASE BRANCH *) normalizePrg (Unit, _) = Unit
      | (* GEN CASE BRANCH *) normalizePrg (EVar (_, ref (SOME P), _, _, _, _), t) = PClo(P, t)
      | (* GEN CASE BRANCH *) normalizePrg (P as EVar _, t) = PClo(P,t)
      | (* GEN CASE BRANCH *) normalizePrg (Lam (D, P), t) = Lam (normalizeDec (D, t), normalizePrg (P, dot1 t))
      | (* GEN CASE BRANCH *) normalizePrg (Rec (D, P), t) = Rec (normalizeDec (D, t), normalizePrg (P, dot1 t))
      | (* GEN CASE BRANCH *) normalizePrg (PClo (P, t), t') = normalizePrg (P, comp (t, t'))

    and normalizeSpine (Nil, t) = Nil
      | (* GEN CASE BRANCH *) normalizeSpine (AppExp (U, S), t) =
         AppExp (Whnf.normalize (U, coerceSub t), normalizeSpine (S, t))
      | (* GEN CASE BRANCH *) normalizeSpine (AppPrg (P, S), t) =
          AppPrg (normalizePrg (P, t), normalizeSpine (S, t))
      | (* GEN CASE BRANCH *) normalizeSpine (AppBlock (B, S), t) =
          AppBlock (I.blockSub (B, coerceSub t), normalizeSpine (S, t))
      | (* GEN CASE BRANCH *) normalizeSpine (SClo (S, t1), t2) =
          normalizeSpine (S, comp (t1, t2))

    and normalizeDec (PDec (name, F, TC1, NONE), t) =
          PDec (name, forSub (F, t), normalizeTCOpt (TCSubOpt (TC1, coerceSub t)), NONE)
      | (* GEN CASE BRANCH *) normalizeDec (UDec D, t) = UDec (Whnf.normalizeDec (D, coerceSub t))

    fun normalizeSub (s as Shift n) = s
      | (* GEN CASE BRANCH *) normalizeSub (Dot (Prg P, s)) =
          Dot (Prg (normalizePrg (P, id)), normalizeSub s)
      | (* GEN CASE BRANCH *) normalizeSub (Dot (Exp E, s)) =
          Dot (Exp (Whnf.normalize (E, I.id)), normalizeSub s)
      | (* GEN CASE BRANCH *) normalizeSub (Dot (Block k, s)) =
          Dot (Block k, normalizeSub s)
      | (* GEN CASE BRANCH *) normalizeSub (Dot (Idx k, s)) =
          Dot (Idx k, normalizeSub s)

    (* derefPrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- V :: F
       and  Psi' |- V value
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)
    fun derefPrg (Var n) = Var n
      | (* GEN CASE BRANCH *) derefPrg (PairExp (U, P')) =
          PairExp (U, derefPrg P')
      | (* GEN CASE BRANCH *) derefPrg (PairBlock (B, P')) =
          PairBlock (B, derefPrg P')
      | (* GEN CASE BRANCH *) derefPrg (PairPrg (P1, P2)) =
          PairPrg (derefPrg (P1), derefPrg (P2))
      | (* GEN CASE BRANCH *) derefPrg (Unit) = Unit
      | (* GEN CASE BRANCH *) derefPrg (EVar (_, ref (SOME P), _, _, _, _)) = P
      | (* GEN CASE BRANCH *) derefPrg (P as EVar _) = P
      | (* GEN CASE BRANCH *) derefPrg (Lam (D, P)) = Lam (derefDec D, derefPrg P)
      | (* GEN CASE BRANCH *) derefPrg (Rec (D, P)) = Rec (derefDec D, derefPrg P)
      | (* GEN CASE BRANCH *) derefPrg (Redex (P, S)) = Redex (derefPrg P, derefSpine S)
      | (* GEN CASE BRANCH *) derefPrg (Case (Cases Cs)) =
          Case (Cases (flattenCases (map (fn (Psi, s, P) => (Psi, s, derefPrg P)) Cs)))
      | (* GEN CASE BRANCH *) derefPrg (Let (D, P1, P2)) = Let (derefDec D, derefPrg P1, derefPrg P2)
      | (* GEN CASE BRANCH *) derefPrg (LetPairExp (D1, D2, P1, P2)) = LetPairExp (D1, derefDec D2, derefPrg P1, derefPrg P2)
      | (* GEN CASE BRANCH *) derefPrg (LetUnit (P1, P2)) = LetUnit (derefPrg P1, derefPrg P2)


    and flattenCases ((Psi, s, Case (Cases L)) :: Cs) =
           map (fn (Psi', s', P') => (Psi', comp (s, s'), P')) (flattenCases L)
           @ flattenCases Cs
      | (* GEN CASE BRANCH *) flattenCases ((Psi, s, P) :: Cs)  = (Psi, s, P) :: flattenCases Cs
      | (* GEN CASE BRANCH *) flattenCases nil = nil

    and derefSpine Nil = Nil
      | (* GEN CASE BRANCH *) derefSpine (AppExp (U, S)) =
         AppExp (U, derefSpine S)
      | (* GEN CASE BRANCH *) derefSpine (AppPrg (P, S)) =
          AppPrg (derefPrg (P), derefSpine (S))
      | (* GEN CASE BRANCH *) derefSpine (AppBlock (B, S)) =
          AppBlock (B, derefSpine (S))

    and derefDec (PDec (name, F, TC1, TC2)) = PDec (name, F, TC1, TC2)
      | (* GEN CASE BRANCH *) derefDec (UDec D) = UDec D

  in
    val lemmaLookup = lemmaLookup
    val lemmaAdd = lemmaAdd
    val lemmaSize = lemmaSize
    val lemmaDef = lemmaDef
    val lemmaName = lemmaName
    val lemmaFor = lemmaFor

    val coerceSub = coerceSub
    val coerceCtx = coerceCtx
    val strengthenCtx = strengthenCtx
    val embedCtx = embedCtx
    val id = id
    val shift = shift
    val comp = comp
    val dot1 = dot1
    val varSub = varSub
    val decSub = decSub
    val weakenSub = weakenSub
    val invertSub = invertSub
    val ctxDec = ctxDec
    val forSub = forSub
    val whnfFor = whnfFor
    val normalizePrg = normalizePrg
    val normalizeSub = normalizeSub
    val derefPrg = derefPrg

    val id = id
    val dotEta = dotEta
    val convFor = convFor
    val newEVar = newEVar
    val newEVarTC = newEVarTC

(* Below are added by Yu Liao *)
    val embedSub = embedSub
    val eqWorlds = eqWorlds
    val ctxDec = ctxDec
    val revCoerceSub = revCoerceSub
    val revCoerceCtx = revCoerceCtx

(* Added referenced by ABP *)
    val coerceFront = coerceFront
    val revCoerceFront = revCoerceFront
    val deblockify = deblockify

(* Stuff that has to do with termination conditions *)
  val TCSub = TCSub
  val normalizeTC  = normalizeTC
  val convTC = convTC
  val transformTC = transformTC


  end
end;  (* functor FunSyn *)
