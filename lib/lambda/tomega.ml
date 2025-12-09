(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao, Adam Poswolsky *)

module Tomega (Whnf : WHNF)
   (Conv : CONV) : TOMEGA =
struct
  exception Error of string

  type label = int
  type lemma = int

  type worlds = Worlds of IntSyn.cid list

  type quantifier = Implicit | Explicit

  type tC   =                       (* Terminiation Condition     *)
    Abs of IntSyn.Dec * tC              (* T ::= {{D}} O              *)
  | Conj of tC * tC                     (*     | O1 ^ O2              *)
  | Base of ((IntSyn.exp * IntSyn.Sub) *
             (IntSyn.exp * IntSyn.Sub)) Order.Order

  type for                          (* Formulas                   *)
  = World of worlds * for               (* F ::= World l1...ln. F     *)
  | All of (Dec * quantifier) * for     (*     | All LD. F            *)
  | Ex  of (IntSyn.Dec * quantifier) * for
                                        (*     | Ex  D. F             *)
  | True                                (*     | T                    *)
  | And of for * for                    (*     | F1 ^ F2              *)
  | FClo of for * Sub                   (*     | F [t]                *)
  | FVar of (Dec IntSyn.ctx * For option ref)
                                        (*     | F (G)                *)

  and Dec =                             (* Declaration:               *)
    UDec of IntSyn.Dec                  (* D ::= x:A                  *)
  | PDec of string option * For * TC option * TC option
                                        (*     | xx :: F              *)

  and Prg =                             (* Programs:                  *)
    Box of Worlds * Prg                 (*     | box W. P             *)
  | Lam of Dec * Prg                    (*     | lam LD. P            *)
  | New of Prg                          (*     | new P                *)
  | Choose of Prg                       (*     | choose P             *)
  | PairExp of IntSyn.exp * Prg         (*     | <M, P>               *)
  | PairBlock of IntSyn.Block * Prg     (*     | <rho, P>             *)
  | PairPrg of Prg * Prg                (*     | <P1, P2>             *)
  | Unit                                (*     | <>                   *)
  | Redex of Prg * Spine
  | Rec of Dec * Prg                    (*     | mu xx. P             *)
  | Case of Cases                       (*     | case t of O          *)
  | PClo of Prg * Sub                   (*     | P [t]                *)
  | Let of Dec * Prg * Prg              (*     | let D = P1 in P2     *)
  | EVar of Dec IntSyn.ctx * Prg option ref * For * TC option * TC option * IntSyn.exp
                                        (*     | E (G, F, TC)         *)
  | Const of lemma                      (* P ::= cc                   *)
  | Var of int                          (*     | xx                   *)
  | LetPairExp of IntSyn.Dec * Dec * Prg * Prg
  | LetUnit of Prg * Prg

  and Spine =                           (* Spines:                    *)
    Nil                                 (* S ::= Nil                  *)
  | AppExp of IntSyn.exp * Spine        (*     | P U                  *)
  | AppBlock of IntSyn.Block * Spine    (*     | P rho                *)
  | AppPrg of Prg * Spine               (*     | P1 P2                *)
  | SClo of Spine * Sub                 (*     | S [t]                *)

  and Sub =                             (* t ::=                      *)
    Shift of int                        (*       ^n                   *)
  | Dot of Front * Sub                  (*     | F . t                *)

  and Front =                           (* F ::=                      *)
    Idx of int                          (*     | i                    *)
  | Prg of Prg                          (*     | p                    *)
  | Exp of IntSyn.exp                   (*     | U                    *)
  | Block of IntSyn.Block               (*     | _x                   *)
  | Undef                               (*     | _                    *)

  and Cases =                           (* Cases                      *)
    Cases of (Dec IntSyn.ctx * Sub * Prg) list
                                        (* C ::= (Psi' |> s |-> P)    *)

  type conDec =                     (* ConDec                     *)
    ForDec of string * For              (* CD ::= f :: F              *)
  | ValDec of string * Prg * For        (*      | f == P              *)

  exception NoMatch

  local
    module I = IntSyn
    module O = Order

    let maxLemma = Global.maxCid
    let lemmaArray = Array.array (maxLemma+1, ForDec ("", True))
                   : ConDec Array.array
    let nextLemma = ref 0

    fun lemmaLookup lemma = Array.sub (lemmaArray, lemma)
    fun lemmaAdd (lemmaDec) =
        let
          let lemma = !nextLemma
        in
          if lemma > maxLemma
            then raise Error ("Global module type size " ^ Int.toString (maxLemma+1) ^ " exceeded")
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
      | lemmaName' n s =
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
    let rec coerceFront = function (Idx k) -> I.Idx k
      | (Prg P) -> I.Undef
      | (Exp M) -> I.Exp M
      | (Block B) -> I.Block B
      | (Undef) -> I.Undef
    (* --Yu Liao Why cases: Block, Undef aren't defined *)

    (* embedFront F = F'

       Invariant:
       If    Psi |- F front
       and   G = mu G. G \in Psi
       then  G   |- F' front
    *)
    let rec embedFront = function (I.Idx k) -> Idx k
      | (I.Exp U) -> Exp U
      | (I.Block B) -> Block B
      | (I.Undef) -> Undef


    (* coerceSub t = s

       Invariant:
       If    Psi |- t : Psi'
       then  G   |- s : G'
       where G = mu G. G \in Psi
       and   G' = mu G. G \in Psi'
    *)
    let rec coerceSub = function (Shift n) -> I.Shift n
      | (Dot (Ft, t)) -> 
          I.Dot (coerceFront Ft, coerceSub t)

    let rec embedSub = function (I.Shift n) -> Shift n
      | (I.Dot (Ft, s)) -> 
          Dot (embedFront Ft, embedSub s)


    (* Definition:
       |- Psi ctx[block] holds iff Psi = _x_1 : (L1, t1), ... _x_n : (Ln, tn)
    *)

    let rec revCoerceFront = function (I.Idx k) -> Idx k
      | (I.Exp M) -> Exp M
      | (I.Block b) -> Block b
      | I.Undef -> Undef


    (* revCoerceSub t = s
    coerce substitution in LF level t ==> s in Tomega level *)
    let rec revCoerceSub = function (I.Shift n) -> Shift n
      | (I.Dot (Ft, t)) -> Dot(revCoerceFront Ft, revCoerceSub t)


    (* Invariant Yu? *)
    let rec revCoerceCtx = function I.Null -> I.Null
      | (I.Decl (Psi, D as I.BDec (_, (L, t)))) -> 
          I.Decl (revCoerceCtx (Psi), UDec D)



    let id = Shift 0

    (* dotEta (Ft, s) = s'

       Invariant:
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)
    let rec dotEta = function (Ft as Idx _, s) -> Dot (Ft, s)
      | (Ft as Exp (U), s) -> 
        let
          let Ft' = Idx (Whnf.etaContract U)
                   handle Eta => Ft
        in
          Dot (Ft', s)
        end
      | (Ft as Undef, s) -> Dot (Ft, s)


    (* embedCtx G = Psi

       Invariant:
       If   G is an LF ctx
       then Psi is G, embedded into Tomega
    *)
    let rec embedCtx = function I.Null -> I.Null
      | (I.Decl (G, D)) -> 
          I.Decl (embedCtx G, UDec D)



      (* orderSub (O, s) = O'

         Invariant:
         If   G' |- O order    and    G |- s : G'
         then G |- O' order
         and  G |- O' == O[s] order
      *)
      fun orderSub (O.Arg ((U, s1), (V, s2)), s) =
            O.Arg ((U,  I.comp (s1, s)), (V, I.comp (s2, s)))
        | orderSub (O.Lex Os, s) = O.Lex (map (fun O -> orderSub (O, s)) Os)
        | orderSub (O.Simul Os, s) = O.Simul (map (fun O -> orderSub (O, s)) Os)

      fun TCSub (Base O, s) = Base (orderSub (O, s))
        | TCSub (Conj (TC1, TC2), s) = Conj (TCSub (TC1, s), TCSub (TC2, s))
        | TCSub (Abs (D, TC), s) = Abs (I.decSub (D, s), TCSub (TC, I.dot1 s))

      fun TCSubOpt (NONE, s) = NONE
        | TCSubOpt (SOME TC, s) = SOME (TCSub (TC, s))

      (* normalizeTC (O) = O'

         Invariant:
         If   G |- O TC
         then G |- O' TC
         and  G |- O = O' TC
         and  each sub term of O' is in normal form.
      *)
      fun normalizeTC' (O.Arg (Us, Vs)) =
            O.Arg ((Whnf.normalize Us, I.id), (Whnf.normalize Vs, I.id))
        | normalizeTC' (O.Lex Os) = O.Lex (map normalizeTC' Os)
        | normalizeTC' (O.Simul Os) = O.Simul (map normalizeTC' Os)

      fun normalizeTC (Base  O) = Base (normalizeTC' O)
        | normalizeTC (Conj (TC1, TC2)) = Conj (normalizeTC TC1, normalizeTC TC2)
        | normalizeTC (Abs (D, TC)) = Abs (Whnf.normalizeDec (D, I.id), normalizeTC TC)

      fun normalizeTCOpt (NONE) = NONE
        | normalizeTCOpt (SOME TC) = SOME (normalizeTC TC)

      (* convTC (O1, O2) = B'

         Invariant:
         If   G |- O1 TC
         and  G |- O2 TC
         then B' holds iff G |- O1 == O2 TC
      *)
      fun convTC' (O.Arg (Us1, _), O.Arg (Us2, _ )) = Conv.conv (Us1, Us2)
        | convTC' (O.Lex Os1, O.Lex Os2) = convTCs (Os1, Os2)
        | convTC' (O.Simul Os1, O.Simul Os2) = convTCs (Os1, Os2)
      and convTCs (nil, nil) = true
        | convTCs (O1 :: L1, O2 :: L2) =
            convTC' (O1, O2) andalso convTCs (L1, L2)

      fun convTC (Base  O, Base O') =  convTC' (O, O')
        | convTC (Conj (TC1, TC2), Conj (TC1', TC2')) = convTC (TC1, TC1')
                     andalso convTC (TC2, TC2')
        | convTC (Abs (D, TC), Abs (D', TC')) = Conv.convDec ((D, I.id), (D', I.id)) andalso
                     convTC (TC, TC')
        | convTC _ = false

      fun convTCOpt (NONE, NONE) = true
        | convTCOpt (SOME TC1, SOME TC2) = convTC (TC1, TC2)
        | convTCOpt _ = false

    let rec transformTC' = function (G, O.Arg k) -> 
        let
          let k' = (I.ctxLength G) -k+1
          let I.Dec (_, V) = I.ctxDec (G, k')
        in
          O.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
        end
      | (G, O.Lex Os) -> 
          O.Lex (map (fun O -> transformTC' (G, O)) Os)
      | (G, O.Simul Os) -> 
          O.Simul (map (fun O -> transformTC' (G, O)) Os)

    let rec transformTC = function (G, All ((UDec D, _), F), Os) -> 
          Abs (D, transformTC (I.Decl (G, D), F, Os))
      | (G, And (F1, F2), O :: Os) -> 
          Conj (transformTC (G, F1, [O]),
                 transformTC (G, F2, Os))
      | (G, Ex _, [O]) -> Base (transformTC' (G, O))





    (* bvarSub (n, t) = Ft'

       Invariant:
       If    Psi |- t : Psi'    Psi' |- n :: F
       then  Ft' = Ftn          if  t = Ft1 .. Ftn .. ^k
         or  Ft' = ^(n+k)       if  t = Ft1 .. Ftm ^k   and m<n
       and   Psi |- Ft' :: F [t]
    *)
    let rec varSub = function (1, Dot(Ft, t)) -> Ft
      | (n, Dot(Ft, t)) -> varSub (n-1, t)
      | (n, Shift(k)) -> Idx (n+k)




    (* frontSub (Ft, t) = Ft'

       Invariant:
       If   Psi |- Ft :: F
       and  Psi' |- t :: Psi
       then Ft' = Ft[t]
       and  Psi' |- Ft' :: F[t]
    *)
    and frontSub (Idx (n), t) = varSub (n, t)
      | frontSub (Exp (U), t) = Exp (I.EClo (U, coerceSub t))
      | frontSub (Prg (P), t) = Prg (PClo (P, t))
      | frontSub (Block B, t) = Block (I.blockSub (B, coerceSub t))
     (* Block case is missing --cs *)


    (* comp (t1, t2) = t

       Invariant:
       If   Psi'' |- t2 :: Psi'
       and  Psi' |- t1 :: Psi
       then t = t1 o t2
       and  Psi'' |- t1 o t2 :: Psi'
    *)
    and comp (Shift (0), t) = t
      | comp (t, Shift (0)) = t
      | comp (Shift (n), Dot (Ft, t)) = comp (Shift (n-1), t)
      | comp (Shift (n), Shift (m)) = Shift (n+m)
      | comp (Dot (Ft, t), t') = Dot (frontSub (Ft, t'), comp (t, t'))




    (* dot1 (t) = t'

       Invariant:
       If   G |- t : G'
       then t' = 1. (t o ^)
       and  for all V t.t.  G' |- V : L
            G, V[t] |- t' : G', V

       If t patsub then t' patsub
    *)
    let rec dot1 = function (t as Shift (0)) -> t
      | t -> Dot (Idx(1), comp(t, Shift 1))

    let id = Shift 0
    let shift = Shift 1

    (* weakenSub (Psi) = w

       Invariant:
       If   Psi is a context
       then G is embed Psi
       and  Psi |- w : G
    *)
    let rec weakenSub = function (I.Null) -> id
      | (I.Decl (Psi, D as UDec _)) -> 
          dot1 (weakenSub Psi)
      | (I.Decl (Psi, D as PDec _)) -> 
          comp (weakenSub Psi, shift)


    (* forSub (F, t) = F'

       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- F' = F[t] for
    *)
    let rec forSub = function (All ((D, Q), F), t) -> 
          All ((decSub (D, t), Q),
                 forSub (F, dot1 t))
      | (Ex ((D, Q), F), t) -> 
          Ex ((I.decSub (D, coerceSub t), Q),
                 forSub (F, dot1 t))
      | (And (F1, F2), t) -> 
          And (forSub (F1, t),
                 forSub (F2, t))
      | (FClo (F, t1), t2) -> 
          forSub (F, comp (t1, t2))
      | (World (W, F), t) -> 
          World (W, forSub (F, t))
      | (True, _) -> True



    (* decSub (x::F, t) = D'

       Invariant:
       If   Psi  |- t : Psi'    Psi' |- F formula
       then D' = x:F[t]
       and  Psi  |- F[t] formula
    *)
    and decSub (PDec (x, F, TC1, NONE), t) =
        let
          let s = coerceSub t
        in
          PDec (x, forSub (F, t), TCSubOpt (TC1, s), NONE)
        end
      | decSub (UDec D, t) = UDec (I.decSub (D, coerceSub t))


    (* invertSub s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)
    fun invertSub s =
      let
        (* returns NONE if not found *)
        let rec getFrontIndex = function (Idx k) -> SOME(k)
          | (Prg P) -> getPrgIndex(P)
          | (Exp U) -> getExpIndex(U)
          | (Block B) -> getBlockIndex(B)
          | (Undef) -> NONE


        (* getPrgIndex returns NONE if it is not an index *)
        and getPrgIndex (Redex (Var k, Nil )) = SOME(k)
          | getPrgIndex (Redex (P, Nil)) = getPrgIndex(P)

          (* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
          | getPrgIndex (PClo (P,t)) =
               (case getPrgIndex(P) of
                  NONE => NONE
                | SOME i => getFrontIndex (varSub (i, t)))
          | getPrgIndex _ = NONE

        (* getExpIndex returns NONE if it is not an index *)
        and getExpIndex (I.Root (I.BVar k, I.Nil)) = SOME(k)
          | getExpIndex (I.Redex (U, I.Nil)) = getExpIndex(U)
          | getExpIndex (I.EClo (U, t)) =
               (case getExpIndex(U) of
                  NONE => NONE
                | SOME i => getFrontIndex (revCoerceFront(I.bvarSub(i, t))))

          | getExpIndex (U as I.Lam (I.Dec (_, U1), U2)) = (SOME ( Whnf.etaContract(U) )  handle Whnf.Eta => NONE)
          | getExpIndex _ = NONE

        (* getBlockIndex returns NONE if it is not an index *)
        and getBlockIndex (I.Bidx k) = SOME(k)
          | getBlockIndex _ = NONE


        let rec lookup = function (n, Shift _, p) -> NONE
          | (n, Dot (Undef, s'), p) -> lookup (n+1, s', p)
          | (n, Dot (Idx k, s'), p) -> 
            if k = p then SOME n
            else lookup (n+1, s', p)

        (* Suggested by ABP
         * If you do not want this, remove the getFrontIndex and other
          | (n, Dot (Ft, s'), p) -> 
              (case getFrontIndex(Ft) of
                 NONE => lookup (n+1, s', p)
               | SOME k => if (k=p) then SOME n else lookup (n+1, s', p))
        *)

        let rec invertSub'' = function (0, si) -> si
          | (p, si) -> 
            (case (lookup (1, s, p))
               of SOME k => invertSub'' (p-1, Dot (Idx k, si))
                | NONE => invertSub'' (p-1, Dot (Undef, si)))

        let rec invertSub' = function (n, Shift p) -> invertSub'' (p, Shift n)
          | (n, Dot (_, s')) -> invertSub' (n+1, s')
      in
        invertSub' (0, s)
      end


    (* coerceCtx (Psi) = G

       Invariant:
       If   |- Psi ctx[block]
       then |- G lf-ctx[block]
       and  |- Psi == G
    *)
    let rec coerceCtx = function I.Null -> I.Null
      | (I.Decl (Psi, UDec D)) -> 
          I.Decl (coerceCtx Psi, D)
      | (I.Decl (Psi, PDec (x, _, _, _))) -> 
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
          let w = weakenSub Psi
          let s = invertSub w
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

    let rec convFor = function ((True, _), (True, _)) -> true
      | convFor ((All ((D1, _), F1), t1),
                 (All ((D2, _), F2), t2)) =
          convDec ((D1, t1), (D2, t2))
          andalso convFor ((F1, dot1 t1), (F2, dot1 t2))
      | convFor ((Ex ((D1, _), F1), t1),
                 (Ex ((D2, _), F2), t2)) =
          Conv.convDec ((D1, coerceSub t1), (D2, coerceSub t2))
          andalso convFor ((F1, dot1 t1), (F2, dot1 t2))
      | ((And (F1, F1'), t1), (And (F2, F2'), t2)) -> 
          convFor ((F1, t1), (F2, t2))
          andalso convFor ((F1', t1), (F2', t2))
      | _ -> false
    and convDec ((UDec D1, t1), (UDec D2, t2)) =
          Conv.convDec ((D1, coerceSub t1), (D2, coerceSub t2))
      | convDec ((PDec (_, F1, TC1, TC1'), t1), (PDec (_, F2, TC2, TC2'), t2)) =
          (convFor ((F1, t1), (F2, t2));
           convTCOpt (TC1, TC1');
           convTCOpt (TC2, TC2'))


  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)
  fun newEVar (Psi, F) = EVar(Psi, ref NONE, F, NONE, NONE, I.newEVar (coerceCtx Psi, I.Uni I.Type))
  fun newEVarTC (Psi, F, TC, TC') = EVar (Psi, ref NONE, F, TC, TC', I.newEVar (coerceCtx Psi, I.Uni I.Type))

  let rec exists = function (x, []) -> false
    | (x, y :: W2) -> (x = y) orelse exists (x, W2)

  let rec subset = function ([], _) -> true
    | (x :: W1, W2) -> exists (x, W2) andalso subset (W1, W2)

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
        let rec ctxDec' = function (I.Decl (G', UDec (I.Dec(x, V'))), 1) -> UDec (I.Dec(x, I.EClo (V', I.Shift (k))))
          | (I.Decl (G', UDec (I.BDec (l, (c, s)))), 1) -> UDec (I.BDec (l, (c, I.comp (s, I.Shift (k)))))
          | (I.Decl (G', PDec (x, F, TC1, TC2)), 1) -> 
              PDec(x, forSub (F, Shift(k)),  TCSubOpt (TC1, I.Shift k), TCSubOpt (TC2, I.Shift k))
          | (I.Decl (G', _), k') -> ctxDec' (G', k'-1)
         (* ctxDec' (Null, k')  should not occur by invariant *)
      in
        ctxDec' (G, k)
      end


     (* mkInst (n) = iota

        Invariant:
        iota = n.n-1....1
     *)
    let rec mkInst = function (0) -> nil
      | (n) -> I.Root (I.BVar (n), I.Nil) :: mkInst (n-1)


    (* deblockify G = (G', t')

       Invariant:
       If   |- G ctx
       then G' |- t' : G
    *)
    let rec deblockify = function (I.Null) -> (I.Null, id)
      | (I.Decl (G, I.BDec (x, (c, s)))) -> 
        let
          let (G', t') = deblockify  G
                                        (* G' |- t' : G *)
          let (_, L) = I.constBlock c
          let n = List.length L
          let G'' = append (G', (L, I.comp (s, coerceSub t')))
                                        (* G'' = G', V1 ... Vn *)
          let t'' = comp (t', Shift n)
                                        (* G'' |- t'' : G *)
          let I = I.Inst (mkInst n)
                                        (* I = (n, n-1 ... 1)  *)
          let t''' = Dot (Block I, t'')
                                        (* G'' |- t''' : G, x:(c,s) *)
        in
          (G'', t''')
        end
    and append (G', (nil, s)) = G'
      | append (G', (D :: L, s)) =
          append (I.Decl (G', I.decSub (D, s)), (L, I.dot1 s))


    (* whnfFor (F, t) = (F', t')

       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- t' : Psi''
       and   Psi'' |- F' :for
       and   Psi' |- F'[t'] = F[t] for
    *)
    let rec whnfFor = function (Ft as (All (D, _), t)) -> Ft
      | (Ft as (Ex (D, F), t)) -> Ft
      | (Ft as (And (F1, F2), t)) -> Ft
      | (FClo (F, t1), t2) -> 
          whnfFor (F, comp (t1, t2))
      | (Ft as (World (W, F), t)) -> Ft
      | (Ft as (True, _)) -> Ft



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

    let rec normalizePrg = function (Var n, t) -> 
        (case varSub (n, t)
           of (Prg P) => P
           | (Idx _) => raise Domain
           | (Exp _) => raise Domain
           | (Block _) => raise Domain
           | (Undef) => raise Domain
             )
      | (PairExp (U, P'), t) -> 
          PairExp (Whnf.normalize (U, coerceSub t), normalizePrg (P', t))
      | (PairBlock (B, P'), t) -> 
          PairBlock (I.blockSub (B, coerceSub t), normalizePrg (P', t))
      | (PairPrg (P1, P2), t) -> 
          PairPrg (normalizePrg (P1, t), normalizePrg (P2, t))
      | (Unit, _) -> Unit
      | (EVar (_, ref (SOME P), _, _, _, _), t) -> PClo(P, t)
      | (P as EVar _, t) -> PClo(P,t)
      | (Lam (D, P), t) -> Lam (normalizeDec (D, t), normalizePrg (P, dot1 t))
      | (Rec (D, P), t) -> Rec (normalizeDec (D, t), normalizePrg (P, dot1 t))
      | (PClo (P, t), t') -> normalizePrg (P, comp (t, t'))

    and normalizeSpine (Nil, t) = Nil
      | normalizeSpine (AppExp (U, S), t) =
         AppExp (Whnf.normalize (U, coerceSub t), normalizeSpine (S, t))
      | normalizeSpine (AppPrg (P, S), t) =
          AppPrg (normalizePrg (P, t), normalizeSpine (S, t))
      | normalizeSpine (AppBlock (B, S), t) =
          AppBlock (I.blockSub (B, coerceSub t), normalizeSpine (S, t))
      | normalizeSpine (SClo (S, t1), t2) =
          normalizeSpine (S, comp (t1, t2))

    and normalizeDec (PDec (name, F, TC1, NONE), t) =
          PDec (name, forSub (F, t), normalizeTCOpt (TCSubOpt (TC1, coerceSub t)), NONE)
      | normalizeDec (UDec D, t) = UDec (Whnf.normalizeDec (D, coerceSub t))

    let rec normalizeSub = function (s as Shift n) -> s
      | (Dot (Prg P, s)) -> 
          Dot (Prg (normalizePrg (P, id)), normalizeSub s)
      | (Dot (Exp E, s)) -> 
          Dot (Exp (Whnf.normalize (E, I.id)), normalizeSub s)
      | (Dot (Block k, s)) -> 
          Dot (Block k, normalizeSub s)
      | (Dot (Idx k, s)) -> 
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
    let rec derefPrg = function (Var n) -> Var n
      | (PairExp (U, P')) -> 
          PairExp (U, derefPrg P')
      | (PairBlock (B, P')) -> 
          PairBlock (B, derefPrg P')
      | (PairPrg (P1, P2)) -> 
          PairPrg (derefPrg (P1), derefPrg (P2))
      | (Unit) -> Unit
      | (EVar (_, ref (SOME P), _, _, _, _)) -> P
      | (P as EVar _) -> P
      | (Lam (D, P)) -> Lam (derefDec D, derefPrg P)
      | (Rec (D, P)) -> Rec (derefDec D, derefPrg P)
      | (Redex (P, S)) -> Redex (derefPrg P, derefSpine S)
      | (Case (Cases Cs)) -> 
          Case (Cases (flattenCases (map (fn (Psi, s, P) => (Psi, s, derefPrg P)) Cs)))
      | (Let (D, P1, P2)) -> Let (derefDec D, derefPrg P1, derefPrg P2)
      | (LetPairExp (D1, D2, P1, P2)) -> LetPairExp (D1, derefDec D2, derefPrg P1, derefPrg P2)
      | (LetUnit (P1, P2)) -> LetUnit (derefPrg P1, derefPrg P2)


    and flattenCases ((Psi, s, Case (Cases L)) :: Cs) =
           map (fn (Psi', s', P') => (Psi', comp (s, s'), P')) (flattenCases L)
           @ flattenCases Cs
      | flattenCases ((Psi, s, P) :: Cs)  = (Psi, s, P) :: flattenCases Cs
      | flattenCases nil = nil

    and derefSpine Nil = Nil
      | derefSpine (AppExp (U, S)) =
         AppExp (U, derefSpine S)
      | derefSpine (AppPrg (P, S)) =
          AppPrg (derefPrg (P), derefSpine (S))
      | derefSpine (AppBlock (B, S)) =
          AppBlock (B, derefSpine (S))

    and derefDec (PDec (name, F, TC1, TC2)) = PDec (name, F, TC1, TC2)
      | derefDec (UDec D) = UDec D

  in
    let lemmaLookup = lemmaLookup
    let lemmaAdd = lemmaAdd
    let lemmaSize = lemmaSize
    let lemmaDef = lemmaDef
    let lemmaName = lemmaName
    let lemmaFor = lemmaFor

    let coerceSub = coerceSub
    let coerceCtx = coerceCtx
    let strengthenCtx = strengthenCtx
    let embedCtx = embedCtx
    let id = id
    let shift = shift
    let comp = comp
    let dot1 = dot1
    let varSub = varSub
    let decSub = decSub
    let weakenSub = weakenSub
    let invertSub = invertSub
    let ctxDec = ctxDec
    let forSub = forSub
    let whnfFor = whnfFor
    let normalizePrg = normalizePrg
    let normalizeSub = normalizeSub
    let derefPrg = derefPrg

    let id = id
    let dotEta = dotEta
    let convFor = convFor
    let newEVar = newEVar
    let newEVarTC = newEVarTC

(* Below are added by Yu Liao *)
    let embedSub = embedSub
    let eqWorlds = eqWorlds
    let ctxDec = ctxDec
    let revCoerceSub = revCoerceSub
    let revCoerceCtx = revCoerceCtx

(* Added referenced by ABP *)
    let coerceFront = coerceFront
    let revCoerceFront = revCoerceFront
    let deblockify = deblockify

(* Stuff that has to do with termination conditions *)
  let TCSub = TCSub
  let normalizeTC  = normalizeTC
  let convTC = convTC
  let transformTC = transformTC


  end
end;; (* functor FunSyn *)
