(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Converter
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   structure ModeTable : MODETABLE
   (*! sharing ModeSyn.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure TomegaPrint : TOMEGAPRINT
   (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
   (*! sharing TomegaPrint.Tomega = Tomega' !*)
   structure WorldSyn : WORLDSYN
   (*! sharing WorldSyn.IntSyn = IntSyn' !*)
   (*! sharing WorldSyn.Tomega = Tomega' !*)
   structure Worldify : WORLDIFY
   (*! sharing Worldify.IntSyn = IntSyn' !*)
   (*! sharing Worldify.Tomega = Tomega' !*)
   structure TomegaTypeCheck : TOMEGATYPECHECK
   (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
   (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure Redundant : REDUNDANT
   structure TomegaAbstract :TOMEGAABSTRACT
       )
     : CONVERTER =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)

  exception Error of string

exception Error' of Tomega.sub

  local
    structure T = Tomega
    structure I = IntSyn
    structure M = ModeSyn
    structure S = Subordinate
    structure A = Abstract
    structure TA = TomegaAbstract

    (* ABP - 4/20/03, determine if Front is (I.Idx 1) *)
    fun (* GEN BEGIN FUN FIRST *) isIdx1 (I.Idx 1) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isIdx1 _ = false (* GEN END FUN BRANCH *)

    fun modeSpine a =
        case ModeTable.modeLookup a
          of NONE => raise Error "Mode declaration expected"
           | SOME mS => mS

    fun typeOf a =
        case I.sgnLookup a
          of I.ConDec (name, _, _, _, V, I.Kind) => V
           | _ => raise Error "Type Constant declaration expected"


    fun nameOf a =
        case I.sgnLookup a
          of I.ConDec (name, _, _, _, V, I.Kind) => name
           | _ => raise Error "Type Constant declaration expected"

    fun chatter chlev f =
        if !Global.chatter >= chlev
          then print ("[tomega] " ^ f ())
        else ()




    (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
    fun strengthenExp (U, s) = Whnf.normalize (Whnf.cloInv (U, s), I.id)

    fun strengthenSub (s, t) = Whnf.compInv (s, t)

    (* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenDec (I.Dec (name, V), s) = I.Dec (name, strengthenExp (V, s)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenDec (I.BDec (name, (L, t)), s) =
                                        (* G0 |- t : Gsome *)
                                        (* G0  |- s : G' *)
                                        (* to show  G' |- t o s^1 : Gsome *)
          I.BDec (name, (L, strengthenSub (t, s))) (* GEN END FUN BRANCH *)

    (* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- w : G1
       then G1 |- G' = G[w^-1] ctx
       and  G0 |- w' : G1, G'
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenCtx (I.Null, s) = (I.Null, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenCtx (I.Decl (G, D), s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', s') = strengthenCtx (G, s) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (G', strengthenDec (D, s')), I.dot1 s')
        end (* GEN END FUN BRANCH *)


    (* strengthenFor (F, s) = F'

       If   Psi0 |- F for
       and  Psi0 |- s :: Psi1
       then Psi1 |- F' = F[s^-1] ctx
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenFor (T.True, s) = T.True (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenFor (T.And (F1, F2), s) =
          T.And (strengthenFor (F1, s), strengthenFor (F2, s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strengthenFor (T.All ((T.UDec D, Q), F), s) =
          T.All ((T.UDec (strengthenDec (D, s)), Q), strengthenFor (F, I.dot1 s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strengthenFor (T.Ex ((D, Q), F), s) =
          T.Ex ((strengthenDec (D, s), Q), strengthenFor (F, I.dot1 s)) (* GEN END FUN BRANCH *)





    (* strengthenOrder (O, s) = O'

       If   Psi0 |- O order
       and  Psi0 |- s :: Psi1
       then Psi1 |- O' = O[s^-1] ctx
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenOrder (Order.Arg((U,s1), (V, s2)), s) =
          Order.Arg ((U, strengthenSub (s1, s)), (V, strengthenSub (s2, s))) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenOrder (Order.Simul Os, s) =
          Order.Simul (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => strengthenOrder (O, s) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strengthenOrder (Order.Lex Os, s) =
          Order.Lex (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => strengthenOrder (O, s) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)


    (* strengthenTC (TC, s) = TC'

       If   Psi0 |- TC : termination condition
       and  Psi0 |- s :: Psi1
       then Psi1 |- TC' = TC[s^-1] ctx
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenTC (T.Base O, s) = T.Base (strengthenOrder (O, s)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenTC (T.Conj (TC1, TC2), s) =
          T.Conj (strengthenTC (TC1, s), strengthenTC (TC2, s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strengthenTC (T.Abs (D, TC), s) =
          T.Abs (strengthenDec (D, s), strengthenTC (TC, I.dot1 s)) (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) strengthenSpine (I.Nil, t) = I.Nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenSpine (I.App (U, S), t) = I.App (strengthenExp (U, t), strengthenSpine (S, t)) (* GEN END FUN BRANCH *)



    (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s :: Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' :: Psi1, Psi'
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenPsi (I.Null, s) = (I.Null, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenPsi (I.Decl (Psi, T.UDec D), s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', s') = strengthenPsi (Psi, s) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (Psi', T.UDec (strengthenDec (D, s'))), I.dot1 s')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) strengthenPsi (I.Decl (Psi, T.PDec (name, F, NONE, NONE)), s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', s') = strengthenPsi (Psi, s) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (Psi', T.PDec (name, strengthenFor (F, s'), NONE, NONE)), I.dot1 s')
        end (* GEN END FUN BRANCH *)


    (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
    fun (* GEN BEGIN FUN FIRST *) strengthenPsi' (nil, s) = (nil, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) strengthenPsi' (T.UDec D :: Psi, s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D' = strengthenDec (D, s) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val s' = I.dot1 s (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi'', s'') = strengthenPsi' (Psi, s') (* GEN END TAG OUTSIDE LET *)
        in
          (T.UDec D' :: Psi'', s'')
        end (* GEN END FUN BRANCH *)

    (* ctxSub (G, s) = (G', s')

       Invariant:
       if   Psi |- G ctx
       and  Psi' |- s : Psi
       then Psi' |- G' ctx
       and  Psi', G' |- s' : G
       and  G' = G [s],  declarationwise defined
    *)
    fun (* GEN BEGIN FUN FIRST *) ctxSub (I.Null, s) = (I.Null, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxSub (I.Decl (G, D), s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', s') = ctxSub (G, s) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (G', I.decSub (D, s')), I.dot1 s)
        end (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) validMode (M.Mnil) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) validMode (M.Mapp (M.Marg (M.Plus, _), mS)) =
          validMode mS (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) validMode (M.Mapp (M.Marg (M.Minus, _), mS)) =
          validMode mS (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) validMode (M.Mapp (M.Marg (M.Star, _), mS)) =
          raise Error "+ or - mode expected, * found" (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) validSig (Psi0, nil) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) validSig (Psi0, (G, V) :: Sig) =
        let
          fun (* GEN BEGIN FUN FIRST *) append (G, I.Null) = G (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) append (G, I.Decl (G', D)) = I.Decl (append (G, G'), D) (* GEN END FUN BRANCH *)
      
        in
          (TypeCheck.typeCheck (T.coerceCtx (append (Psi0, T.embedCtx G)),
                                (V, I.Uni I.Type)); validSig (Psi0, Sig))
        end (* GEN END FUN BRANCH *)


    fun convertOneFor cid =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val V  = case I.sgnLookup cid
                   of I.ConDec (name, _, _, _, V, I.Kind) => V
                    | _ => raise Error "Type Constant declaration expected" (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val mS = case ModeTable.modeLookup cid
                   of NONE => raise Error "Mode declaration expected"
                    | SOME mS => mS (* GEN END TAG OUTSIDE LET *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = validMode mS (* GEN END TAG OUTSIDE LET *)
    
        (* convertFor' (V, mS, w1, w2, n) = (F', F'')
    
           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
        fun (* GEN BEGIN FUN FIRST *) convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (F', F'') = convertFor' (V, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n-1) (* GEN END TAG OUTSIDE LET *)
            in
              ((* GEN BEGIN FUNCTION EXPRESSION *) fn F => T.All ((T.UDec (strengthenDec (D, w1)), T.Explicit), F' F) (* GEN END FUNCTION EXPRESSION *), F'')
            end (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (F', F'') = convertFor' (V, mS, I.comp (w1, I.shift), I.dot1 w2, n+1) (* GEN END TAG OUTSIDE LET *)
            in
              (F', T.Ex ((I.decSub (D, w2), T.Explicit), F''))
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) convertFor' (I.Uni I.Type, M.Mnil, _, _, _) =
              ((* GEN BEGIN FUNCTION EXPRESSION *) fn F => F (* GEN END FUNCTION EXPRESSION *), T.True) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) convertFor' _ = raise Error "type family must be +/- moded" (* GEN END FUN BRANCH *)
    
        (* shiftPlus (mS) = s'
    
         Invariant:
         s' = ^(# of +'s in mS)
         *)
    
        fun shiftPlus mS =
          let
            fun (* GEN BEGIN FUN FIRST *) shiftPlus' (M.Mnil, n) = n (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) shiftPlus' (M.Mapp (M.Marg (M.Plus, _), mS'), n) =
                  shiftPlus' (mS', n+1) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) shiftPlus' (M.Mapp (M.Marg (M.Minus, _), mS'), n) =
                  shiftPlus' (mS', n) (* GEN END FUN BRANCH *)
          in
            shiftPlus' (mS, 0)
          end
    
        (* GEN BEGIN TAG OUTSIDE LET *) val n = shiftPlus mS (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (F, F') = convertFor' (V, mS, I.id, I.Shift n, n) (* GEN END TAG OUTSIDE LET *)
      in
        F F'
      end



    (* createIH L = (Psi', P', F')

       Invariant:
       If   L is a list of type families
       and  Psi is a context
       then Psi' extends Psi' by declarations in L
       and  F' is the conjunction of the formuals
            that corresponds to each type family in L
       and  Psi' |- P' in F'
    *)
    fun (* GEN BEGIN FUN FIRST *) createIH nil = raise Error "Empty theorem" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createIH [a] =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val name = I.conDecName (I.sgnLookup a) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val F = convertOneFor a (* GEN END TAG OUTSIDE LET *)
        in
          (name, F)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) createIH (a :: L) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val name = I.conDecName (I.sgnLookup a) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val F = convertOneFor a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (name', F') = createIH  L (* GEN END TAG OUTSIDE LET *)
        in
          (name ^ "/" ^ name', T.And (F, F'))
        end (* GEN END FUN BRANCH *)




    fun convertFor L =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (_, F') = createIH L (* GEN END TAG OUTSIDE LET *)
      in
        F'
      end

    (* occursInExpN (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
    fun (* GEN BEGIN FUN FIRST *) occursInExpN (k, I.Uni _) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInExpN (k, I.Pi (DP, V)) = occursInDecP (k, DP) orelse occursInExpN (k+1, V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExpN (k, I.Root (H, S)) = occursInHead (k, H) orelse occursInSpine (k, S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInExpN (k, I.Lam (D, V)) = occursInDec (k, D) orelse occursInExpN (k+1, V) (* GEN END FUN BRANCH *)
      (* | occursInExpN (k, I.FgnExp (cs, ops)) =
         occursInExpN (k, Whnf.normalize (#toInternal(ops) (), I.id)) MERGE Fri Aug 22 23:09:53 2003 --cs *)
      | (* GEN BEGIN FUN BRANCH *) occursInExpN (k, I.FgnExp csfe) =
        I.FgnExpStd.fold csfe ((* GEN BEGIN FUNCTION EXPRESSION *) fn (U, DP) => DP orelse (occursInExp (k, Whnf.normalize (U, I.id))) (* GEN END FUNCTION EXPRESSION *)) false (* GEN END FUN BRANCH *)

   (* no case for Redex, EVar, EClo *)


    and (* GEN BEGIN FUN FIRST *) occursInHead (k, I.BVar (k')) = (k = k') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.Const _) = false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.Def _) = false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.FgnConst _) = false (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) occursInHead (k, I.Proj _) = false (* GEN END FUN BRANCH *)
      (* no case for FVar *)

    and (* GEN BEGIN FUN FIRST *) occursInSpine (_, I.Nil) = false (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) occursInSpine (k, I.App (U, S)) = occursInExpN (k, U) orelse occursInSpine (k, S) (* GEN END FUN BRANCH *)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExpN (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    and occursInExp (k, U) = occursInExpN (k, Whnf.normalize (U, I.id))


    (* dot1inv w = w'

       Invariant:
       If   G, A |- w : G', A
       then G |- w' : G'
       and  w = 1.w' o ^
    *)
    fun dot1inv (w) = strengthenSub (I.comp (I.shift, w), I.shift)

    (* shiftinv (w) = w'

       Invariant:
       If   G, A |- w : G'
       and  1 does not occur in w
       then w  = w' o ^
    *)
    fun shiftinv (w) = strengthenSub (w, I.shift)

    fun peel w =
      if isIdx1(I.bvarSub (1, w)) then dot1inv w else shiftinv w

    fun (* GEN BEGIN FUN FIRST *) peeln (0, w) = w (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) peeln (n, w) = peeln (n-1, peel w) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) popn (0, Psi) = (Psi, I.Null) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) popn (n, I.Decl (Psi, T.UDec D)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', G') = popn (n-1, Psi) (* GEN END TAG OUTSIDE LET *)
        in
          (Psi', I.Decl (G', D))
        end (* GEN END FUN BRANCH *)


    (* domain (G2, w) = n'

       Invariant:
       If   G2 |- w: G1   and w weakening substitution
       then n' = |G1|
    *)
    fun (* GEN BEGIN FUN FIRST *) domain (G, I.Dot (I.Idx _, s)) = domain (G, s) + 1 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) domain (I.Null, I.Shift 0) = 0 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) domain (G as I.Decl _, I.Shift 0) = domain (G, I.Dot (I.Idx 1, I.Shift 1)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) domain (I.Decl (G, _), I.Shift n) = domain (G, I.Shift (n-1)) (* GEN END FUN BRANCH *)


    (* strengthen (Psi, (a, S), w, m) = (Psi', w')

       This function traverses the spine, and finds
       all variables in a position input/output position m
       (hence strenghten might not be a good name for it, because it is to general.)

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1 (but is a subset of Psi?)
    *)

    fun strengthen (Psi, (a, S), w, m) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val mS = modeSpine a (* GEN END TAG OUTSIDE LET *)
    
        fun (* GEN BEGIN FUN FIRST *) args (I.Nil, M.Mnil) = nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) args (I.App (U, S'), M.Mapp (M.Marg (m', _), mS)) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val L = args (S', mS) (* GEN END TAG OUTSIDE LET *)
              in
                (case M.modeEqual (m, m')
                   of true => U :: L
                    | false => L)
              end (* GEN END FUN BRANCH *)
    
    
        fun (* GEN BEGIN FUN FIRST *) strengthenArgs (nil, s) =  nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) strengthenArgs (U :: L, s) =
              strengthenExp (U, s) :: strengthenArgs (L, s) (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) occursInArgs (n, nil) = false (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) occursInArgs (n, U :: L) =
            (occursInExp (n, U) orelse occursInArgs (n, L)) (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) occursInPsi (n, (nil, L)) =
              occursInArgs (n, L) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) occursInPsi (n, (T.UDec (I.Dec (_, V)) :: Psi1, L)) =
              occursInExp (n, V) orelse occursInPsi (n+1, (Psi1, L)) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) occursInPsi (n, (T.UDec (I.BDec (_, (cid, s))) :: Psi1, L)) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val I.BlockDec (_, _, G, _) = I.sgnLookup cid (* GEN END TAG OUTSIDE LET *)
              in
                occursInSub (n, s, G) orelse occursInPsi (n+1, (Psi1, L))
              end (* GEN END FUN BRANCH *)
        and (* GEN BEGIN FUN FIRST *) occursInSub (_, _, I.Null) = false (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) occursInSub (n, I.Shift k, G) =
              occursInSub (n, I.Dot (I.Idx (k+1), I.Shift (k+1)), G) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) occursInSub (n, I.Dot (I.Idx k, s), I.Decl (G, _)) =
              (n = k) orelse occursInSub (n, s, G) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) occursInSub (n, I.Dot (I.Exp U, s), I.Decl (G, _)) =
              occursInExp (n, U) orelse occursInSub (n, s, G) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) occursInSub (n, I.Dot (I.Block _, s), I.Decl (G, _)) =
              occursInSub (n, s, G) (* GEN END FUN BRANCH *)   (* is this ok? -- cs *)
          (* no other cases *)
    
        and (* GEN BEGIN FUN FIRST *) occursInG (n, I.Null, k) = k n (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) occursInG (n, I.Decl (G, I.Dec (_, V)), k) =
              occursInG (n, G, (* GEN BEGIN FUNCTION EXPRESSION *) fn n' => occursInExp (n', V) orelse k (n'+ 1) (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN BRANCH *)
    
        fun occursBlock (G, (Psi2, L)) =
          let
            fun (* GEN BEGIN FUN FIRST *) occursBlock (I.Null, n) = false (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) occursBlock (I.Decl (G, D), n) =
                  occursInPsi (n, (Psi2, L)) orelse occursBlock (G, n+1) (* GEN END FUN BRANCH *)
          in
            occursBlock (G, 1)
          end
    
        (* testBlock (G, (bw, w1)) = (bw', w')
    
           Invariant:
           If   |- G ctx
           and  |- G1 ctx
           and  |- G2 ctx
           and  G1 |- w1 : G2, G
           and  bw is a boolean value
           then there ex. a G1'
           s.t. |- G1' ctx
           and  G1' |- w' : G2
           and  bw' = bw or (G1 =/= G1')
         *)
        fun (* GEN BEGIN FUN FIRST *) inBlock (I.Null, (bw, w1)) = (bw, w1) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) inBlock (I.Decl (G, D), (bw, w1)) =
            if isIdx1(I.bvarSub (1, w1)) then
              inBlock (G, (true, dot1inv w1))
            else inBlock (G, (bw, strengthenSub (w1, I.shift))) (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) blockSub (I.Null, w) = (I.Null, w) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) blockSub (I.Decl (G, I.Dec (name, V)), w) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (G', w') = blockSub (G, w) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val V' = strengthenExp (V, w') (* GEN END TAG OUTSIDE LET *)
            in
              (I.Decl (G', I.Dec (name, V')), I.dot1 w')
            end (* GEN END FUN BRANCH *)
    
        (* strengthen' (Psi1, Psi2, S, w1) =  (Psi', w')
    
           Invariant:
           If   |- Psi1 ctx
           and  Psi1 |- Psi2 ctx      (Psi2 is a list to maintain order)
           and  |- Psi3 ctx
           and  Psi1 |- w1 : Psi3     where w1 is a weakening substitution
           and  Psi1, Psi2 |- S : V1 > V2
           then |- Psi' ctx
           and  Psi1 |- w' : Psi'     where w' is a weakening substitution
           where Psi3 < Psi' < Psi1   (Psi' contains all variables of Psi3
                                       and all variables occuring in m
                                       position in S)
        *)
        fun (* GEN BEGIN FUN FIRST *) strengthen' (I.Null, Psi2, L, w1 (* =  I.id *)) = (I.Null, I.id, I.id) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) strengthen' (I.Decl (Psi1, LD as T.UDec (I.Dec (name, V))), Psi2, L, w1) =
            if isIdx1(I.bvarSub (1, w1)) then
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val w1' = dot1inv w1 (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (Psi1', w', z') = strengthen' (Psi1, LD :: Psi2, L, w1') (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val V' = strengthenExp (V, w') (* GEN END TAG OUTSIDE LET *)
              in
                (I.Decl (Psi1', T.UDec (I.Dec (name, V'))), I.dot1 w', I.dot1 z')
              end
            else
              if occursInPsi (1, (Psi2, L)) then
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val w1' = strengthenSub (w1, I.shift) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val (Psi1', w', z') = strengthen' (Psi1, LD :: Psi2, L, w1') (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val V' = strengthenExp (V, w') (* GEN END TAG OUTSIDE LET *)
                in
                  (I.Decl (Psi1', T.UDec (I.Dec (name, V'))), I.dot1 w', I.comp (z', I.shift))
                end
              else
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val w1' = strengthenSub (w1, I.shift) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val w2 = I.shift (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val (Psi2', w2') = strengthenPsi' (Psi2, w2) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val L' = strengthenArgs (L, w2') (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val (Psi1'', w', z') = strengthen' (Psi1, Psi2', L', w1') (* GEN END TAG OUTSIDE LET *)
                in
                  (Psi1'', I.comp (w', I.shift), z')
                end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) strengthen' (I.Decl (Psi1, D as T.PDec (name, F, NONE, NONE)), Psi2, L, w1) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val w1' = dot1inv w1 (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (Psi1', w', z') = strengthen' (Psi1, D :: Psi2, L, w1') (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val F' = strengthenFor (F, w') (* GEN END TAG OUTSIDE LET *)
            in
              (I.Decl (Psi1', T.PDec (name, F', NONE, NONE)), I.dot1 w', I.dot1 z')
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) strengthen' (I.Decl (Psi1, LD as T.UDec (I.BDec (name, (cid, s)))), Psi2, L, w1) =
            let  (* blocks are always used! *)
              (* GEN BEGIN TAG OUTSIDE LET *) val w1' = dot1inv w1 (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (Psi1', w', z') = strengthen' (Psi1, LD :: Psi2, L, w1') (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val s' = strengthenSub (s, w') (* GEN END TAG OUTSIDE LET *)
            in
              (I.Decl (Psi1', T.UDec (I.BDec (name, (cid, s')))), I.dot1 w', I.dot1 z')
            end (* GEN END FUN BRANCH *)
      in
        strengthen' (Psi, nil, args (S, mS), w)
      end





    fun lookupIH (Psi, L, a) =
        let
          fun lookupIH' (b::L, a, k)=
              if a = b then k
              else lookupIH' (L, a, k-1)
        in
          lookupIH' (L, a, I.ctxLength Psi)
        end


    (* createSub (Psi, L) = t'

       Invariant:
       If  |- Psi = Psi0, Psi1 ctx
       and Psi0 contains all declarations for invariants in L
       and |Psi0| = n
       and |L| = k
       and n = k + m - 1
       then Psi |- t' = m, m+1 ... n. ^n :  Psi0
    *)
    fun createIHSub (Psi, L) =
         T.Shift (I.ctxLength Psi - 1 (*List.length L *))


    (* transformInit (Psi, (a, S), w1) = (w', s')

       Invariant:
       If   |- Psi ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w1 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi+ |- s' : Gamma+
       and  x1:A1 .. xn:An |- w: Gamma+    (w weakening substitution)
    *)
    fun transformInit (Psi, L, (a, S), w1) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val mS = modeSpine a (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val V = typeOf a (* GEN END TAG OUTSIDE LET *)
    
        (* transformInit' ((S, mS), V, (w, s)) = (w', s')
    
           Invariant:
           If   Psi |- S : V > type
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *)
    
        fun (* GEN BEGIN FUN FIRST *) transformInit' ((I.Nil, M.Mnil), I.Uni I.Type, (w, s)) = (w, s) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) transformInit' ((I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS)),
                            I.Pi (_, V2), (w, s)) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val w' = I.comp (w, I.shift) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val s' = s (* GEN END TAG OUTSIDE LET *)
            in
              transformInit' ((S, mS), V2, (w', s'))
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) transformInit' ((I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS)),
                            I.Pi ((I.Dec (name, V1), _), V2), (w, s)) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val V1' = strengthenExp (V1, w) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val w' = I.dot1 w (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val U' = strengthenExp (U, w1) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val s' = T.dotEta (T.Exp U', s) (* GEN END TAG OUTSIDE LET *)
            in
              transformInit' ((S, mS), V2, (w', s'))
            end (* GEN END FUN BRANCH *)
      in
        transformInit' ((S, mS), V, (I.id, createIHSub (Psi, L)))
      end

    (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)
    fun transformConc ((a, S), w) =
      let
    
        fun (* GEN BEGIN FUN FIRST *) transformConc' (I.Nil, M.Mnil) =
              T.Unit (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) transformConc' (I.App (U, S'), M.Mapp (M.Marg (M.Plus, _), mS')) =
              transformConc' (S', mS') (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) transformConc' (I.App (U, S'), M.Mapp (M.Marg (M.Minus, _), mS')) =
              T.PairExp (strengthenExp (U, w), transformConc' (S', mS')) (* GEN END FUN BRANCH *)
      in
        transformConc' (S, modeSpine a)
      end


    (* renameExp f U = U'

       Invariant:
       U' = U module application of f to any projectoin contained
       in U.
    *)
    fun (* GEN BEGIN FUN FIRST *) renameExp f (U as I.Uni _) = U (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) renameExp f (I.Pi ((D, DP), V)) =
          I.Pi ((renameDec f D, DP), renameExp f V) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) renameExp f (I.Root (H, S)) =
          I.Root (renameHead f H, renameSpine f S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) renameExp f (I.Lam (D, U)) =
          I.Lam (renameDec f D, renameExp f U) (* GEN END FUN BRANCH *)
    and renameDec f (I.Dec (x, V)) =
          I.Dec (x, renameExp f V)
    and (* GEN BEGIN FUN FIRST *) renameHead f (I.Proj bi) = f bi (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) renameHead f H = H (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) renameSpine f I.Nil = I.Nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) renameSpine f (I.App (U, S)) = I.App (renameExp f U, renameSpine f S) (* GEN END FUN BRANCH *)


    fun rename (I.BDec (_, (c, s)), V) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G, L) = I.constBlock c (* GEN END TAG OUTSIDE LET *)
    
          fun (* GEN BEGIN FUN FIRST *) makeSubst (n, G, s, nil, f) = (G, f) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) makeSubst (n, G, s,( D as I.Dec (x, V')) :: L, f) =
              if Subordinate.belowEq (I.targetFam V', I.targetFam V) then
                makeSubst (n+1, I.Decl (G, I.decSub (D, s)), I.dot1 s, L,
                           f)
              else
                makeSubst (n, G, I.comp (s, I.shift), L, f) (* GEN END FUN BRANCH *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', f) = makeSubst (1, G, s, L, (* GEN BEGIN FUNCTION EXPRESSION *) fn x => I.Proj x (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        in
          (G, renameExp f V)
        end


        fun (* GEN BEGIN FUN FIRST *) append (G, I.Null) = G (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) append (G, I.Decl (G', D)) = I.Decl (append (G, G'), D) (* GEN END FUN BRANCH *)


        (* traverseNeg (L, wmap, projs)  (Psi0, Psi, V) = ([w', PQ'], L')    [] means optional

           Invariant:
           If   |- Psi0 ctx      (context that contains induction hypotheses)
           and  Psi0 |- Psi ctx  (context of all assumptions)
           and  Psi0, Psi |- V : type
           then L' list of cases
           and  Psi0, Psi |- w' : Psi0, Psi'
           and  PQ'  is a pair that can generate a proof term
        *)
        fun (* GEN BEGIN FUN FIRST *) traverseNeg (L, wmap, projs)  ((Psi0, Psi), I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), w) =
            (case traverseNeg (L, wmap, projs)  ((Psi0, I.Decl (Psi, T.UDec D)), V2, I.dot1 w)
               of (SOME (w', PQ')) => SOME (peel w', PQ')) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) traverseNeg (L, wmap, projs)  ((Psi0, Psi), I.Pi ((D as I.Dec (_, V1), I.No), V2), w) =
            (case traverseNeg (L, wmap, projs)  ((Psi0, I.Decl (Psi, T.UDec D)), V2, I.comp (w, I.shift))
               of (SOME (w', PQ')) => traversePos (L, wmap, projs)  ((Psi0, Psi, I.Null), V1, SOME (peel w', PQ'))) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) traverseNeg (L, wmap, projs)  ((Psi0, Psi), I.Root (I.Const a, S), w) =
                                        (* Psi0, Psi |- w : Psi0, Psi' *)
                                        (* Sigma (a) = Va *)
                                        (* Psi0, Psi |- S : {G} type > type *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Psi1 = append (Psi0, Psi) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi1 = Psi0, Psi *)
              (* GEN BEGIN TAG OUTSIDE LET *) val w0 = I.Shift (I.ctxLength Psi) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi1 |- w0 : Psi0 *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', w', _) = strengthen (Psi1, (a, S), w0, M.Plus) (* GEN END TAG OUTSIDE LET *)
                                        (* |- Psi' ctx *)
                                        (* Psi1 |- w' : Psi' *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (w'', s'') = transformInit (Psi', L, (a, S), w') (* GEN END TAG OUTSIDE LET *)
                                        (* Psi' |- s'' : G+ *)
                                        (* G |- w'' : G+ *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkCtx Psi' (* GEN END TAG OUTSIDE LET *)
            in
              (SOME (w', ((* GEN BEGIN FUNCTION EXPRESSION *) fn P => (Psi', s'', P) (* GEN END FUNCTION EXPRESSION *), transformConc ((a, S), w))))
            end (* GEN END FUN BRANCH *)

        and (* GEN BEGIN FUN FIRST *) traversePos (L, wmap, projs)  ((Psi0, Psi, G), I.Pi ((D as I.BDec (x, (c, s)), _), V), SOME (w1, (P, Q))) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val c' = wmap c (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val n = I.ctxLength Psi0 + I.ctxLength G (* GEN END TAG OUTSIDE LET *)
        
              (* GEN BEGIN TAG OUTSIDE LET *) val (Gsome, Lpi) = I.constBlock c (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheckCtx (T.coerceCtx (append(append(Psi0, Psi), T.embedCtx G))) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheckSub (T.coerceCtx (append(append(Psi0, Psi), T.embedCtx G)), s, Gsome) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (Gsome', Lpi') = I.constBlock c' (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheckCtx (T.coerceCtx (append(append(Psi0, Psi), T.embedCtx G))) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheckSub (T.coerceCtx (append(append(Psi0, Psi), T.embedCtx G)), s, Gsome') (* GEN END TAG OUTSIDE LET *)
            in
              traversePos (L, wmap, projs)  ((Psi0, Psi,
                            I.Decl (G,  (* T.UDec *) (I.BDec (x, (c', s))))),
                           V, SOME (I.dot1 w1, (P, Q)))
            end (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) traversePos (L, wmap, projs)  ((Psi0, G, B), V as I.Root (I.Const a, S), SOME (w1, (P, Q))) =
                                        (* Psi0 = x1::F1 ... xn::Fn *)
                                        (* |- Psi0 matches L *)
                                        (* Psi0, G, B |- V : type *)
                                        (* Psi0, G, B |- w1 : Psi0, G', B' *)
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val Psi1 = append (Psi0, append (G, T.embedCtx B)) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi1 = Psi0, G, B *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkCtx (append(append(Psi0, G), T.embedCtx B)) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val n = domain (Psi1, w1) (* GEN END TAG OUTSIDE LET *) (* n = |Psi0, G', B'| *)
              (* GEN BEGIN TAG OUTSIDE LET *) val m = I.ctxLength Psi0 (* GEN END TAG OUTSIDE LET *)  (* m = |Psi0| *)
          
              fun lookupbase a =
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val s = I.conDecName (I.sgnLookup a) (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val l = T.lemmaName s (* GEN END TAG OUTSIDE LET *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val T.ValDec (_, P, F) = T.lemmaLookup l (* GEN END TAG OUTSIDE LET *)
                  in
                    (T.Const l, F)
                  end
          
              fun (* GEN BEGIN FUN FIRST *) lookup (([b], NONE, F), a) =
                  if a=b then
                    let
                      (* GEN BEGIN TAG OUTSIDE LET *) val P = T.Var n (* GEN END TAG OUTSIDE LET *)
                    in
                      (P, F)
                    end
                  else lookupbase a (* GEN END FUN FIRST *)
                | (* GEN BEGIN FUN BRANCH *) lookup (([b], SOME [lemma], F), a) =
                  if a = b then
                    let
                      (* GEN BEGIN TAG OUTSIDE LET *) val P = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil)) (* GEN END TAG OUTSIDE LET *)
                    in
                      (P, F)
                    end
                  else lookupbase a (* GEN END FUN BRANCH *)
                | (* GEN BEGIN FUN BRANCH *) lookup ((b :: L, SOME (lemma :: lemmas), T.And (F1, F2)), a) =
                  if a = b then
                    let
                      (* GEN BEGIN TAG OUTSIDE LET *) val P = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil)) (* GEN END TAG OUTSIDE LET *)
                    in
                      (P, F1)
                    end
                  else lookup ((L, SOME lemmas, F2), a) (* GEN END FUN BRANCH *)
          
              (* strengthened invariant Psi0 might be empty --cs Fri Apr 11 15:25:32 2003 *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (HP, F) = if I.ctxLength Psi0 > 0 then
                              let
                                (* GEN BEGIN TAG OUTSIDE LET *) val T.PDec(_, F0, _, _) =  I.ctxLookup (Psi0, 1) (* GEN END TAG OUTSIDE LET *)
                              in
                                lookup ((L, projs, F0), a)
                              end
                            else lookupbase a (* GEN END TAG OUTSIDE LET *)
          
          
              (* apply ((S, mS), F')= (S'', F'')
          
                 Invariant:
                 Psi0, G, B |- S : V >> type
                   (mS is the corresponding mode spine)
                 and  Psi0, G', B |- F'  :: for
                 then Psi0, G', B |- F'' :: for
                 and  Psi0, G', B |- S'' :: F' >> F''
              *)
          
              fun apply ((S, mS), Ft) = applyW ((S, mS), T.whnfFor (Ft))
              and (* GEN BEGIN FUN FIRST *) applyW ((I.Nil, M.Mnil), Ft') = (T.Nil, T.forSub Ft') (* GEN END FUN FIRST *)
                | (* GEN BEGIN FUN BRANCH *) applyW ((I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS)),
                         (T.All (D, F'), t')) =
                                        (* Psi0, G', B' |- D = x:V' : type *)
                                        (* Psi0, G', B', x:V' |- F' :: for *)
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val U' = strengthenExp (U, w1) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G', B' |- U' : V' *)
                    (* GEN BEGIN TAG OUTSIDE LET *) val (S'', F'') = apply ((S, mS), (F', T.Dot (T.Exp U', t'))) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G', B' |- F'' :: for *)
                                        (* Psi0, G', B' |- S'' : F' [t'] >> F'' *)
                  in
                   (T.AppExp (U', S''), F'')
                                        (* Psi0, G', B' |- U' ; S''
                                                       : all {x:V'} F' >> F'' *)
                  end (* GEN END FUN BRANCH *)
                | (* GEN BEGIN FUN BRANCH *) applyW ((I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS)), Ft) =
                    applyW ((S, mS), Ft) (* GEN END FUN BRANCH *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val (S'', F'') = apply ((S, modeSpine a), (F, T.id)) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G', B' |- F'' :: for *)
                                        (* Psi0, G', B' |- S'' :: F' >> F'' *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkFor (append (append (Psi0, G), T.embedCtx B),
                                                (T.forSub(F'', T.embedSub w1))) (* GEN END TAG OUTSIDE LET *)
          
          
          
              (* GEN BEGIN TAG OUTSIDE LET *) val P'' = T.Redex (HP (*T.Var k' *) , S'') (* GEN END TAG OUTSIDE LET *)  (* was T.Root  -cs Sun Jan  5 23:15:06 2003 *)
                                        (* Psi0, G', B' |- P'' :: F'' *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val b = I.ctxLength B (* GEN END TAG OUTSIDE LET *)     (* b = |B| = |B'| *)
              (* GEN BEGIN TAG OUTSIDE LET *) val w1' = peeln (b, w1) (* GEN END TAG OUTSIDE LET *)   (* Psi0, G |- w1' : Psi0, G' *)
          
          
              (* GEN BEGIN TAG OUTSIDE LET *) val (B', _) = strengthenCtx (B, w1') (* GEN END TAG OUTSIDE LET *)
                                        (* |- Psi0, G', B' ctx *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val n' = n - I.ctxLength B' (* GEN END TAG OUTSIDE LET *)   (* n' = |Psi0, G'| *)
          
          
              fun (* GEN BEGIN FUN FIRST *) subCtx (I.Null, s) = (I.Null, s) (* GEN END FUN FIRST *)
                | (* GEN BEGIN FUN BRANCH *) subCtx (I.Decl (G, D), s) =
                  let (* GEN BEGIN TAG OUTSIDE LET *) val (G', s') = subCtx (G, s) (* GEN END TAG OUTSIDE LET *)
                  in (I.Decl (G', I.decSub (D, s')), I.dot1 s')
                  end (* GEN END FUN BRANCH *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val (B'', _) = subCtx (B', w1') (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkCtx (append (append (Psi0, G), T.embedCtx B'')) (* GEN END TAG OUTSIDE LET *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val (GB', iota) = T.deblockify  B' (* GEN END TAG OUTSIDE LET *)    (* Psi0, G' |- GB' ctx *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheckSub (GB', T.coerceSub iota, B')
                         handle TypeCheck.Error _ => raise Error' iota (* GEN END TAG OUTSIDE LET *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val RR = T.forSub (F'', iota) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G, B |- w1 : Psi0, G', B' *)
                                        (* Psi0, G', GB'  |- s' : Psi0, G', B' *)
                                        (* Psi0, G', GB' |- RR for *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val F''' = TA.raiseFor (GB', (RR, I.id)) (* GEN END TAG OUTSIDE LET *)
                                          (* Psi0, G |- w1' : Psi0, G' *)
                                          (* Psi0, G' |- F''' for *)
          
          
              (* lift (B, (P, F)) = (P', F')
          
                 Invariant:
                 If   Psi0, G, B |- P :: F
                 then Psi0, G |- P'  :: F'
                 and  P' =  (lam B. P)
                 and  F' = raiseFor (B, F)
              *)
              fun (* GEN BEGIN FUN FIRST *) lift (I.Null, P) = P (* GEN END FUN FIRST *)
                | (* GEN BEGIN FUN BRANCH *) lift (I.Decl (G, D), P) =
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val (Bint, _) = T.deblockify (I.Decl (I.Null, D)) (* GEN END TAG OUTSIDE LET *)
                  in
                    lift (G, T.New (T.Lam (T.UDec D, P)))
                  end (* GEN END FUN BRANCH *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val P''' = lift (B', P'') (* GEN END TAG OUTSIDE LET *) (* Psi0, G' |- P''' :: F''' *)
          
          
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkCtx (append (Psi0, G)) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkFor (append (Psi0, G),
                                                (T.forSub(F''', T.embedSub w1'))) (* GEN END TAG OUTSIDE LET *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val (Psi1'', w2, z2) = strengthen (Psi1, (a, S), w1, M.Minus) (* GEN END TAG OUTSIDE LET *)
                                        (* |- Psi0, Psi1'' ctx *)
                                        (* Psi0, G, B |- w2 : Psi1'' *)
                                        (* Psi1'' = Psi0, G3, B3' *)
                                        (* |B| = |GB'| *)
                                        (* Psi'' |-  z2 : Psi0, G', B' *)
                                        (* Psi0, G, B |- w2 : Psi0, G3, B3' *)
              (* GEN BEGIN TAG OUTSIDE LET *) val w3 = peeln (b, w2) (* GEN END TAG OUTSIDE LET *)    (* Psi0, G |- w3 : Psi0, G3 *)
              (* GEN BEGIN TAG OUTSIDE LET *) val z3 = peeln (b, z2) (* GEN END TAG OUTSIDE LET *)    (* Psi0, G3 |-  z3 : Psi0, G' *)
          
          
              (* GEN BEGIN TAG OUTSIDE LET *) val (Psi2, B3') = popn (b, Psi1'') (* GEN END TAG OUTSIDE LET *)
                                        (* Psi2 = Psi0, G3 *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val Pat' = transformConc ((a, S), w2) (* GEN END TAG OUTSIDE LET *)
          
                                        (* Psi0, G3, B3' |- Pat' :: For *)
              (* GEN BEGIN TAG OUTSIDE LET *) val F4 = T.forSub (F''', T.embedSub z3) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G3 |- F4 for *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkCtx (Psi1'') (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkCtx (append (Psi2, T.embedCtx B3')) (* GEN END TAG OUTSIDE LET *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkFor (Psi2, F4)
                handle _ => raise Error "" (* GEN END TAG OUTSIDE LET *)(* ' F4 *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val (B3, sigma3) = T.deblockify  B3' (* GEN END TAG OUTSIDE LET *)
          
              (* GEN BEGIN TAG OUTSIDE LET *) val Pat'' = T.normalizePrg (Pat', sigma3) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Pat = TA.raisePrg (B3, Pat'', F4) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G3 |- Pat :: F4  *)
                                        (* Here's a commutative diagram
                                           at work which one has to prove
                                           correct
                                        *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkPrg (Psi2, (Pat, F4)) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val t = T.Dot (T.Prg Pat, T.embedSub z3) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G3 |- t :: Psi0, G', x :: F4  *)
            in
              (SOME (w3,
                     ((* GEN BEGIN FUNCTION EXPRESSION *) fn p => P (T.Let (T.PDec (NONE, F''', NONE, NONE), P''',
                                        T.Case (T.Cases [(Psi2, t, p)]))) (* GEN END FUNCTION EXPRESSION *), Q)))
            end (* GEN END FUN BRANCH *)




    (* traverse (Psi0, L, Sig, wmap) = C'

       Invariant:
       If   |- Psi0  ctx
       and  L is a the theorem we would like to transform
       and  Sig is a signature
       and  forall (G, V) in Sig the following holds:
                    Psi0, G |- V : type
               and  head (V) in L
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
       then C' is a list of cases (corresponding to each (G, V) in Sig)
    *)
    fun traverse (Psi0, L, Sig, wmap, projs) =
      let
    
    
        fun (* GEN BEGIN FUN FIRST *) traverseSig' nil = nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) traverseSig' ((G, V) :: Sig) =
            (TypeCheck.typeCheck (append (T.coerceCtx Psi0, G), (V, I.Uni I.Type));
             case traverseNeg (L, wmap, projs) ((Psi0, T.embedCtx G), V, I.id)
               of (SOME (wf, (P', Q'))) =>  traverseSig' Sig @ [(P' Q')]) (* GEN END FUN BRANCH *)
      in
        traverseSig' Sig
      end




    (* transformWorlds (fams, W) = (W', wmap)

       Invariant:
       If   fams is the theorem to be compiled
       and  W a world with declarations,
       then W' is the new world stripped of all dynamic extensions
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
    *)
    fun transformWorlds (fams, T.Worlds cids) =
        let
          (* convertList (a, L, w) = L'
    
             Invariant:
             If   G0 |- G, L : ctx
             and  G0, G |- w : G0, G'
             then G0 |- G', L' ctx
          *)
          fun (* GEN BEGIN FUN FIRST *) transformList (nil, w) = nil (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) transformList ((D as I.Dec (x, V)) :: L, w) =
              if List.foldr ((* GEN BEGIN FUNCTION EXPRESSION *) fn (a, b) => b andalso Subordinate.belowEq (a, I.targetFam V) (* GEN END FUNCTION EXPRESSION *)) true fams then
                transformList (L,  I.comp (w, I.shift))
              else
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val  L' = transformList (L, I.dot1 w) (* GEN END TAG OUTSIDE LET *)
                in
                  (I.Dec (x, strengthenExp (V, w))) :: L'
                end (* GEN END FUN BRANCH *)
    
          fun (* GEN BEGIN FUN FIRST *) transformWorlds' (nil) = (nil, (* GEN BEGIN FUNCTION EXPRESSION *) fn c => raise Error "World not found" (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) transformWorlds' (cid :: cids') =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val I.BlockDec (s, m, G, L) = I.sgnLookup cid (* GEN END TAG OUTSIDE LET *)
                (* Design decision: Let's keep all of G *)
                (* GEN BEGIN TAG OUTSIDE LET *) val L' = transformList (L, I.id) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (cids'', wmap) = transformWorlds' (cids') (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val cid' = I.sgnAdd (I.BlockDec (s, m, G, L')) (* GEN END TAG OUTSIDE LET *)
              in
                (cid' :: cids'', (* GEN BEGIN FUNCTION EXPRESSION *) fn c => if c = cid then cid' else wmap c (* GEN END FUNCTION EXPRESSION *))
              end (* GEN END FUN BRANCH *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val (cids', wmap) = transformWorlds' (cids) (* GEN END TAG OUTSIDE LET *)
    
        in
          (T.Worlds cids', wmap)
        end


    (* dynamicSig (Psi0, fams, W) = Sig'

       Invariant:
       If   |- Psi0 ctx
       and  fams are the typfamilies to be converted
       and  W is the world in which the translation takes place
       then Sig' = (G1;V1) ... (Gn;Vn)
       and  |- Psi0, Gi ctx
       and  Psi, Gi |- Vi : type.
    *)
    fun dynamicSig (Psi0, a, T.Worlds cids) =
        let
    
    
          (* findDec (G, n, L, s, S) = S'
    
             Invariant:
             If   G |-  L : ctx
             and  G |- w: G'
             then |- G', L' ctx
          *)
          fun (* GEN BEGIN FUN FIRST *) findDec (G, _, nil, w, Sig) = Sig (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) findDec (G, n, D :: L, w, Sig) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (D' as I.Dec (x, V')) = I.decSub (D, w) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val b = I.targetFam V' (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val Sig' = if b = a then  (G, Whnf.normalize (V',I.id)) :: Sig
                           else Sig (* GEN END TAG OUTSIDE LET *)
              in
                findDec (G, n+1, L, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, n), I.Nil)), w), Sig')
              end (* GEN END FUN BRANCH *)
    
          (* mediateSub G = (G0, s)
    
             Invariant:
             If   . |- G ctx
             then Psi0 |- G0 ctx
             and  Psi0, G0 |- s : G
          *)
          fun (* GEN BEGIN FUN FIRST *) mediateSub (I.Null) = (I.Null, I.Shift (I.ctxLength Psi0)) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) mediateSub (I.Decl (G, D)) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val (G0, s') = mediateSub G (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.decSub (D, s') (* GEN END TAG OUTSIDE LET *)
                in
                  (I.Decl (G0, D'), I.dot1 s')
                end (* GEN END FUN BRANCH *)
    
    
          fun (* GEN BEGIN FUN FIRST *) findDecs' (nil, Sig) = Sig (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) findDecs' (cid :: cids', Sig) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val I.BlockDec (s, m, G, L) = I.sgnLookup cid (* GEN END TAG OUTSIDE LET *)
                                        (* G |- L ctx *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (G0, s') = mediateSub G (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G0 |- s'' : G *)
                (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decName (G0, I.BDec (NONE, (cid, s'))) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G0 |- D : dec *)
                (* GEN BEGIN TAG OUTSIDE LET *) val s'' = I.comp (s', I.shift) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, G0, D' |- s'' : G *)
                
                (* GEN BEGIN TAG OUTSIDE LET *) val Sig' = findDec (I.Decl (G0, D'), 1, L, s'', Sig) (* GEN END TAG OUTSIDE LET *)
              in
                findDecs' (cids', Sig')
              end (* GEN END FUN BRANCH *)
        in
          findDecs' (cids, nil)
        end

    (* staticSig Sig = Sig'

       Invariant:
       If   |- Psi0 ctx
       then Sig' = (c1:V1) ... (cn:Vn)
       and  . |- Vi : type.
    *)
    fun (* GEN BEGIN FUN FIRST *) staticSig (Psi0, nil) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) staticSig (Psi0, I.ConDec (name, _, _, _, V, I.Type) :: Sig) =
          (I.Null, Whnf.normalize (V, I.Shift (I.ctxLength Psi0))) :: staticSig (Psi0, Sig) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) name [a] = I.conDecName (I.sgnLookup a) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) name (a :: L) = I.conDecName (I.sgnLookup a) ^ "/" ^ (name L) (* GEN END FUN BRANCH *)

    (* convertPrg L = P'

       Invariant:
       If   L is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in L into functional form
    *)

    fun convertPrg (L, projs) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (name, F0) = createIH L (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val D0 = T.PDec (SOME name, F0, NONE, NONE) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Psi0 = I.Decl (I.Null, D0) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val Prec = (* GEN BEGIN FUNCTION EXPRESSION *) fn p => T.Rec (D0, p) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
        fun (* GEN BEGIN FUN FIRST *) convertWorlds [a] =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val W = WorldSyn.lookup a (* GEN END TAG OUTSIDE LET *) (* W describes the world of a *)
            in
              W
            end (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) convertWorlds (a :: L') =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val W = WorldSyn.lookup a (* GEN END TAG OUTSIDE LET *) (* W describes the world of a *)
              (* GEN BEGIN TAG OUTSIDE LET *) val W' = convertWorlds L' (* GEN END TAG OUTSIDE LET *)
            in
              if T.eqWorlds (W, W') then W' else raise Error "Type families different in different worlds"
            end (* GEN END FUN BRANCH *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val W = convertWorlds L (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (W', wmap) = transformWorlds (L, W) (* GEN END TAG OUTSIDE LET *)
    
        fun convertOnePrg (a, F) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val name = nameOf a (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val V = typeOf a (* GEN END TAG OUTSIDE LET *)            (* Psi0 |- {x1:V1} ... {xn:Vn} type *)
            (* GEN BEGIN TAG OUTSIDE LET *) val mS = modeSpine a (* GEN END TAG OUTSIDE LET *)        (* |- mS : {x1:V1} ... {xn:Vn} > type *)
            (* GEN BEGIN TAG OUTSIDE LET *) val Sig = Worldify.worldify a (* GEN END TAG OUTSIDE LET *)
                                        (* Sig in LF(reg)   *)
            (* GEN BEGIN TAG OUTSIDE LET *) val dynSig = dynamicSig (Psi0, a, W) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val statSig = staticSig (Psi0, Sig) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (I.ConDec (_, _,_,_,U,V)) => TypeCheck.check (U, I.Uni  V) (* GEN END FUNCTION EXPRESSION *)) Sig (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = validSig (Psi0, statSig) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = validSig (Psi0, dynSig) (* GEN END TAG OUTSIDE LET *)
    
            (* GEN BEGIN TAG OUTSIDE LET *) val C0 = traverse (Psi0, L, dynSig, wmap, projs) (* GEN END TAG OUTSIDE LET *)
            (* init' F = P'
    
               Invariant:
               If   F = All x1:A1. ... All xn:An. F'
               and  f' does not start with a universal quantifier
               then P' P'' = Lam x1:A1. ... Lam xn:An P''
                    for any P''
            *)
            fun (* GEN BEGIN FUN FIRST *) init (T.All ((D, _), F')) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val (F'', P') = init F' (* GEN END TAG OUTSIDE LET *)
                in
                  (F'', (* GEN BEGIN FUNCTION EXPRESSION *) fn p => T.Lam (D, P' p) (* GEN END FUNCTION EXPRESSION *))
                end (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) init F' = (F', (* GEN BEGIN FUNCTION EXPRESSION *) fn p => p (* GEN END FUNCTION EXPRESSION *)) (* GEN END FUN BRANCH *)
    
            (* GEN BEGIN TAG OUTSIDE LET *) val (F', Pinit) = init F (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val C = traverse (Psi0, L, statSig, wmap, projs) (* GEN END TAG OUTSIDE LET *)
                                        (* Psi0, x1:V1, ..., xn:Vn |- C :: F *)
          in
            Pinit (T.Case ((* F', *) T.Cases (C0 @ C)))
          end
    
        fun (* GEN BEGIN FUN FIRST *) convertPrg' (nil, _) = raise Error "Cannot convert Empty program" (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) convertPrg' ([a], F) = convertOnePrg (a, F) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) convertPrg' (a :: L', T.And (F1, F2)) = T.PairPrg (convertOnePrg (a, F1), convertPrg' (L', F2)) (* GEN END FUN BRANCH *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val P = Prec (convertPrg' (L, F0)) (* GEN END TAG OUTSIDE LET *)
      in
        P
      end

    fun installFor [cid] =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val F = convertFor [cid] (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = I.conDecName (I.sgnLookup cid) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = T.lemmaAdd (T.ForDec (name, F)) (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end


    fun (* GEN BEGIN FUN FIRST *) depthConj (T.And (F1, F2)) =
        1+ depthConj F2 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) depthConj F = 1 (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) createProjection (Psi, depth, F as T.And (F1, F2), Pattern) =
          createProjection (I.Decl (Psi, T.PDec (NONE, F1, NONE, NONE)), depth+1,
                            T.forSub (F2, T.Shift 1),
                            T.PairPrg (T.Var (depth+2), Pattern)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) createProjection (Psi, depth, F,  Pattern) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val Psi' = I.Decl (Psi, T.PDec (NONE, F, NONE, NONE)) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val depth' = depth + 1 (* GEN END TAG OUTSIDE LET *)
          in
            (* GEN BEGIN FUNCTION EXPRESSION *) fn k => let
                      (* GEN BEGIN TAG OUTSIDE LET *) val T.PDec (_, F', _, _) = T.ctxDec (Psi', k) (* GEN END TAG OUTSIDE LET *)
                    in
                      (T.Case (T.Cases [(Psi',
                                       T.Dot (T.Prg (Pattern),
                                              T.Shift (depth')),
                                       T.Var k)]), F')
                    end (* GEN END FUNCTION EXPRESSION *)
          end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) installProjection (nil, _, F, Proj) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) installProjection (cid :: cids, n, F, Proj) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (P', F') = Proj n (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val P = T.Lam (T.PDec (NONE, F, NONE, NONE), P') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val F'' = T.All ((T.PDec (NONE, F, NONE, NONE), T.Explicit), F') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = I.conDecName (I.sgnLookup cid) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F'')) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val lemma = T.lemmaAdd (T.ValDec ("#" ^ name, P, F'')) (* GEN END TAG OUTSIDE LET *)
        in
          lemma :: installProjection (cids, n-1, F, Proj)
        end (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) installSelection ([cid], [lemma], F1, main) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val P = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = I.conDecName (I.sgnLookup cid) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F1)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val lemma' = T.lemmaAdd (T.ValDec (name, P, F1)) (* GEN END TAG OUTSIDE LET *)
        in
          [lemma']
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) installSelection (cid :: cids, lemma :: lemmas, T.And (F1, F2), main) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val P = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = I.conDecName (I.sgnLookup cid) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F1)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val lemma' = T.lemmaAdd (T.ValDec (name, P, F1)) (* GEN END TAG OUTSIDE LET *)
        in
          lemma' :: installSelection (cids, lemmas, F2, main)
        end (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) installPrg [cid] =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val F = convertFor [cid] (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val P = convertPrg ([cid], NONE) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = I.conDecName (I.sgnLookup cid) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.chatter >= 4) then print ("[Redundancy Checker (factoring) ...") else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val factP = Redundant.convert P (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.chatter >= 4) then print ("done]\n") else () (* GEN END TAG OUTSIDE LET *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val lemma = T.lemmaAdd (T.ValDec (name, factP, F)) (* GEN END TAG OUTSIDE LET *)
    
    
        in
          (lemma, [], [])
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) installPrg cids =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val F = convertFor cids (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkFor (I.Null, F) (* GEN END TAG OUTSIDE LET *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val Proj = createProjection (I.Null, 0, F, T.Var 1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val projs = installProjection (cids, depthConj F, F, Proj) (* GEN END TAG OUTSIDE LET *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val P = convertPrg (cids, SOME projs) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val s = name cids (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.chatter >= 4) then print ("[Redundancy Checker (factoring) ...") else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val factP = Redundant.convert P (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if (!Global.chatter >= 4) then print ("done]\n") else () (* GEN END TAG OUTSIDE LET *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val lemma = T.lemmaAdd (T.ValDec (s, factP, F)) (* GEN END TAG OUTSIDE LET *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val sels = installSelection (cids, projs, F, lemma) (* GEN END TAG OUTSIDE LET *)
      
        in
          (lemma, projs, sels)
        end (* GEN END FUN BRANCH *)



    fun (* GEN BEGIN FUN FIRST *) mkResult 0 = T.Unit (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) mkResult n = T.PairExp (I.Root (I.BVar n, I.Nil), mkResult (n-1)) (* GEN END FUN BRANCH *)

    fun convertGoal (G, V)  =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val a = I.targetFam V (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val W = WorldSyn.lookup a (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (W', wmap) = transformWorlds ([a], W) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val SOME (_, (P', Q')) = traversePos ([], wmap, NONE)
                                  ((I.Null, G, I.Null), V,
                                   SOME (I.Shift (I.ctxLength G),
                                         ((* GEN BEGIN FUNCTION EXPRESSION *) fn P => (I.Null, T.id, P) (* GEN END FUNCTION EXPRESSION *),  mkResult (I.ctxLength G)))) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (_, _, P'') = P' Q' (* GEN END TAG OUTSIDE LET *)
      in
        P''
      end

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val convertFor = convertFor (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val convertPrg = (* GEN BEGIN FUNCTION EXPRESSION *) fn L => convertPrg (L, NONE) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val installFor = installFor (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val installPrg = installPrg (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val traverse = traverse (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val convertGoal = convertGoal (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *) (* functor FunSyn *)
