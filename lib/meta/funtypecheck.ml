 (* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) FunTypeCheck ((*! structure FunSyn' : FUNSYN !*)
                      structure StateSyn' : STATESYN
                      (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                      structure Abstract : ABSTRACT
                      (*! sharing Abstract.IntSyn = FunSyn'.IntSyn !*)
                      structure TypeCheck : TYPECHECK
                      (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
                      structure Conv : CONV
                      (*! sharing Conv.IntSyn = FunSyn'.IntSyn !*)
                      structure Whnf : WHNF
                      (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
                      structure Print : PRINT
                      (*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
                      structure Subordinate : SUBORDINATE
                      (*! sharing Subordinate.IntSyn = FunSyn'.IntSyn !*)
                      structure Weaken : WEAKEN
                      (*! sharing Weaken.IntSyn = FunSyn'.IntSyn   !*)
                      structure FunPrint : FUNPRINT
                      (*! sharing FunPrint.FunSyn = FunSyn' !*)
                          ) : FUNTYPECHECK=
struct
  (*! structure FunSyn = FunSyn' !*)
  structure StateSyn = StateSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn

    (* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
    fun conv (Gs, Gs') =
      let
        exception Conv
        fun (* GEN BEGIN FUN FIRST *) conv ((I.Null, s), (I.Null, s')) = (s, s') (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) conv ((I.Decl (G, I.Dec (_, V)), s),
                  (I.Decl (G', I.Dec (_, V')), s')) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (s1, s1') = conv ((G, s), (G', s')) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val ps as (s2, s2') = (I.dot1 s1, I.dot1 s1') (* GEN END TAG OUTSIDE LET *)
            in
              if Conv.conv ((V, s1), (V', s1')) then ps
              else raise Conv
            end (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) conv _ = raise Conv (* GEN END FUN BRANCH *)
      in
        (conv (Gs, Gs'); true) handle Conv => false
      end



    (* extend (G, L) = G'

       Invariant:
       If   G : 'a ctx
       and  L : 'a list
       then G' = G, L : 'a ctx
    *)
    fun (* GEN BEGIN FUN FIRST *) extend (G, nil) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) extend (G, D :: L) = extend (I.Decl (G, D), L) (* GEN END FUN BRANCH *)


    (* validBlock (Psi, k, (l : G)) = ()

       Invariant:
       If   |- Psi ctx
       and  |- k is a debruijn index (for LF context)
       and  |- l label
       and  |- G LFctx
       then validBlock terminates with ()
       iff  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  l = l'
       and  Psi(k) = x1
       and  G == x1:A1 .. xn:An
    *)

    fun validBlock (Psi, k, (l, G)) =
      let
        fun (* GEN BEGIN FUN FIRST *) skipBlock (I.Null, k) = k (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) skipBlock (I.Decl (G', _), k) = skipBlock (G', k-1) (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) validBlock' (I.Decl (Psi, F.Block (F.CtxBlock (l', G'))), 0) =
              if (l' = l) andalso conv ((G, I.id), (G', I.id)) then ()
              else raise Error "Typecheck Error: Not a valid block" (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) validBlock' (I.Decl (Psi, F.Prim _), 0) =
              raise Error "Typecheck Error: Not a valid block" (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) validBlock' (I.Null, k) =
              raise Error "Typecheck Error: Not a valid block" (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) validBlock' (I.Decl (Psi, F.Block (F.CtxBlock (l', G'))), k) =
              validBlock' (Psi, skipBlock (G', k)) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) validBlock' (I.Decl (Psi, F.Prim (D)), k) =
              validBlock' (Psi, k-1) (* GEN END FUN BRANCH *)
    
      in
        validBlock' (Psi, k)
      end

    (* raiseSub (l:G, Psi') = s'

       Invariant:
       If   |- Psi ctx
       and  Psi |- l:G ctx
       and  Psi, l:G |- Psi' ctx
       then Psi, {G} Psi', l:G|- s' : Psi, l:G, Psi'
    *)
    fun raiseSub (G, Psi') =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val n = I.ctxLength G (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val m = I.ctxLength Psi' (* GEN END TAG OUTSIDE LET *)
    
        fun (* GEN BEGIN FUN FIRST *) args (0, a, S) = S (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) args (n', a, S) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V) = I.ctxDec (G, n') (* GEN END TAG OUTSIDE LET *)
            in
              if Subordinate.belowEq (I.targetFam V, a)
                then args (n'-1, a, I.App (I.Root (I.BVar n', I.Nil), S))
              else args (n'-1, a, S)
            end (* GEN END FUN BRANCH *)
    
        fun term m' =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V) = I.ctxDec (Psi', m') (* GEN END TAG OUTSIDE LET *)
            in
              I.Exp (I.Root (I.BVar (n+m'), args (n, I.targetFam (V), I.Nil)))
            end
    
        fun (* GEN BEGIN FUN FIRST *) raiseSub'' (0, s) = s (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) raiseSub'' (m', s) = raiseSub'' (m'-1, I.Dot (term m', s)) (* GEN END FUN BRANCH *)
    
        fun (* GEN BEGIN FUN FIRST *) raiseSub' (0, s) = raiseSub'' (m, s) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) raiseSub' (n', s) = raiseSub' (n'-1, I.Dot (I.Idx n', s)) (* GEN END FUN BRANCH *)
    
      in
        raiseSub' (n, I.Shift (n+m))
      end

    (* raiseType (l:G, L) = L'

       Invariant:
       L contains no parameter block declarations
       Each x:A in L is mapped xto  x:{G}A in L'
       L' preserves the order of L
    *)

    fun raiseType (F.CtxBlock (l, G), Psi') =
      let
        fun (* GEN BEGIN FUN FIRST *) raiseType'' (I.Null, Vn, a) = Vn (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) raiseType'' (I.Decl (G', D as I.Dec (_, V')), Vn, a) =
            if Subordinate.belowEq (I.targetFam V', a)
              then raiseType'' (G', Abstract.piDepend ((D, I.Maybe), Vn), a)
            else raiseType'' (G', Weaken.strengthenExp (Vn, I.shift), a) (* GEN END FUN BRANCH *)
        fun (* GEN BEGIN FUN FIRST *) raiseType' (Psi1, nil) = nil (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) raiseType' (Psi1, F.Prim (D as I.Dec (x, V)) :: Psi1') =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val s = raiseSub (G, Psi1) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val Vn = Whnf.normalize (V, s) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val a = I.targetFam Vn (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.Dec (x, raiseType'' (G, Vn, a)) (* GEN END TAG OUTSIDE LET *)
            in
              F.Prim (D') :: (raiseType'(I.Decl (Psi1, D),  Psi1'))
            end (* GEN END FUN BRANCH *)
          (* no case of F.Block by invariant *)
      in
        raiseType' (I.Null, Psi')
      end


    (* raiseM (B, L) = L'

       Invariant
       Each xx in F in L is mapped to xx in PI B. F in L'
       L' preserves the order of L
    *)
    fun (* GEN BEGIN FUN FIRST *) raiseM (B, nil) = nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) raiseM (B, F.MDec (xx, F) :: L) =
          F.MDec (xx, F.All (F.Block B, F)) :: raiseM (B, L) (* GEN END FUN BRANCH *)

    (* psub (k, Phi, s) = s'

       Invariant:
       If   |- Phi ctx
       and  |- Psi ctx
       and  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  Psi (k) = x1
       and  | Phi | = n
       and  s = k-i ... k. id   for i <=n
       then s' = k-n . ... k . id
    *)

    fun (* GEN BEGIN FUN FIRST *) psub (k, I.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) psub (k, I.Decl (G, _), s) =
          psub (k-1, G, I.Dot (I.Idx k, s)) (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) deltaSub (I.Null, s) = I.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) deltaSub (I.Decl (Delta, DD), s) =
          I.Decl (deltaSub (Delta, s), F.mdecSub (DD, s)) (* GEN END FUN BRANCH *)

    fun shift Delta = deltaSub (Delta, I.shift)

    fun (* GEN BEGIN FUN FIRST *) shifts (I.Null, Delta) = Delta (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) shifts (I.Decl (G, _), Delta) =
          shifts (G, shift Delta) (* GEN END FUN BRANCH *)

    fun shiftBlock (F.CtxBlock (_, G), Delta) =
      shifts (G, Delta)

    fun (* GEN BEGIN FUN FIRST *) shiftSub (I.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) shiftSub (I.Decl (G, _), s) = shiftSub (G, I.comp (I.shift, s)) (* GEN END FUN BRANCH *)

    fun shiftSubBlock (F.CtxBlock (_, G), s) =
      shiftSub (G, s)

    (* check (Psi, Delta, P, (F, s)) = ()

       Invariant:
       If   Psi'' |- F formula
       and  Psi |- s : Psi''
       and  Psi |- Delta mctx
        returns () if there exists a F',
              s.t. Psi, Delta |- P  : F'
              and  Psi |- F' = F[s] formula
       otherwise Error is raised
    *)
    fun (* GEN BEGIN FUN FIRST *) check (Psi, Delta, F.Unit, (F.True, _)) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) check (Psi, Delta, F.Rec (DD, P), F) =
          (check (Psi, I.Decl (Delta, DD), P, F)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) check (Psi, Delta, F.Lam (LD as F.Prim (I.Dec (_, V)), P),
               (F.All (F.Prim (I.Dec (_, V')), F'), s')) =
        if (Conv.conv ((V, I.id), (V', s'))) then
          check (I.Decl (Psi, LD), shift Delta,
                 P, (F', I.dot1 s'))
         else raise Error "Typecheck Error: Primitive Abstraction" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) check (Psi, Delta, F.Lam (LD as F.Block (B as F.CtxBlock (l, G)), P),
               (F.All (F.Block (F.CtxBlock (l', G')), F'), s')) =
        (if (l = l' andalso conv ((G, I.id), (G', s'))) then
           check (I.Decl (Psi, LD), shiftBlock (B, Delta),
                  P,
                  (F', F.dot1n (G, s')))
         else raise Error "Typecheck Error: Block Abstraction") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) check (Psi, Delta, F.Inx (M, P), (F.Ex (I.Dec (_, V'), F'), s')) =
          (TypeCheck.typeCheck (F.makectx Psi, (M, (I.EClo (V', s'))));
           check (Psi, Delta, P, (F', I.Dot (I.Exp (M), s')))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) check (Psi, Delta, F.Case (F.Opts O), (F', s')) =
          checkOpts (Psi, Delta, O, (F', s')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) check (Psi, Delta, F.Pair (P1, P2), (F.And (F1', F2'), s')) =
          (check(Psi, Delta, P1, (F1', s'));
           check(Psi, Delta, P2, (F2', s'))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) check (Psi, Delta, F.Let (Ds, P), (F', s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', Delta', s'') = assume (Psi, Delta, Ds) (* GEN END TAG OUTSIDE LET *)
        in
          check (extend (Psi, Psi'), extend (Delta, Delta'), P, (F', I.comp (s', s'')))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) check _ = raise Error "Typecheck Error: Term not well-typed" (* GEN END FUN BRANCH *)

    and infer (Delta, kk) = (I.ctxLookup (Delta, kk), I.id)

    (* assume (Psi, Delta, Ds) = (Psi', Delta', s')

       Invariant:
       If   |- Psi context
       and  Psi |- Delta assumptions
       and  Psi, Delta |- Decs declarations
       then |- Psi, Psi' context
       and  Psi, Psi' |- Delta, Delta' assumptions
       and  Psi, Psi' |- s' = ^|Psi'| : Psi
    *)

    and (* GEN BEGIN FUN FIRST *) assume (Psi, Delta, F.Empty) = (nil, nil, I.id) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) assume (Psi, Delta, F.Split (kk, Ds)) =
        (case infer (Delta, kk) of
          (F.MDec (name, F.Ex (D, F)), s) =>
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val LD = F.Prim (I.decSub (D, s)) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val DD = F.MDec (name, F.forSub (F, I.dot1 s)) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', Delta', s') = assume (I.Decl (Psi, LD),
                                               I.Decl (shift Delta, DD), Ds) (* GEN END TAG OUTSIDE LET *)
            in
              (LD :: Psi', F.mdecSub (DD, s') :: Delta', I.comp (I.shift, s'))
            end
        | _ => raise Error "Typecheck Error: Declaration") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) assume (Psi, Delta, F.New (B, Ds)) =
        let
          (* check B valid context block       <-------------- omission *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheck (F.makectx (I.Decl (Psi, F.Block B)), (I.Uni I.Type, I.Uni I.Kind)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', Delta', s') =  assume (I.Decl (Psi, F.Block B),
                                            shiftBlock (B, Delta), Ds) (* GEN END TAG OUTSIDE LET *)
        in
          (raiseType (B, Psi'), raiseM (B, Delta'),  s')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) assume (Psi, Delta, F.App ((kk, U), Ds)) =
        (case infer (Delta, kk) of
           (F.MDec (name, F.All (F.Prim (I.Dec (_, V)), F)), s) =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheck (F.makectx Psi, (U, I.EClo (V, s)))
                 handle TypeCheck.Error msg =>
                   raise Error (msg ^  " " ^
                                Print.expToString (F.makectx Psi, U) ^
                                " has type " ^
                                Print.expToString (F.makectx Psi,
                                                   TypeCheck.infer' (F.makectx Psi, U)) ^
                                " expected " ^
                                Print.expToString (F.makectx Psi, I.EClo (V, s))) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val DD = F.MDec (name, F.forSub (F, I.Dot (I.Exp (U), s))) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds) (* GEN END TAG OUTSIDE LET *)
             in
               (Psi', F.mdecSub (DD, s') :: Delta', s')
             end
         | (F.MDec (name, F), s) =>
             raise Error ("Typecheck Error: Declaration App" ^
                             (FunPrint.forToString (I.Null, F) ["x"]))) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) assume (Psi, Delta, F.PApp ((kk, k), Ds)) =
        (case infer (Delta, kk) of
           (F.MDec (name, F.All (F.Block (F.CtxBlock (l, G)), F)), s) =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = validBlock (Psi, k, (l, G)) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val DD = F.MDec (name, F.forSub (F, psub(k, G, s))) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds) (* GEN END TAG OUTSIDE LET *)
             in
               (Psi', F.mdecSub (DD, s') :: Delta', s')
             end
         | _ => raise Error "Typecheck Error: Declaration PApp") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) assume (Psi, Delta, F.Left (kk, Ds)) =
        (case infer (Delta, kk) of
           (F.MDec (name, F.And (F1, F2)), s) =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val DD = F.MDec (name, F.forSub (F1, s)) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds) (* GEN END TAG OUTSIDE LET *)
             in
               (Psi', F.mdecSub (DD, s') :: Delta', s')
             end
         | _ => raise Error "Typecheck Error: Declaration Left") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) assume (Psi, Delta, F.Right (kk, Ds)) =
        (case infer (Delta, kk) of
           (F.MDec (name, F.And (F1, F2)), s) =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val DD = F.MDec (name, F.forSub (F2, s)) (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds) (* GEN END TAG OUTSIDE LET *)
             in
               (Psi', F.mdecSub (DD, s') :: Delta', s')
             end
         | _ => raise Error "Typecheck Error: Declaration Left") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) assume (Psi, Delta, F.Lemma (cc, Ds)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val F.LemmaDec (names, _, F) = F.lemmaLookup cc (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val name = foldr op^ "" names (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val DD = F.MDec (SOME name, F) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds) (* GEN END TAG OUTSIDE LET *)
        in
          (Psi', F.mdecSub (DD, s') :: Delta', s')
        end (* GEN END FUN BRANCH *)


    (* checkSub (Psi1, s, Psi2) = ()

       Invariant:
       The function terminates
       iff  Psi1 |- s : Psi2
    *)
    and (* GEN BEGIN FUN FIRST *) checkSub (I.Null, I.Shift 0, I.Null) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (I.Decl (Psi, F.Prim D), I.Shift k, I.Null) =
        if k>0 then checkSub (Psi, I.Shift (k-1), I.Null)
        else raise Error "Substitution not well-typed" (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (I.Decl (Psi, F.Block (F.CtxBlock (_, G))), I.Shift k, I.Null) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val g = I.ctxLength G (* GEN END TAG OUTSIDE LET *)
        in
          if k>=g then checkSub (Psi, I.Shift (k-g), I.Null)
          else raise Error "Substitution not well-typed"
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (Psi', I.Shift k, Psi) =
          checkSub (Psi', I.Dot (I.Idx (k+1), I.Shift (k+1)), Psi) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (Psi', I.Dot (I.Idx k, s'), I.Decl (Psi, F.Prim (I.Dec (_, V2)))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val G' = F.makectx Psi' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V1) = I.ctxDec (G', k) (* GEN END TAG OUTSIDE LET *)
        in
          if Conv.conv ((V1, I.id), (V2, s')) then checkSub (Psi', s', Psi)
          else raise Error ("Substitution not well-typed \n  found: " ^
                            Print.expToString (G', V1) ^ "\n  expected: " ^
                            Print.expToString (G', I.EClo (V2, s')))
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (Psi', I.Dot (I.Exp (U), s'), I.Decl (Psi, F.Prim (I.Dec (_, V2)))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val G' = F.makectx Psi' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TypeCheck.typeCheck (G', (U, I.EClo (V2, s'))) (* GEN END TAG OUTSIDE LET *)
        in
          checkSub (Psi', s', Psi)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkSub (Psi', s as I.Dot (I.Idx k, _), I.Decl (Psi, F.Block (F.CtxBlock (l1, G)))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (F.Block (F.CtxBlock (l2, G')), w) = F.lfctxLFDec (Psi', k) (* GEN END TAG OUTSIDE LET *)
          (* check that l1 = l2     <----------------------- omission *)
      
          (* checkSub' ((G', w), s, G, m) = ()
          *)
      
          fun (* GEN BEGIN FUN FIRST *) checkSub' ((I.Null, w1), s1, I.Null, _) = s1 (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) checkSub' ((I.Decl (G', I.Dec (_, V')), w1), I.Dot (I.Idx k', s1),
                         I.Decl (G, I.Dec (_, V)), m) =
              if k' = m then
                if Conv.conv ((V', w1), (V, s1)) then
                  checkSub' ((G', I.comp (w1, I.shift)), s1, G, m + 1)
                else raise Error "ContextBlock assignment not well-typed"
              else raise Error "ContextBlock assignment out of order" (* GEN END FUN BRANCH *)
        in
          checkSub (Psi', checkSub' ((G', w), s, G, k), Psi)
        end (* GEN END FUN BRANCH *)


    (* checkOpts (Psi, Delta, (O, s) *)

    and (* GEN BEGIN FUN FIRST *) checkOpts (Psi, Delta, nil, _) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkOpts (Psi, Delta, (Psi', t, P)::O, (F', s')) =
          (checkSub (Psi', t, Psi);
           check (Psi', deltaSub (Delta, t), P, (F', I.comp (s', t)));
           (* [Psi' strict in  t] <------------------------- omission*)
           checkOpts(Psi, Delta, O, (F', s'))) (* GEN END FUN BRANCH *)

    fun checkRec (P, T) =
      check (I.Null, I.Null, P, (T, I.id))


    fun (* GEN BEGIN FUN FIRST *) isFor (G, F.All (F.Prim D, F)) =
          ((TypeCheck.checkDec (G, (D, I.id));
            isFor (I.Decl (G, D), F))
           handle TypeCheck.Error msg => raise Error msg) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isFor (G, F.All (F.Block (F.CtxBlock (_, G1)), F)) =
          isForBlock (G, F.ctxToList G1, F) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isFor (G, F.Ex (D, F)) =
          ((TypeCheck.checkDec (G, (D, I.id));
            isFor (I.Decl (G, D), F))
           handle TypeCheck.Error msg => raise Error msg) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isFor (G, F.True) = () (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) isFor (G, F.And (F1, F2)) =
          (isFor (G, F1); isFor (G, F2)) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) isForBlock (G, nil, F) = isFor (G, F) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isForBlock (G, D :: G1, F) = isForBlock (I.Decl (G, D), G1, F) (* GEN END FUN BRANCH *)





    fun (* GEN BEGIN FUN FIRST *) checkTags' (V, F.Ex _) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkTags' (I.Pi (_, V), F.All (_, F)) =
          checkTags' (V, F) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkTags' _ = raise Domain (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) checkTags (I.Null, I.Null) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkTags (I.Decl (G, I.Dec (_, V)), I.Decl (B, T)) =
        (checkTags (G, B);
         case T
           of S.Lemma (_) =>  ()
            | _ => ()) (* GEN END FUN BRANCH *)


    (* isState (S) = ()

       Invariant:

       Side effect:
       If it doesn't hold that |- S state, then exception Error is raised

       Remark: Function is only partially implemented
    *)
    fun isState (S.State (n, (G, B), (IH, OH), d, O, H, F)) =
        (TypeCheck.typeCheckCtx G;
         checkTags (G, B);
         if (not (Abstract.closedCtx G)) then raise Error "State context not closed!" else ();
         map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (n', F') => (isFor (G, F')
             (* ;          TextIO.print ("Checked: " ^ (FunPrint.Formatter.makestring_fmt (FunPrint.formatForBare (G, F'))) ^ "\n") *) ) (* GEN END FUNCTION EXPRESSION *)) H;
         (* n' is not checked for consistency   --cs *)
         isFor (G, F))



  in
    (* GEN BEGIN TAG OUTSIDE LET *) val isFor = isFor (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val check = checkRec (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val checkSub = checkSub (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val isState = isState (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *) (* Signature FUNTYPECHECK *)
