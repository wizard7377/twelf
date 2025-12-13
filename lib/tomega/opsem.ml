(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

functor (* GEN BEGIN FUNCTOR DECL *) Opsem ( structure Whnf : WHNF
               structure Abstract : ABSTRACT
               structure Subordinate : SUBORDINATE
               structure TomegaTypeCheck : TOMEGATYPECHECK
               structure TomegaPrint : TOMEGAPRINT
               structure Unify : UNIFY
                   ) : OPSEM =
struct
  structure T = Tomega
  structure I = IntSyn
  structure S = Subordinate
  structure A = Abstract

  exception Error of string
  exception Abort



(*  local -- removed ABP 1/19/03 *)

  exception NoMatch

(*
 matchPrg is used to see if two values can be 'unified' for
   purpose of matching case

 matchPrg (Psi, P1, P2) = ()

    Invariant:
    If P1 has no EVARs and P2 possibly does.
    and Psi  |- P1 :: F
    and Psi |- P1 value
    and Psi |- P2 :: F
    and Psi |- P2 value
     then if Psi |- P1 == P2 matchPrg terminates
       otherwise exception NoMatch is raised
*)
    fun matchPrg (Psi, P1, P2) =
      matchVal (Psi, (P1, T.id), T.normalizePrg (P2, T.id))
      (* ABP -- normalizePrg invariant does not state what happens to non-free EVArs,
       and there are some embedded under PClo... *)

    and (* GEN BEGIN FUN FIRST *) matchVal (Psi, (T.Unit, _), T.Unit) = () (* GEN END FUN FIRST *)

      | (* GEN BEGIN FUN BRANCH *) matchVal (Psi, (T.PairPrg (P1, P1'), t1), T.PairPrg (P2, P2')) =
         (matchVal (Psi, (P1, t1), P2);
          matchVal (Psi, (P1', t1), P2')) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchVal (Psi, (T.PairBlock (B1, P1), t1), T.PairBlock (B2, P2)) =
         (matchVal (Psi, (P1, t1), P2);
          Unify.unifyBlock (T.coerceCtx Psi, I.blockSub (B1, T.coerceSub t1), B2)
          handle Unify.Unify _ => raise NoMatch) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchVal (Psi, (T.PairExp (U1, P1), t1), T.PairExp (U2, P2)) =
         (matchVal (Psi, (P1, t1), P2);
          Unify.unify (T.coerceCtx Psi, (U1, T.coerceSub t1), (U2, I.id))
          handle Unify.Unify _ => raise NoMatch) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchVal (Psi, (T.PClo (P, t1'), t1), Pt) =
          matchVal (Psi, (P, T.comp (t1', t1)), Pt) (* GEN END FUN BRANCH *)

      (* Added by ABP *)

      | (* GEN BEGIN FUN BRANCH *) matchVal (Psi, (P',t1), T.PClo(T.PClo (P, t2), t3)) =
         (* ABP -- Do we need this? I added it *)
         matchVal (Psi, (P',t1), T.PClo(P, T.comp (t2, t3))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchVal (Psi, (P',t1), T.PClo(T.EVar (_, r as ref NONE, _, _, _, _), t2)) =
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val iw = T.invertSub t2 (* GEN END TAG OUTSIDE LET *)
         in
           (* ABP -- just make sure this is right *)
           r := SOME (T.PClo (P', T.comp(t1, iw)))
         end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchVal (Psi, (P', t1), T.EVar (_, r as ref NONE, _, _, _, _)) =
         r := SOME (T.PClo (P', t1)) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchVal (Psi, (V,t), T.EVar ((D, r as ref (SOME P), F, _, _, _))) =
         (* ABP -- this should never occur, since we normalized it to start *)
         matchVal (Psi, (V,t), P) (* GEN END FUN BRANCH *)

     | (* GEN BEGIN FUN BRANCH *) matchVal _ = raise NoMatch (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) append (G1, I.Null) = G1 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) append (G1, I.Decl (G2, D)) = I.Decl (append (G1, G2), D) (* GEN END FUN BRANCH *)

(* raisePrg is used in handling of NEW construct
   raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
*)
and (* GEN BEGIN FUN FIRST *) raisePrg (Psi, G, T.Unit) = T.Unit (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) raisePrg (Psi, G, T.PairPrg (P1, P2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val P1' = raisePrg (Psi, G, P1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val P2' = raisePrg (Psi, G, P2) (* GEN END TAG OUTSIDE LET *)
        in
          T.PairPrg (P1', P2')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) raisePrg (Psi, G, T.PairExp (U, P)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V = TypeCheck.infer' (append (T.coerceCtx Psi, G), U) (* GEN END TAG OUTSIDE LET *)
         (* this is a real time sink, it would be much better if we did not have to
      compute the type information of U,
      more thought is required
         *)
          (* GEN BEGIN TAG OUTSIDE LET *) val w = S.weaken (G, I.targetFam V) (* GEN END TAG OUTSIDE LET *)
                                                   (* G  |- w  : G'    *)
          (* GEN BEGIN TAG OUTSIDE LET *) val iw = Whnf.invert w (* GEN END TAG OUTSIDE LET *)                    (* G' |- iw : G     *)
          (* GEN BEGIN TAG OUTSIDE LET *) val G' = Whnf.strengthen (iw, G) (* GEN END TAG OUTSIDE LET *)        (* Psi0, G' |- B'' ctx *)
      
          (* GEN BEGIN TAG OUTSIDE LET *) val U' = A.raiseTerm (G', I.EClo (U, iw)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val P' = raisePrg (Psi, G, P) (* GEN END TAG OUTSIDE LET *)
        in
          T.PairExp (U', P')
        end (* GEN END FUN BRANCH *)



   (* evalPrg (Psi, (P, t)) = V

       Invariant:
       If   Psi' |- P :: F
       and  Psi |- t :: Psi'
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- P[t] evalsto V
       and  Psi |- F[t] == F'
    *)
    and (* GEN BEGIN FUN FIRST *) evalPrg (Psi, (T.Unit, t)) = T.Unit (* GEN END FUN FIRST *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.PairExp (M, P), t))  =
          T.PairExp (I.EClo (M, T.coerceSub t), evalPrg (Psi, (P, t))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.PairBlock (B, P), t)) =
          T.PairBlock (I.blockSub (B, T.coerceSub t), evalPrg (Psi, (P, t))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.PairPrg (P1, P2), t)) =
          T.PairPrg (evalPrg (Psi, (P1, t)), evalPrg (Psi, (P2, t))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.Redex (P, S), t)) =
          evalRedex (Psi, evalPrg (Psi, (P, t)), (S, t)) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.Var k, t)) =
          (case T.varSub (k, t)
            of T.Prg P =>  evalPrg (Psi, (P, T.id))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.Const lemma, t)) =
            evalPrg (Psi, (T.lemmaDef lemma, t)) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.Lam (D as T.UDec (I.BDec _), P), t)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val D' = T.decSub (D, t) (* GEN END TAG OUTSIDE LET *)
          in
            T.Lam (D', evalPrg (I.Decl (Psi, D'), (P, T.dot1 t)))
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.Lam (D, P), t)) =
          T.Lam (T.decSub (D, t), T.PClo (P, T.dot1 t)) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (P' as T.Rec (D, P), t)) =
         evalPrg (Psi, (P, T.Dot (T.Prg (T.PClo (P', t)), t))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.PClo (P, t'), t)) =
          evalPrg (Psi, (P, T.comp (t', t))) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.Case (T.Cases O), t')) =
          (* this is ugly.
           * don't do reverse *)
         (* reverse list O, so it looks at the
           cases in the same order it is printed
           *)
          match (Psi, t', T.Cases (rev O)) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.EVar (D, r as ref (SOME P), F, _, _, _), t)) =
          evalPrg (Psi, (P, t)) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.Let (D, P1, P2), t)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val V = evalPrg (Psi, (P1, t)) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val V' = evalPrg (Psi, (P2, T.Dot (T.Prg V, t))) (* GEN END TAG OUTSIDE LET *)
          in
            V'
          end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.New (T.Lam (D, P)), t)) =
           let
             (* GEN BEGIN TAG OUTSIDE LET *) val D' = T.decSub (D, t) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val T.UDec (D'') = D' (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val D''' = T.UDec (Names.decName (T.coerceCtx Psi, D'')) (* GEN END TAG OUTSIDE LET *)  (* unnecessary naming, remove later --cs *)
             (* GEN BEGIN TAG OUTSIDE LET *) val V = evalPrg (I.Decl (Psi, D'''), (P, T.dot1 t)) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val B = T.coerceCtx (I.Decl (I.Null, D''')) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val (G, t') = T.deblockify B (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val newP = raisePrg (Psi, G, T.normalizePrg (V, t')) (* GEN END TAG OUTSIDE LET *)
           in
             newP
           end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.Box (W, P), t)) =
           evalPrg (Psi, (P, t)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) evalPrg (Psi, (T.Choose P, t)) =
           let
      
             (* This function was imported from cover.fun   -- cs Thu Mar 20 11:47:06 2003 *)
      
             (* substtospine' (s, G, T) = S @ T
                If   G' |- s : G
                then G' |- S : {{G}} a >> a  for arbitrary a
                    {{G}} erases void declarations in G
              *)
             fun (* GEN BEGIN FUN FIRST *) substToSpine' (I.Shift(n), I.Null, T) = T (* GEN END FUN FIRST *)
               | (* GEN BEGIN FUN BRANCH *) substToSpine' (I.Shift(n), G as I.Decl _, T) =
                   substToSpine' (I.Dot (I.Idx (n+1), I.Shift(n+1)), G, T) (* GEN END FUN BRANCH *)
               | (* GEN BEGIN FUN BRANCH *) substToSpine' (I.Dot(I.Exp(U),s), I.Decl(G,V), T) =
                   substToSpine' (s, G, T.AppExp (U, T)) (* GEN END FUN BRANCH *)
               | (* GEN BEGIN FUN BRANCH *) substToSpine' (I.Dot(I.Idx(n),s), I.Decl(G,I.Dec(_,V)), T) =
                   (* Eta-expand *)
                   let
                     (* GEN BEGIN TAG OUTSIDE LET *) val (Us,_) = Whnf.whnfEta ((I.Root (I.BVar(n), I.Nil), I.id), (V, I.id)) (* GEN END TAG OUTSIDE LET *)
                   in
                     substToSpine' (s, G, T.AppExp (I.EClo Us, T))
                   end (* GEN END FUN BRANCH *)
      
      
      
             fun (* GEN BEGIN FUN FIRST *) choose (k, I.Null) = raise Abort (* GEN END FUN FIRST *)
               | (* GEN BEGIN FUN BRANCH *) choose (k, I.Decl (Psi', T.PDec _)) =
                   choose (k+1, Psi') (* GEN END FUN BRANCH *)
               | (* GEN BEGIN FUN BRANCH *) choose (k, I.Decl (Psi', T.UDec (I.Dec _))) =
                   choose (k+1, Psi') (* GEN END FUN BRANCH *)
               | (* GEN BEGIN FUN BRANCH *) choose (k, I.Decl (Psi', T.UDec (I.BDec (_, (l1, s1))))) =
                   let
                     (* GEN BEGIN TAG OUTSIDE LET *) val (Gsome, Gpi) = I.constBlock l1 (* GEN END TAG OUTSIDE LET *)
                     (* GEN BEGIN TAG OUTSIDE LET *) val S = substToSpine' (s1, Gsome, T.AppBlock (I.Bidx k, T.Nil)) (* GEN END TAG OUTSIDE LET *)
                   in
                     evalPrg (Psi, (T.Redex (T.PClo (P, t), S), T.id)) handle Abort => choose (k+1, Psi')
                   end (* GEN END FUN BRANCH *)
      
           in
             choose (1, Psi)
           end (* GEN END FUN BRANCH *)





   (* other cases should not occur -cs *)


 (* match is used to handle Case statements
  match (Psi, t1, O) = V

       Invariant:
       If   Psi |- t1 :: Psi''
       and  Psi'' |- O :: F
       and  |- Psi ctx[block]
       then if t1 matches O then Psi |- t ~ O evalPrgs to W
            otherwise exception NoMatch is raised.
    *)

    and (* GEN BEGIN FUN FIRST *) match (Psi, t1, T.Cases ((Psi', t2, P) :: C)) =
        let
          (* val I.Null = Psi *)
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createVarSub (Psi, Psi') (* GEN END TAG OUTSIDE LET *) (* Psi |- t : Psi' *)
                                          (* Psi' |- t2 . shift(k) : Psi'' *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = T.comp (t2, t) (* GEN END TAG OUTSIDE LET *)
        in
          (* Note that since we are missing the shift(k), it is possible
           * that t' has extra DOTs in there that weren't removed *)
          ( matchSub (Psi, t1, t');
           evalPrg (Psi, (P, (*T.normalizeSub*) t)))
          handle NoMatch => match (Psi, t1, T.Cases C)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) match (Psi, t1, T.Cases (nil)) = raise Abort (* GEN END FUN BRANCH *)

      (* What do you want to do if it doesn't match anything *)
      (* can't happen when total function - ABP *)
      (* | match (Psi, t1, T.Cases Nil) = raise Domain  *)


    (* createVarSub (Psi, Psi') = t

       Invariant:
       If   |- Psi ctx[block]
       and  |- Psi' ctx
       then Psi |- t :: Psi'
    *)
    and (* GEN BEGIN FUN FIRST *) createVarSub (Psi, I.Null) = T.Shift(I.ctxLength(Psi)) (* GEN END FUN FIRST *)

      | (* GEN BEGIN FUN BRANCH *) createVarSub (Psi, Psi'' as I.Decl (Psi', T.PDec (name, F, NONE, NONE))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createVarSub (Psi, Psi') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val t' = T.Dot (T.Prg (T.newEVarTC (Psi, T.forSub(F,t), NONE, NONE)), t) (* GEN END TAG OUTSIDE LET *)
        in
          t'
        end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) createVarSub (Psi, I.Decl (Psi', T.UDec (I.Dec (name, V)))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createVarSub (Psi, Psi') (* GEN END TAG OUTSIDE LET *)
        in
      
          T.Dot (T.Exp (I.EVar (ref NONE, T.coerceCtx Psi, I.EClo (V, T.coerceSub t), ref [])), t)
        end (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) createVarSub (Psi, I.Decl (Psi', T.UDec (I.BDec (name, (cid, s))))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val t = createVarSub (Psi, Psi') (* GEN END TAG OUTSIDE LET *)
        in
          T.Dot (T.Block (I.LVar (ref NONE, I.id, (cid, I.comp (s,  T.coerceSub t)))), t)
        end (* GEN END FUN BRANCH *)


 (* matchSub (t1, t2) = ()

       Invariant:
       If   Psi  |- t1 :: Psi'
       and  Psi  |- t2 :: Psi'
       and  Psi  |- t1 == t2 :: Psi'
       and  |- Psi ctx [block]
       then function returns ()
            otherwise exception NoMatch is raised
    *)

    and (* GEN BEGIN FUN FIRST *) matchSub (Psi, _, T.Shift _) = () (* GEN END FUN FIRST *) (* By Invariant *)
      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Shift n, t as T.Dot _) =  matchSub (Psi, T.Dot (T.Idx (n+1), T.Shift (n+1)), t) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Exp U2, t2)) =
          (matchSub (Psi, t1, t2);
           Unify.unify (T.coerceCtx Psi, (U1, I.id), (U2, I.id)) handle Unify.Unify s => raise NoMatch) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Idx k, t2)) =
          ( matchSub (Psi, t1, t2);
           Unify.unify (T.coerceCtx Psi, (U1, I.id), (I.Root (I.BVar k, I.Nil), I.id)) handle Unify.Unify _ => raise NoMatch) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Dot (T.Idx k, t1), T.Dot (T.Exp U2, t2)) =
          ( matchSub (Psi, t1, t2);
           Unify.unify (T.coerceCtx Psi, (I.Root (I.BVar k, I.Nil), I.id), (U2, I.id)) handle Unify.Unify _ => raise NoMatch ) (* GEN END FUN BRANCH *)


      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Prg P2, t2)) =
          ( matchSub (Psi, t1, t2);
           matchPrg (Psi, P1, P2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Idx k, t2)) =
          (matchSub (Psi, t1, t2);
           matchPrg (Psi, P1, T.Var k)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Dot (T.Idx k, t1), T.Dot (T.Prg P2, t2)) =
          (matchSub (Psi, t1, t2);
           matchPrg (Psi, T.Var k, P2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Dot (T.Idx k1, t1), T.Dot (T.Idx k2, t2)) =
          (if k1 = k2 then matchSub (Psi, t1, t2) else raise NoMatch) (* GEN END FUN BRANCH *)

      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Dot (T.Idx k, t1), T.Dot (T.Block (I.LVar (r, s1, (c,s2))), t2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val s1' = Whnf.invert s1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = r := SOME (I.blockSub (I.Bidx k, s1')) (* GEN END TAG OUTSIDE LET *)
        in
          matchSub (Psi, t1, t2)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) matchSub (Psi, T.Dot (T.Block (B), t1), T.Dot (T.Block (I.LVar (r, s1, (c,s2))), t2)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val s1' = Whnf.invert s1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = r := SOME (I.blockSub (B, s1')) (* GEN END TAG OUTSIDE LET *)
        in
           matchSub (Psi, t1, t2)
        end (* GEN END FUN BRANCH *)

    (* evalRedex (Psi, V, (S, t)) = V'

       Invariant:
       If   Psi  |- V :: F1
       and  Psi' |- S :: F2 > F3
       and  Psi  |- t :: Psi'
       and  Psi' |- F1 == F2[t]
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- V . (S[t]) evalsto V''
       then Psi |- V' == V'' : F3[t]
    *)

  and (* GEN BEGIN FUN FIRST *) evalRedex (Psi, V, (T.Nil, _)) = V (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) evalRedex (Psi, V, (T.SClo (S, t1), t2)) =
          evalRedex (Psi, V, (S, T.comp (t1, t2))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) evalRedex (Psi, T.Lam (T.UDec (I.Dec (_, A)), P'), (T.AppExp (U, S), t)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val V = evalPrg (Psi, (P', T.Dot (T.Exp (I.EClo (U, T.coerceSub t)), T.id))) (* GEN END TAG OUTSIDE LET *)
      in
        evalRedex (Psi, V, (S, t))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) evalRedex (Psi, T.Lam (T.UDec _, P'), (T.AppBlock (B, S), t)) =
          evalRedex (Psi, evalPrg (Psi, (P', T.Dot (T.Block (I.blockSub (B, T.coerceSub t)), T.id))), (S, t)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) evalRedex (Psi, T.Lam (T.PDec _, P'), (T.AppPrg (P, S), t)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val V = evalPrg (Psi, (P, t)) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val V' = evalPrg (Psi, (P', T.Dot (T.Prg V, T.id))) (* GEN END TAG OUTSIDE LET *)
          in
            evalRedex (Psi, V', (S, t))
          end (* GEN END FUN BRANCH *)


    (* topLevel (Psi, d, (P, t))

       Invariant:
       Psi |- t : Psi'
       Psi' |- P :: F
       d = | Psi' |

    *)
    fun (* GEN BEGIN FUN FIRST *) topLevel (Psi, d, (T.Unit, t)) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) topLevel (Psi, d, (T.Let (D', P1, T.Case Cs), t)) =
        (* lf value definition *)
        let
          (* printLF (G, s, G') k = ()
             Invariant:
             G |- s : G'
          *)
      
          fun (* GEN BEGIN FUN FIRST *) printLF (_, _, _) 0 = () (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) printLF (G, I.Dot (I.Exp U, s'), I.Decl (G', I.Dec (SOME name, V))) k =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = printLF (G, s', G') (k-1) (* GEN END TAG OUTSIDE LET *)
              in
                print ("def " ^ name ^ " = "  ^ (Print.expToString (G, U))
                       ^ " : " ^ (Print.expToString (G, I.EClo (V, s'))) ^ "\n")
              end (* GEN END FUN BRANCH *)
      
          fun match (Psi, t1, T.Cases ((Psi', t2, P) :: C)) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val t = createVarSub (Psi, Psi') (* GEN END TAG OUTSIDE LET *) (* Psi |- t : Psi' *)
                                                 (* Psi' |- t2 . shift(k) : Psi'' *)
                (* GEN BEGIN TAG OUTSIDE LET *) val t' = T.comp (t2, t) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val m = I.ctxLength Psi' (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = matchSub (Psi, t1, t') (* GEN END TAG OUTSIDE LET *);
                (* GEN BEGIN TAG OUTSIDE LET *) val t'' = (* T.normalizeSub *) t (* GEN END TAG OUTSIDE LET *)  (* Psi |- t'' : Psi' *)
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = printLF (T.coerceCtx Psi, T.coerceSub t'', T.coerceCtx Psi') (m-d) (* GEN END TAG OUTSIDE LET *)
              in
                topLevel (Psi, m, (P, t''))
              end
          (* GEN BEGIN TAG OUTSIDE LET *) val V = evalPrg (Psi, (P1, t)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = match (Psi, T.Dot (T.Prg V, t), Cs) (* GEN END TAG OUTSIDE LET *)
        in
          V'
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) topLevel (Psi, d, (T.Let (D,  T.Lam (D' as T.UDec (I.BDec (SOME name, (cid, s))), P1), P2), t)) =
        (* new declaration *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = print ("new " ^ name ^ "\n") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val D'' = T.decSub (D', t) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = topLevel (I.Decl (Psi, D''), d+1, (P1, T.dot1 t)) (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) topLevel (Psi, d, (T.Let (D, P1, P2), t)) =
        (* function definition *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val T.PDec (SOME name, F, _, _) = D (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V = evalPrg (Psi, (P1, t)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = print ("val " ^ name ^ " = " ^ TomegaPrint.prgToString (Psi, V) ^ " :: " ^ TomegaPrint.forToString (Psi, F) ^ "\n") (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val V' = topLevel (Psi, d+1, (P2, T.Dot (T.Prg V, t))) (* GEN END TAG OUTSIDE LET *)
        in
          V'
        end (* GEN END FUN BRANCH *)

  (* in -- removed local *)
    (* GEN BEGIN TAG OUTSIDE LET *) val evalPrg = (* GEN BEGIN FUNCTION EXPRESSION *) fn P => evalPrg (I.Null, (P, T.id)) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val topLevel = (* GEN BEGIN FUNCTION EXPRESSION *) fn P => topLevel (I.Null, 0, (P, T.id)) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)

  (* end -- removed local *)

end (* GEN END FUNCTOR DECL *)




