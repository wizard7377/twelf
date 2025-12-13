(* Meta Theorem Prover Version 1.3 *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) MTProver (structure MTPGlobal : MTPGLOBAL
                  (*! structure IntSyn' : INTSYN !*)
                  (*! structure FunSyn : FUNSYN !*)
                  (*! sharing FunSyn.IntSyn = IntSyn' !*)
                  structure StateSyn : STATESYN
                  (*! sharing IntSyn = IntSyn' !*)
                  (*! sharing StateSyn.FunSyn = FunSyn !*)
                  structure Order : ORDER
                  (*! sharing Order.IntSyn = IntSyn' !*)
                  structure MTPInit : MTPINIT
                  (*! sharing MTPInit.FunSyn = FunSyn !*)
                    sharing MTPInit.StateSyn = StateSyn
                  structure MTPStrategy : MTPSTRATEGY
                    sharing MTPStrategy.StateSyn = StateSyn
                  structure RelFun : RELFUN
                  (*! sharing RelFun.FunSyn = FunSyn !*)
                      )
  : PROVER =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn

    (* DISCLAIMER: This functor is temporary. Its purpose is to
       connect the new prover to Twelf  (see also functor below) *)

    (* List of open states *)
    (* GEN BEGIN TAG OUTSIDE LET *) val openStates : S.state list ref = ref nil (* GEN END TAG OUTSIDE LET *)

    (* List of solved states *)
    (* GEN BEGIN TAG OUTSIDE LET *) val solvedStates : S.state list ref = ref nil (* GEN END TAG OUTSIDE LET *)

    fun (* GEN BEGIN FUN FIRST *) transformOrder' (G, Order.Arg k) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val k' = (I.ctxLength G) -k+1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (_, V) = I.ctxDec (G, k') (* GEN END TAG OUTSIDE LET *)
        in
          S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) transformOrder' (G, Order.Lex Os) =
          S.Lex (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => transformOrder' (G, O) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) transformOrder' (G, Order.Simul Os) =
          S.Simul (map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => transformOrder' (G, O) (* GEN END FUNCTION EXPRESSION *)) Os) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) transformOrder (G, F.All (F.Prim D, F), Os) =
          S.All (D, transformOrder (I.Decl (G, D), F, Os)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) transformOrder (G, F.And (F1, F2), O :: Os) =
          S.And (transformOrder (G, F1, [O]),
                 transformOrder (G, F2, Os)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) transformOrder (G, F.Ex _, [O]) = transformOrder' (G, O) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) transformOrder (G, F.True, [O]) = transformOrder' (G, O) (* GEN END FUN BRANCH *)
        (* last case: no existentials---order must be trivial *)

    fun select c = (Order.selLookup c handle _ => Order.Lex [])

    fun error s = raise Error s

    (* reset () = ()

       Invariant:
       Resets the internal state of open states/solved states
    *)
    fun reset () =
        (openStates := nil;
         solvedStates := nil)

    (* contains (L1, L2) = B'

       Invariant:
       B' holds iff L1 subset of L2 (modulo permutation)
    *)
    fun (* GEN BEGIN FUN FIRST *) contains (nil, _) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) contains (x :: L, L') =
          (List.exists ((* GEN BEGIN FUNCTION EXPRESSION *) fn x' => x = x' (* GEN END FUNCTION EXPRESSION *)) L') andalso contains (L, L') (* GEN END FUN BRANCH *)

    (* equiv (L1, L2) = B'

       Invariant:
       B' holds iff L1 is equivalent to L2 (modulo permutation)
    *)
    fun equiv (L1, L2) =
          contains (L1, L2) andalso contains (L2, L1)

    (* insertState S = ()

       Invariant:
       If S is successful prove state, S is stored in solvedStates
       else S is stored in openStates
    *)
    fun insertState S =
        openStates := S :: (! openStates)


    (* cLtoString L = s

       Invariant:
       If   L is a list of cid,
       then s is a string, listing their names
    *)
    fun (* GEN BEGIN FUN FIRST *) cLToString (nil) = "" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) cLToString (c :: nil) =
          (I.conDecName (I.sgnLookup c)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) cLToString (c :: L) =
          (I.conDecName (I.sgnLookup c)) ^ ", " ^ (cLToString L) (* GEN END FUN BRANCH *)

    (* init (k, cL) = ()

       Invariant:
       If   k is the maximal search depth
       and  cL is a complete and consistent list of cids
       then init initializes the openStates/solvedStates
       else an Error exception is raised
    *)
    fun init (k, cL as (c :: _)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = MTPGlobal.maxFill := k (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = reset () (* GEN END TAG OUTSIDE LET *);
          (* GEN BEGIN TAG OUTSIDE LET *) val cL' = Order.closure c
                    handle Order.Error _ => cL (* GEN END TAG OUTSIDE LET *)  (* if no termination ordering given! *)
          (* GEN BEGIN TAG OUTSIDE LET *) val F = RelFun.convertFor cL (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val O = transformOrder (I.Null, F, map select cL) (* GEN END TAG OUTSIDE LET *)
    
        in
          if equiv (cL, cL')
            then List.app ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => insertState S (* GEN END FUNCTION EXPRESSION *)) (MTPInit.init (F, O))
          else raise Error ("Theorem by simultaneous induction not correctly stated:"
                             ^ "\n            expected: " ^ (cLToString cL'))
        end

    (* auto () = ()

       Invariant:
       Solves as many States in openStates
       as possible.
    *)
    fun auto () =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Open, solvedStates') = MTPStrategy.run (!openStates)
             handle Splitting.Error s => error ("Splitting Error: " ^ s)
                  | Filling.Error s => error ("Filling Error: " ^ s)
                  | Recursion.Error s => error ("Recursion Error: " ^ s)
                  | Filling.TimeOut =>  error ("A proof could not be found -- Exceeding Time Limit\n") (* GEN END TAG OUTSIDE LET *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = openStates := Open (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = solvedStates := (!solvedStates) @ solvedStates' (* GEN END TAG OUTSIDE LET *)
        in
          if (List.length (!openStates)) > 0 then
            raise Error ("A proof could not be found")
          else ()
        end


    fun print () = ()
    fun install _ = ()

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val init = init (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val auto = auto (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val print = print (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val install = install (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *) (* functor MTProver *)



functor (* GEN BEGIN FUNCTOR DECL *) CombiProver (structure MTPGlobal : MTPGLOBAL
                     (*! structure IntSyn' : INTSYN !*)
                     structure ProverOld : PROVER
                     (*! sharing ProverOld.IntSyn = IntSyn' !*)
                     structure ProverNew : PROVER
                     (*! sharing ProverNew.IntSyn = IntSyn' !*)
                       )
  : PROVER =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  fun he f = f () handle ProverNew.Error s => raise Error s
                        | ProverOld.Error s => raise Error s

  local
    fun init Args =
      he ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => case !(MTPGlobal.prover)
                     of MTPGlobal.New => ProverNew.init Args
                      | MTPGlobal.Old => ProverOld.init Args (* GEN END FUNCTION EXPRESSION *))

    fun auto Args =
      he ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => case !(MTPGlobal.prover)
                        of MTPGlobal.New => ProverNew.auto Args
                         | MTPGlobal.Old => ProverOld.auto Args (* GEN END FUNCTION EXPRESSION *))

    fun print Args =
      he ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => case !(MTPGlobal.prover)
                        of MTPGlobal.New => ProverNew.print Args
                         | MTPGlobal.Old => ProverOld.print Args (* GEN END FUNCTION EXPRESSION *))

    fun install Args =
      he ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => case !(MTPGlobal.prover)
                        of MTPGlobal.New => ProverNew.install Args
                         | MTPGlobal.Old => ProverOld.install Args (* GEN END FUNCTION EXPRESSION *))
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val init = init (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val auto = auto (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val print = print (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val install = install (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *) (* functor CombiProver *)
