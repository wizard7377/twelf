(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

let recctor Interactive
  (module Global : GLOBAL
   (*! module IntSyn' : INTSYN !*)
   (*! module Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   module State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   module Formatter : FORMATTER
   module Trail : TRAIL
   module Ring : RING
   module Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   module Weaken : WEAKEN
   (*! sharing Weaken.IntSyn = IntSyn' !*)
   (* module ModeSyn : MODESYN *)
   (*! sharing ModeSyn.IntSyn = IntSyn' !*)
   module WorldSyn : WORLDSYN
   (*! sharing WorldSyn.IntSyn = IntSyn' !*)
   (*! sharing WorldSyn.Tomega = Tomega' !*)
   module Introduce : INTRODUCE
   (*! sharing Introduce.IntSyn = IntSyn' !*)
   (*! sharing Introduce.Tomega = Tomega' !*)
     sharing Introduce.State = State'
   module Elim : ELIM
   (*! sharing Elim.IntSyn = IntSyn' !*)
   (*! sharing Elim.Tomega = Tomega' !*)
     sharing Elim.State = State'
   module Split : SPLIT
   (*! sharing Split.IntSyn = IntSyn' !*)
   (*! sharing Split.Tomega = Tomega' !*)
     sharing Split.State = State'
   module FixedPoint : FIXEDPOINT
   (*! sharing FixedPoint.IntSyn = IntSyn' !*)
   (*! sharing FixedPoint.Tomega = Tomega' !*)
     sharing FixedPoint.State = State'
   module Fill : FILL
   (*! sharing Fill.IntSyn = IntSyn' !*)
   (*! sharing Fill.Tomega = Tomega' !*)
     sharing Fill.State = State')
  : INTERACTIVE =
struct
  (*! module IntSyn = IntSyn' !*)
  (*! module Tomega = Tomega' !*)
  module State = State'

  exception Error = State'.Error

  local
    module I = IntSyn
    module T = Tomega
    module S = State
    module M = ModeSyn
    module W = WorldSyn

    fun abort s =
        (print ("* " ^ s ^ "\n");
         raise Error s)

    (* this is pretty preliminary:
       I think we should just adapt the internal representation for formulas
    *)
    fun convertOneFor cid =
      let
        let V  = case I.sgnLookup cid
                   of I.ConDec (name, _, _, _, V, I.Kind) => V
                    | _ => raise Error "Type Constant declaration expected"
        let mS = case ModeTable.modeLookup cid
                   of NONE => raise Error "Mode declaration expected"
                    | SOME mS => mS

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
        fun convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n) =
            let
              let (F', F'') = convertFor' (V, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n-1)
            in
              (fun F -> T.All ((T.UDec (Weaken.strengthenDec (D, w1)), T.Explicit), F' F), F'')
            end
          | convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n) =
            let
              let (F', F'') = convertFor' (V, mS, I.comp (w1, I.shift), I.dot1 w2, n+1)
            in
              (F', T.Ex ((I.decSub (D, w2), T.Explicit), F''))
            end
          | convertFor' (I.Uni I.Type, M.Mnil, _, _, _) =
              (fun F -> F, T.True)
          | convertFor' _ = raise Error "type family must be +/- moded"

        (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)

        fun shiftPlus mS =
          let
            fun shiftPlus' (M.Mnil, n) = n
              | shiftPlus' (M.Mapp (M.Marg (M.Plus, _), mS'), n) =
                  shiftPlus' (mS', n+1)
              | shiftPlus' (M.Mapp (M.Marg (M.Minus, _), mS'), n) =
                  shiftPlus' (mS', n)
          in
            shiftPlus' (mS, 0)
          end

        let n = shiftPlus mS
        let (F, F') = convertFor' (V, mS, I.id, I.Shift n, n)
      in
        F F'
      end


    (* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)
    fun convertFor nil = raise Error "Empty theorem"
      | convertFor [a] = convertOneFor a
      | convertFor (a :: L) = T.And (convertOneFor a, convertFor L)

   (* here ends the preliminary stuff *)

    type MenuItem
    = Split     of Split.operator
    | Fill      of Fill.operator
    | Introduce of Introduce.operator
    | Fix       of FixedPoint.operator
    | Elim      of Elim.operator

    let Focus : (S.State list) ref = ref []

    let Menu : MenuItem list option ref = ref NONE


    fun SplittingToMenu (O, A) = Split O :: A

    fun initFocus () = (Focus := [])


    fun normalize () =
        (case (!Focus)
          of (S.State (W, Psi, P, F) :: Rest) =>
              (Focus := (S.State (W, Psi, T.derefPrg P, F) :: Rest))
           | _ => ())

    fun reset () =
        (initFocus ();
         Menu := NONE)

    fun format k =
        if k < 10 then (Int.toString k) ^ ".  "
        else (Int.toString k) ^ ". "

    fun menuToString () =
        let
          fun menuToString' (k, nil) = ""
            | menuToString' (k, Split O  :: M) =
              let
                let s = menuToString' (k+1, M)
              in
                 s ^ "\n  " ^ (format k) ^ (Split.menu O)
              end
            | menuToString' (k, Introduce O :: M) =
              let
                let s = menuToString' (k+1, M)
              in
                s ^ "\n  " ^ (format k) ^ (Introduce.menu O)
              end
            | menuToString' (k, Fill O :: M) =
              let
                let s = menuToString' (k+1, M)
              in
                s ^ "\n  " ^ (format k) ^ (Fill.menu O)
              end
            | menuToString' (k, Fix O :: M) =
              let
                let s = menuToString' (k+1, M)
              in
                s ^ "\n  " ^ (format k) ^ (FixedPoint.menu O)
              end
            | menuToString' (k, Elim O :: M) =
              let
                let s = menuToString' (k+1, M)
              in
                s ^ "\n  " ^ (format k) ^ (Elim.menu O)
              end
(*          | menuToString' (k, Inference O :: M,kOopt) =
              let
                let (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
              end
*)      in
          case !Menu of
            NONE => raise Error "Menu is empty"
          | SOME M =>  menuToString' (1, M)
        end


    fun printStats () =
        let
          let nopen   = 0
          let nsolved = 0
        in
          (print "Statistics:\n\n";
           print ("Number of goals : " ^ (Int.toString (nopen + nsolved)) ^"\n");
           print ("     open goals : " ^ (Int.toString (nopen)) ^ "\n");
           print ("   solved goals : " ^ (Int.toString (nsolved)) ^ "\n"))
        end

    fun printmenu () =
        (case !Focus
           of [] => abort "QED"
            | (S.State (W, Psi, P, F) :: R) =>
                  (print ("\n=======================");
                   print ("\n= META THEOREM PROVER =\n");
                   print (TomegaPrint.ctxToString (Psi));
                   print ("\n-----------------------\n");
                   print (TomegaPrint.forToString (Psi, F));
                   print ("\n-----------------------\n");
                   print (TomegaPrint.prgToString (Psi, P));
                   print ("\n-----------------------");
                   print (menuToString ());
                   print ("\n=======================\n"))
            | (S.StateLF (X as I.EVar (r, G, V, Cs)) :: R) =>
                  (print ("\n=======================");
                   print ("\n=== THEOREM PROVER ====\n");
                   print (Print.ctxToString (I.Null, G));
                   print ("\n-----------------------\n");
                   print (Print.expToString (G, V));
                   print ("\n-----------------------\n");
                   print (Print.expToString (G, X));
                   print ("\n-----------------------");
                   print (menuToString ());
                   print ("\n=======================\n")))



    fun menu () =
        (case (!Focus)
           of [] => print "Please initialize first\n"
            | (S.State (W, Psi, P, F) :: _) =>
              let
                let Xs = S.collectT P
                let F1 = map (fn (T.EVar (Psi, r, F, TC, TCs, X)) => (Names.varReset I.Null;
                                                             S.Focus (T.EVar (TomegaPrint.nameCtx Psi, r, F, TC, TCs, X), W))) Xs
                let Ys = S.collectLF P
                let F2 = map (fun Y -> S.FocusLF Y) Ys


                fun splitMenu [] = []
                  | splitMenu (operators :: l) = map Split operators @ splitMenu l

                let _ = Global.doubleCheck := true


                fun introMenu [] =  []
                  | introMenu ((SOME oper) :: l) = (Introduce oper) :: introMenu l
                  | introMenu (NONE :: l) = introMenu l

                let intro = introMenu (map Introduce.expand F1)


                let fill = foldr (fn (S, l) => l @ map (fun O -> Fill O) (Fill.expand S)) nil F2

                fun elimMenu [] = []
                  | elimMenu (operators :: l) = map Elim operators @ elimMenu l

                let elim = elimMenu (map Elim.expand F1)

                let split = splitMenu (map Split.expand F1)
              in
                Menu := SOME (intro @ split @ fill @ elim)
              end
            | (S.StateLF Y :: _) =>
              let
                let Ys = Abstract.collectEVars (I.Null, (Y, I.id), nil)
                let F2 = map (fun Y -> S.FocusLF Y) Ys
                let fill = foldr (fn (S, l) => l @ map (fun O -> Fill O) (Fill.expand S)) nil F2
              in
                Menu := SOME (fill)
              end)


    fun select k =
        let
          fun select' (k, nil) = abort ("No such menu item")
            | select' (1, Split O :: _) =
                (Timers.time Timers.splitting Split.apply) O
            | select' (1, Introduce O :: _) =
                Introduce.apply O    (* no timer yet -- cs *)
            | select' (1, Elim O :: _) =
                Elim.apply O    (* no timer yet -- cs *)
            | select' (1, Fill O :: _) =
                (Timers.time Timers.filling Fill.apply) O
            | select' (k, _ :: M) = select' (k-1, M)
        in
          (case !Menu of
            NONE => raise Error "No menu defined"
          | SOME M => (select' (k, M); normalize (); menu (); printmenu())
             handle S.Error s => ())
        end


    fun init names =
        let
          let _ = TomegaPrint.evarReset()
          let cL = map (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
          let F = convertFor cL
          let Ws = map W.lookup cL
          fun select c = (Order.selLookup c handle _ => Order.Lex [])

          let TC = Tomega.transformTC (I.Null, F, map select cL)
          (* so far omitted:  make sure that all parts of the theorem are
             declared in the same world
          *)
          let (W :: _) = Ws
          let _ = Focus :=  [S.init (F, W)]
          let P = (case (!Focus)
                     of [] => abort "Initialization of proof goal failed\n"
                   | (S.State (W, Psi, P, F) :: _) => P)
          let Xs = S.collectT P
          let F = map (fn (T.EVar (Psi, r, F, TC, TCs, X)) => (Names.varReset I.Null;
                                                    S.Focus (T.EVar (TomegaPrint.nameCtx Psi, r, F, TC, TCs, X), W))) Xs
          let [Ofix] = map (fun f -> (FixedPoint.expand (f, TC))) F
          let _ = FixedPoint.apply Ofix
          let _ = normalize ();
          let _ = menu ()
          let _ = printmenu ()
        in
          ()
        end


    (* focus n = ()

       Invariant:
       Let n be a string.
       Side effect: Focus on selected subgoal.
    *)
    fun focus n =
        (case (!Focus)
           of [] => print "Please initialize first\n"
            | (S.State (W, Psi, P, F) :: _) =>
              let
                fun findIEVar nil = raise Error ("cannot focus on " ^ n)
                  | findIEVar (Y :: Ys) =
                    if Names.evarName (T.coerceCtx Psi, Y) = n then
                       (Focus := (S.StateLF Y :: !Focus);
                        normalize ();
                        menu ();
                        printmenu ())
                    else findIEVar Ys
                fun findTEVar nil = findIEVar (S.collectLF P)
                  | findTEVar ((X as T.EVar (Psi, r, F, TC, TCs, Y)) :: Xs) =
                    if Names.evarName (T.coerceCtx Psi, Y) = n then
                      (Focus := (S.State (W, TomegaPrint.nameCtx Psi, X, F) :: !Focus);
                       normalize ();
                       menu ();
                       printmenu ())
                    else findTEVar Xs
              in
                findTEVar (S.collectT P)
              end
            | (S.StateLF (U) :: _) =>
              (* Invariant: U has already been printed, all EVars occuring
                 in U are already named.
              *)
              (case (Names.getEVarOpt n)
                 of NONE => raise Error ("cannot focus on " ^ n)
                  | SOME Y =>
                       (Focus := (S.StateLF Y :: !Focus);
                        normalize ();
                        menu ();
                        printmenu ())))


    fun return () =
      (case (!Focus)
        of [S] => if S.close S then print "[Q.E.D.]\n" else ()
         | (S :: Rest) => (Focus := Rest ; normalize (); menu (); printmenu ()))

  in
    let init = init
    let select = select
    let print = printmenu
    let stats = printStats
    let reset = reset
    let focus = focus
    let return = return
  end
end (* functor Interactive *)