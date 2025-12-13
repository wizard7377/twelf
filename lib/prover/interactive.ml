(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Interactive
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Formatter : FORMATTER
   structure Trail : TRAIL
   structure Ring : RING
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Weaken : WEAKEN
   (*! sharing Weaken.IntSyn = IntSyn' !*)
   (* structure ModeSyn : MODESYN *)
   (*! sharing ModeSyn.IntSyn = IntSyn' !*)
   structure WorldSyn : WORLDSYN
   (*! sharing WorldSyn.IntSyn = IntSyn' !*)
   (*! sharing WorldSyn.Tomega = Tomega' !*)
   structure Introduce : INTRODUCE
   (*! sharing Introduce.IntSyn = IntSyn' !*)
   (*! sharing Introduce.Tomega = Tomega' !*)
     sharing Introduce.State = State'
   structure Elim : ELIM
   (*! sharing Elim.IntSyn = IntSyn' !*)
   (*! sharing Elim.Tomega = Tomega' !*)
     sharing Elim.State = State'
   structure Split : SPLIT
   (*! sharing Split.IntSyn = IntSyn' !*)
   (*! sharing Split.Tomega = Tomega' !*)
     sharing Split.State = State'
   structure FixedPoint : FIXEDPOINT
   (*! sharing FixedPoint.IntSyn = IntSyn' !*)
   (*! sharing FixedPoint.Tomega = Tomega' !*)
     sharing FixedPoint.State = State'
   structure Fill : FILL
   (*! sharing Fill.IntSyn = IntSyn' !*)
   (*! sharing Fill.Tomega = Tomega' !*)
     sharing Fill.State = State')
  : INTERACTIVE =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error = State'.Error

  local
    structure I = IntSyn
    structure T = Tomega
    structure S = State
    structure M = ModeSyn
    structure W = WorldSyn

    fun abort s =
        (print ("* " ^ s ^ "\n");
         raise Error s)

    (* this is pretty preliminary:
       I think we should just adapt the internal representation for formulas
    *)
    fun convertOneFor cid =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val V  = case I.sgnLookup cid
                   of I.ConDec (name, _, _, _, V, I.Kind) => V
                    | _ => raise Error "Type Constant declaration expected" (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val mS = case ModeTable.modeLookup cid
                   of NONE => raise Error "Mode declaration expected"
                    | SOME mS => mS (* GEN END TAG OUTSIDE LET *)
    
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
              ((* GEN BEGIN FUNCTION EXPRESSION *) fn F => T.All ((T.UDec (Weaken.strengthenDec (D, w1)), T.Explicit), F' F) (* GEN END FUNCTION EXPRESSION *), F'')
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


    (* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)
    fun (* GEN BEGIN FUN FIRST *) convertFor nil = raise Error "Empty theorem" (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) convertFor [a] = convertOneFor a (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convertFor (a :: L) = T.And (convertOneFor a, convertFor L) (* GEN END FUN BRANCH *)

   (* here ends the preliminary stuff *)

    datatype menu_item
    = Split     of Split.operator
    | Fill      of Fill.operator
    | Introduce of Introduce.operator
    | Fix       of FixedPoint.operator
    | Elim      of Elim.operator

    (* GEN BEGIN TAG OUTSIDE LET *) val Focus : (S.state list) ref = ref [] (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val Menu : menu_item list option ref = ref NONE (* GEN END TAG OUTSIDE LET *)


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
          fun (* GEN BEGIN FUN FIRST *) menuToString' (k, nil) = "" (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Split O  :: M) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val s = menuToString' (k+1, M) (* GEN END TAG OUTSIDE LET *)
              in
                 s ^ "\n  " ^ (format k) ^ (Split.menu O)
              end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Introduce O :: M) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val s = menuToString' (k+1, M) (* GEN END TAG OUTSIDE LET *)
              in
                s ^ "\n  " ^ (format k) ^ (Introduce.menu O)
              end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Fill O :: M) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val s = menuToString' (k+1, M) (* GEN END TAG OUTSIDE LET *)
              in
                s ^ "\n  " ^ (format k) ^ (Fill.menu O)
              end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Fix O :: M) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val s = menuToString' (k+1, M) (* GEN END TAG OUTSIDE LET *)
              in
                s ^ "\n  " ^ (format k) ^ (FixedPoint.menu O)
              end (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) menuToString' (k, Elim O :: M) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val s = menuToString' (k+1, M) (* GEN END TAG OUTSIDE LET *)
              in
                s ^ "\n  " ^ (format k) ^ (Elim.menu O)
              end (* GEN END FUN BRANCH *)
    (*          | menuToString' (k, Inference O :: M,kOopt) =
              let
                val (kopt, s) = menuToString' (k+1, M, kOopt)
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
          (* GEN BEGIN TAG OUTSIDE LET *) val nopen   = 0 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val nsolved = 0 (* GEN END TAG OUTSIDE LET *)
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
                (* GEN BEGIN TAG OUTSIDE LET *) val Xs = S.collectT P (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val F1 = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (T.EVar (Psi, r, F, TC, TCs, X)) => (Names.varReset I.Null;
                                                             S.Focus (T.EVar (TomegaPrint.nameCtx Psi, r, F, TC, TCs, X), W)) (* GEN END FUNCTION EXPRESSION *)) Xs (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val Ys = S.collectLF P (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val F2 = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn Y => S.FocusLF Y (* GEN END FUNCTION EXPRESSION *)) Ys (* GEN END TAG OUTSIDE LET *)
    
    
                fun (* GEN BEGIN FUN FIRST *) splitMenu [] = [] (* GEN END FUN FIRST *)
                  | (* GEN BEGIN FUN BRANCH *) splitMenu (operators :: l) = map Split operators @ splitMenu l (* GEN END FUN BRANCH *)
    
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = Global.doubleCheck := true (* GEN END TAG OUTSIDE LET *)
    
    
                fun (* GEN BEGIN FUN FIRST *) introMenu [] =  [] (* GEN END FUN FIRST *)
                  | (* GEN BEGIN FUN BRANCH *) introMenu ((SOME oper) :: l) = (Introduce oper) :: introMenu l (* GEN END FUN BRANCH *)
                  | (* GEN BEGIN FUN BRANCH *) introMenu (NONE :: l) = introMenu l (* GEN END FUN BRANCH *)
    
                (* GEN BEGIN TAG OUTSIDE LET *) val intro = introMenu (map Introduce.expand F1) (* GEN END TAG OUTSIDE LET *)
    
    
                (* GEN BEGIN TAG OUTSIDE LET *) val fill = foldr ((* GEN BEGIN FUNCTION EXPRESSION *) fn (S, l) => l @ map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => Fill O (* GEN END FUNCTION EXPRESSION *)) (Fill.expand S) (* GEN END FUNCTION EXPRESSION *)) nil F2 (* GEN END TAG OUTSIDE LET *)
    
                fun (* GEN BEGIN FUN FIRST *) elimMenu [] = [] (* GEN END FUN FIRST *)
                  | (* GEN BEGIN FUN BRANCH *) elimMenu (operators :: l) = map Elim operators @ elimMenu l (* GEN END FUN BRANCH *)
    
                (* GEN BEGIN TAG OUTSIDE LET *) val elim = elimMenu (map Elim.expand F1) (* GEN END TAG OUTSIDE LET *)
    
                (* GEN BEGIN TAG OUTSIDE LET *) val split = splitMenu (map Split.expand F1) (* GEN END TAG OUTSIDE LET *)
              in
                Menu := SOME (intro @ split @ fill @ elim)
              end
            | (S.StateLF Y :: _) =>
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val Ys = Abstract.collectEVars (I.Null, (Y, I.id), nil) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val F2 = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn Y => S.FocusLF Y (* GEN END FUNCTION EXPRESSION *)) Ys (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val fill = foldr ((* GEN BEGIN FUNCTION EXPRESSION *) fn (S, l) => l @ map ((* GEN BEGIN FUNCTION EXPRESSION *) fn O => Fill O (* GEN END FUNCTION EXPRESSION *)) (Fill.expand S) (* GEN END FUNCTION EXPRESSION *)) nil F2 (* GEN END TAG OUTSIDE LET *)
              in
                Menu := SOME (fill)
              end)


    fun select k =
        let
          fun (* GEN BEGIN FUN FIRST *) select' (k, nil) = abort ("No such menu item") (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Split O :: _) =
                (Timers.time Timers.splitting Split.apply) O (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Introduce O :: _) =
                Introduce.apply O (* GEN END FUN BRANCH *)    (* no timer yet -- cs *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Elim O :: _) =
                Elim.apply O (* GEN END FUN BRANCH *)    (* no timer yet -- cs *)
            | (* GEN BEGIN FUN BRANCH *) select' (1, Fill O :: _) =
                (Timers.time Timers.filling Fill.apply) O (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) select' (k, _ :: M) = select' (k-1, M) (* GEN END FUN BRANCH *)
        in
          (case !Menu of
            NONE => raise Error "No menu defined"
          | SOME M => (select' (k, M); normalize (); menu (); printmenu())
             handle S.Error s => ())
        end


    fun init names =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaPrint.evarReset() (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val cL = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => valOf (Names.constLookup (valOf (Names.stringToQid x))) (* GEN END FUNCTION EXPRESSION *)) names (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val F = convertFor cL (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Ws = map W.lookup cL (* GEN END TAG OUTSIDE LET *)
          fun select c = (Order.selLookup c handle _ => Order.Lex [])
    
          (* GEN BEGIN TAG OUTSIDE LET *) val TC = Tomega.transformTC (I.Null, F, map select cL) (* GEN END TAG OUTSIDE LET *)
          (* so far omitted:  make sure that all parts of the theorem are
             declared in the same world
          *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (W :: _) = Ws (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Focus :=  [S.init (F, W)] (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val P = (case (!Focus)
                     of [] => abort "Initialization of proof goal failed\n"
                   | (S.State (W, Psi, P, F) :: _) => P) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val Xs = S.collectT P (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val F = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (T.EVar (Psi, r, F, TC, TCs, X)) => (Names.varReset I.Null;
                                                    S.Focus (T.EVar (TomegaPrint.nameCtx Psi, r, F, TC, TCs, X), W)) (* GEN END FUNCTION EXPRESSION *)) Xs (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val [Ofix] = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => (FixedPoint.expand (f, TC)) (* GEN END FUNCTION EXPRESSION *)) F (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = FixedPoint.apply Ofix (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = normalize () (* GEN END TAG OUTSIDE LET *);
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = menu () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = printmenu () (* GEN END TAG OUTSIDE LET *)
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
                fun (* GEN BEGIN FUN FIRST *) findIEVar nil = raise Error ("cannot focus on " ^ n) (* GEN END FUN FIRST *)
                  | (* GEN BEGIN FUN BRANCH *) findIEVar (Y :: Ys) =
                    if Names.evarName (T.coerceCtx Psi, Y) = n then
                       (Focus := (S.StateLF Y :: !Focus);
                        normalize ();
                        menu ();
                        printmenu ())
                    else findIEVar Ys (* GEN END FUN BRANCH *)
                fun (* GEN BEGIN FUN FIRST *) findTEVar nil = findIEVar (S.collectLF P) (* GEN END FUN FIRST *)
                  | (* GEN BEGIN FUN BRANCH *) findTEVar ((X as T.EVar (Psi, r, F, TC, TCs, Y)) :: Xs) =
                    if Names.evarName (T.coerceCtx Psi, Y) = n then
                      (Focus := (S.State (W, TomegaPrint.nameCtx Psi, X, F) :: !Focus);
                       normalize ();
                       menu ();
                       printmenu ())
                    else findTEVar Xs (* GEN END FUN BRANCH *)
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
    (* GEN BEGIN TAG OUTSIDE LET *) val init = init (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val select = select (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val print = printmenu (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val stats = printStats (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val focus = focus (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val return = return (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *) (* functor Interactive *)