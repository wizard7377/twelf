(* Meta Prover Interface *)


(* Author: Carsten Schuermann *)


module Interactive (Global : GLOBAL) (State' : STATE) (Formatter : FORMATTER) (Trail : TRAIL) (Ring : RING) (Names : NAMES) (Weaken : WEAKEN) (WorldSyn : WORLDSYN) (Introduce : INTRODUCE) (Elim : ELIM) (Split : SPLIT) (FixedPoint : FIXEDPOINT) (Fill : FILL) : INTERACTIVE = struct (*! structure IntSyn = IntSyn' !*)

(*! structure Tomega = Tomega' !*)

module State = State'
exception Error
module I = IntSyn
module T = Tomega
module S = State
module M = ModeSyn
module W = WorldSyn
let rec abort s  = (print ("* " ^ s ^ "\n"); raise (Error s))
(* this is pretty preliminary:
       I think we should just adapt the internal representation for_sml formulas
    *)

let rec convertOneFor cid  = ( (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for_sml G'
           then F'  is a formula excepting a another argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
(* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
let V = match I.sgnLookup cid with I.ConDec (name, _, _, _, V, I.Kind) -> V | _ -> raise (Error "Type Constant declaration expected") in let mS = match ModeTable.modeLookup cid with None -> raise (Error "Mode declaration expected") | Some mS -> mS in let rec convertFor' = function (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n) -> ( let (F', F'') = convertFor' (V, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n - 1) in  (fun F -> T.All ((T.UDec (Weaken.strengthenDec (D, w1)), T.Explicit), F' F), F'') ) | (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n) -> ( let (F', F'') = convertFor' (V, mS, I.comp (w1, I.shift), I.dot1 w2, n + 1) in  (F', T.Ex ((I.decSub (D, w2), T.Explicit), F'')) ) | (I.Uni I.Type, M.Mnil, _, _, _) -> (fun F -> F, T.True) | _ -> raise (Error "type family must be +/- moded") in let rec shiftPlus mS  = ( let rec shiftPlus' = function (M.Mnil, n) -> n | (M.Mapp (M.Marg (M.Plus, _), mS'), n) -> shiftPlus' (mS', n + 1) | (M.Mapp (M.Marg (M.Minus, _), mS'), n) -> shiftPlus' (mS', n) in  shiftPlus' (mS, 0) ) in let n = shiftPlus mS in let (F, F') = convertFor' (V, mS, I.id, I.Shift n, n) in  F F' )
(* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)

let rec convertFor = function [] -> raise (Error "Empty theorem") | [a] -> convertOneFor a | (a :: L) -> T.And (convertOneFor a, convertFor L)
(* here ends the preliminary stuff *)

type menuItem = Split of Split.operator | Fill of Fill.operator | Introduce of Introduce.operator | Fix of FixedPoint.operator | Elim of Elim.operator
let Focus : S.state list ref = ref []
let Menu : menuItem list option ref = ref None
let rec SplittingToMenu (O, A)  = Split O :: A
let rec initFocus ()  = (Focus := [])
let rec normalize ()  = (match (! Focus) with (S.State (W, Psi, P, F) :: Rest) -> (Focus := (S.State (W, Psi, T.derefPrg P, F) :: Rest)) | _ -> ())
let rec reset ()  = (initFocus (); Menu := None)
let rec format k  = if k < 10 then (Int.toString k) ^ ".  " else (Int.toString k) ^ ". "
let rec menuToString ()  = ( (*          | menuToString' (k, Inference O :: M,kOopt) =
              let
                val (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
              end
*)
let rec menuToString' = function (k, []) -> "" | (k, Split O :: M) -> ( let s = menuToString' (k + 1, M) in  s ^ "\n  " ^ (format k) ^ (Split.menu O) ) | (k, Introduce O :: M) -> ( let s = menuToString' (k + 1, M) in  s ^ "\n  " ^ (format k) ^ (Introduce.menu O) ) | (k, Fill O :: M) -> ( let s = menuToString' (k + 1, M) in  s ^ "\n  " ^ (format k) ^ (Fill.menu O) ) | (k, Fix O :: M) -> ( let s = menuToString' (k + 1, M) in  s ^ "\n  " ^ (format k) ^ (FixedPoint.menu O) ) | (k, Elim O :: M) -> ( let s = menuToString' (k + 1, M) in  s ^ "\n  " ^ (format k) ^ (Elim.menu O) ) in  match ! Menu with None -> raise (Error "Menu is empty") | Some M -> menuToString' (1, M) )
let rec printStats ()  = ( let nopen = 0 in let nsolved = 0 in  (print "Statistics:\n\n"; print ("Number of goals : " ^ (Int.toString (nopen + nsolved)) ^ "\n"); print ("     open goals : " ^ (Int.toString (nopen)) ^ "\n"); print ("   solved goals : " ^ (Int.toString (nsolved)) ^ "\n")) )
let rec printmenu ()  = (match ! Focus with [] -> abort "QED" | (S.State (W, Psi, P, F) :: R) -> (print ("\n======================="); print ("\n= META THEOREM PROVER =\n"); print (TomegaPrint.ctxToString (Psi)); print ("\n-----------------------\n"); print (TomegaPrint.forToString (Psi, F)); print ("\n-----------------------\n"); print (TomegaPrint.prgToString (Psi, P)); print ("\n-----------------------"); print (menuToString ()); print ("\n=======================\n")) | (S.StateLF (X) :: R) -> (print ("\n======================="); print ("\n=== THEOREM PROVER ====\n"); print (Print.ctxToString (I.Null, G)); print ("\n-----------------------\n"); print (Print.expToString (G, V)); print ("\n-----------------------\n"); print (Print.expToString (G, X)); print ("\n-----------------------"); print (menuToString ()); print ("\n=======================\n")))
let rec menu ()  = (match (! Focus) with [] -> print "Please initialize first\n" | (S.State (W, Psi, P, F) :: _) -> ( let Xs = S.collectT P in let F1 = map (fun (T.EVar (Psi, r, F, TC, TCs, X)) -> (Names.varReset I.Null; S.Focus (T.EVar (TomegaPrint.nameCtx Psi, r, F, TC, TCs, X), W))) Xs in let Ys = S.collectLF P in let F2 = map (fun Y -> S.FocusLF Y) Ys in let rec splitMenu = function [] -> [] | (operators :: l) -> map Split operators @ splitMenu l in let _ = Global.doubleCheck := true in let rec introMenu = function [] -> [] | ((Some oper) :: l) -> (Introduce oper) :: introMenu l | (None :: l) -> introMenu l in let intro = introMenu (map Introduce.expand F1) in let fill = foldr (fun (S, l) -> l @ map (fun O -> Fill O) (Fill.expand S)) [] F2 in let rec elimMenu = function [] -> [] | (operators :: l) -> map Elim operators @ elimMenu l in let elim = elimMenu (map Elim.expand F1) in let split = splitMenu (map Split.expand F1) in  Menu := Some (intro @ split @ fill @ elim) ) | (S.StateLF Y :: _) -> ( let Ys = Abstract.collectEVars (I.Null, (Y, I.id), []) in let F2 = map (fun Y -> S.FocusLF Y) Ys in let fill = foldr (fun (S, l) -> l @ map (fun O -> Fill O) (Fill.expand S)) [] F2 in  Menu := Some (fill) ))
let rec select k  = ( let rec select' = function (k, []) -> abort ("No such menu item") | (1, Split O :: _) -> (Timers.time Timers.splitting Split.apply) O | (1, Introduce O :: _) -> Introduce.apply O | (1, Elim O :: _) -> Elim.apply O | (1, Fill O :: _) -> (Timers.time Timers.filling Fill.apply) O | (k, _ :: M) -> select' (k - 1, M) in  (match ! Menu with None -> raise (Error "No menu defined") | Some M -> try (select' (k, M); normalize (); menu (); printmenu ()) with S.Error s -> ()) )
let rec init names  = ( (* so far omitted:  make sure that all parts of the theorem are
             declared in the same world
          *)
let _ = TomegaPrint.evarReset () in let cL = map (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x)))) names in let F = convertFor cL in let Ws = map W.lookup cL in let rec select c  = (try Order.selLookup c with _ -> Order.Lex []) in let TC = Tomega.transformTC (I.Null, F, map select cL) in let (W :: _) = Ws in let _ = Focus := [S.init (F, W)] in let P = (match (! Focus) with [] -> abort "Initialization of proof goal failed\n" | (S.State (W, Psi, P, F) :: _) -> P) in let Xs = S.collectT P in let F = map (fun (T.EVar (Psi, r, F, TC, TCs, X)) -> (Names.varReset I.Null; S.Focus (T.EVar (TomegaPrint.nameCtx Psi, r, F, TC, TCs, X), W))) Xs in let [Ofix] = map (fun f -> (FixedPoint.expand (f, TC))) F in let _ = FixedPoint.apply Ofix in let _ = normalize () in let _ = menu () in let _ = printmenu () in  () )
(* focus n = ()

       Invariant:
       Let n be a string.
       Side effect: Focus on selected subgoal.
    *)

let rec focus n  = (match (! Focus) with [] -> print "Please initialize first\n" | (S.State (W, Psi, P, F) :: _) -> ( let rec findIEVar = function [] -> raise (Error ("cannot focus on " ^ n)) | (Y :: Ys) -> if Names.evarName (T.coerceCtx Psi, Y) = n then (Focus := (S.StateLF Y :: ! Focus); normalize (); menu (); printmenu ()) else findIEVar Ys in let rec findTEVar = function [] -> findIEVar (S.collectLF P) | ((X) :: Xs) -> if Names.evarName (T.coerceCtx Psi, Y) = n then (Focus := (S.State (W, TomegaPrint.nameCtx Psi, X, F) :: ! Focus); normalize (); menu (); printmenu ()) else findTEVar Xs in  findTEVar (S.collectT P) ) | (S.StateLF (U) :: _) -> (* Invariant: U has already been printed, all EVars occuring
                 in U are already named.
              *)
(match (Names.getEVarOpt n) with None -> raise (Error ("cannot focus on " ^ n)) | Some Y -> (Focus := (S.StateLF Y :: ! Focus); normalize (); menu (); printmenu ())))
let rec return ()  = (match (! Focus) with [S] -> if S.close S then print "[Q.E.D.]\n" else () | (S :: Rest) -> (Focus := Rest; normalize (); menu (); printmenu ()))
let init = init
let select = select
let print = printmenu
let stats = printStats
let reset = reset
let focus = focus
let return = return
 end

(* functor Interactive *)

