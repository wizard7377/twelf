Interactive  Global GLOBAL    State' STATE    Formatter FORMATTER    Trail TRAIL    Ring RING    Names NAMES    Weaken WEAKEN    WorldSyn WORLDSYN    Introduce INTRODUCE    Introduce State  State'   Elim ELIM    Elim State  State'   Split SPLIT    Split State  State'   FixedPoint FIXEDPOINT    FixedPoint State  State'   Fill FILL    Fill State  State'    INTERACTIVE  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
module exception module module module module module let rec aborts (print ("* " ^ s ^ "\n"); raise (error s))(* this is pretty preliminary:
       I think we should just adapt the internal representation for formulas
    *)
let rec convertOneForcid let let  inlet  in(* convertFor' (V, mS, w1, w2, n) = (F', F'')

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
let rec convertFor'(pi ((d,  , _),  , v),  , mapp (marg (plus,  , _),  , mS),  , w1,  , w2,  , n) let let  in in (fun f -> all ((uDec (strengthenDec (d,  , w1)),  , explicit),  , f' f),  , f'') convertFor'(pi ((d,  , _),  , v),  , mapp (marg (minus,  , _),  , mS),  , w1,  , w2,  , n) let let  in in (f',  , ex ((decSub (d,  , w2),  , explicit),  , f'')) convertFor'(uni type,  , mnil,  , _,  , _,  , _) (fun f -> f,  , true) convertFor'_ raise (error "type family must be +/- moded")(* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
let rec shiftPlusmS let let rec shiftPlus'(mnil,  , n) n shiftPlus'(mapp (marg (plus,  , _),  , mS'),  , n) shiftPlus' (mS',  , n + 1) shiftPlus'(mapp (marg (minus,  , _),  , mS'),  , n) shiftPlus' (mS',  , n) in shiftPlus' (mS,  , 0)let  inlet  in in f f'(* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)
let rec convertFornil raise (error "Empty theorem") convertFor[a] convertOneFor a convertFor(a :: l) and (convertOneFor a,  , convertFor l)(* here ends the preliminary stuff *)
type MenuItemlet  inlet  inlet rec splittingToMenu(o,  , a) split o :: alet rec initFocus() (focus := [])let rec normalize() (match (! focus) with (state (w,  , psi,  , p,  , f) :: rest) -> (focus := (state (w,  , psi,  , derefPrg p,  , f) :: rest)) _ -> ())let rec reset() (initFocus (); menu := nONE)let rec formatk if k < 10 then (toString k) ^ ".  " else (toString k) ^ ". "let rec menuToString() let let rec menuToString'(k,  , nil) "" menuToString'(k,  , split o :: m) let let  in in s ^ "\n  " ^ (format k) ^ (menu o) menuToString'(k,  , introduce o :: m) let let  in in s ^ "\n  " ^ (format k) ^ (menu o) menuToString'(k,  , fill o :: m) let let  in in s ^ "\n  " ^ (format k) ^ (menu o) menuToString'(k,  , fix o :: m) let let  in in s ^ "\n  " ^ (format k) ^ (menu o) menuToString'(k,  , elim o :: m) let let  in in s ^ "\n  " ^ (format k) ^ (menu o)(*          | menuToString' (k, Inference O :: M,kOopt) =
              let
                val (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
              end
*)
 in match ! menu with nONE -> raise (error "Menu is empty") sOME m -> menuToString' (1,  , m)let rec printStats() let let  inlet  in in (print "Statistics:\n\n"; print ("Number of goals : " ^ (toString (nopen + nsolved)) ^ "\n"); print ("     open goals : " ^ (toString (nopen)) ^ "\n"); print ("   solved goals : " ^ (toString (nsolved)) ^ "\n"))let rec printmenu() (match ! focus with [] -> abort "QED" (state (w,  , psi,  , p,  , f) :: r) -> (print ("\n======================="); print ("\n= META THEOREM PROVER =\n"); print (ctxToString (psi)); print ("\n-----------------------\n"); print (forToString (psi,  , f)); print ("\n-----------------------\n"); print (prgToString (psi,  , p)); print ("\n-----------------------"); print (menuToString ()); print ("\n=======================\n")) (stateLF (x as eVar (r,  , g,  , v,  , cs)) :: r) -> (print ("\n======================="); print ("\n=== THEOREM PROVER ====\n"); print (ctxToString (null,  , g)); print ("\n-----------------------\n"); print (expToString (g,  , v)); print ("\n-----------------------\n"); print (expToString (g,  , x)); print ("\n-----------------------"); print (menuToString ()); print ("\n=======================\n")))let rec menu() (match (! focus) with [] -> print "Please initialize first\n" (state (w,  , psi,  , p,  , f) :: _) -> let let  inlet  inlet  inlet  inlet rec splitMenu[] [] splitMenu(operators :: l) map split operators @ splitMenu llet  inlet rec introMenu[] [] introMenu((sOME oper) :: l) (introduce oper) :: introMenu l introMenu(nONE :: l) introMenu llet  inlet  inlet rec elimMenu[] [] elimMenu(operators :: l) map elim operators @ elimMenu llet  inlet  in in menu := sOME (intro @ split @ fill @ elim) (stateLF y :: _) -> let let  inlet  inlet  in in menu := sOME (fill))let rec selectk let let rec select'(k,  , nil) abort ("No such menu item") select'(1,  , split o :: _) (time splitting apply) o select'(1,  , introduce o :: _) apply o select'(1,  , elim o :: _) apply o select'(1,  , fill o :: _) (time filling apply) o select'(k,  , _ :: m) select' (k - 1,  , m) in (match ! menu with nONE -> raise (error "No menu defined") sOME m -> try  with )let rec initnames let let  inlet  inlet  inlet  inlet rec selectc (try  with )let  in(* so far omitted:  make sure that all parts of the theorem are
             declared in the same world
          *)
let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in ()(* focus n = ()

       Invariant:
       Let n be a string.
       Side effect: Focus on selected subgoal.
    *)
let rec focusn (match (! focus) with [] -> print "Please initialize first\n" (state (w,  , psi,  , p,  , f) :: _) -> let let rec findIEVarnil raise (error ("cannot focus on " ^ n)) findIEVar(y :: ys) if evarName (coerceCtx psi,  , y) = n then (focus := (stateLF y :: ! focus); normalize (); menu (); printmenu ()) else findIEVar yslet rec findTEVarnil findIEVar (collectLF p) findTEVar((x as eVar (psi,  , r,  , f,  , tC,  , tCs,  , y)) :: xs) if evarName (coerceCtx psi,  , y) = n then (focus := (state (w,  , nameCtx psi,  , x,  , f) :: ! focus); normalize (); menu (); printmenu ()) else findTEVar xs in findTEVar (collectT p) (stateLF (u) :: _) -> (* Invariant: U has already been printed, all EVars occuring
                 in U are already named.
              *)
(match (getEVarOpt n) with nONE -> raise (error ("cannot focus on " ^ n)) sOME y -> (focus := (stateLF y :: ! focus); normalize (); menu (); printmenu ())))let rec return() (match (! focus) with [s] -> if close s then print "[Q.E.D.]\n" else () (s :: rest) -> (focus := rest; normalize (); menu (); printmenu ()))let  inlet  inlet  inlet  inlet  inlet  inlet  inend