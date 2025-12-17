Skolem  Global GLOBAL    Whnf WHNF    Abstract ABSTRACT    IndexSkolem INDEX    ModeTable MODETABLE    Print PRINT    Compile COMPILE    Timers TIMERS    Names NAMES     SKOLEM  struct (*! structure IntSyn = IntSyn' !*)
exception module module (*! structure CompSyn = Compile.CompSyn !*)
(* installSkolem (name, k, (V, mS), L) =

       Invariant:
            name is the name of a theorem
       and  imp is the number of implicit arguments
       and  V is its term together with the mode assignment mS
       and  L is the level of the declaration

       Effects: New Skolem constants are generated, named, and indexed
    *)
let rec installSkolem(name,  , imp,  , (v,  , mS),  , l) let (* spine n = S'

           Invariant:
           S' = n; n-1; ... 1; Nil
        *)
let rec spine0 nil spinen app (root (bVar n,  , nil),  , spine (n - 1))(* installSkolem' ((V, mS), s, k) = ()

           Invariant:
                G |- V : type
           and  G' |- s : G
           and  |G'| = d
           and  k is a continuation, mapping a type G' |- V' type
                to . |- {{G'}} V'

           Effects: New Skolem constants are generated, named, and indexed
        *)
let rec installSkolem'(d,  , (pi ((d,  , dP),  , v),  , mS),  , s,  , k) (match mS with mapp (marg (plus,  , _),  , mS') -> installSkolem' (d + 1,  , (v,  , mS'),  , dot1 s,  , fun v -> k (piDepend ((normalizeDec (d,  , s),  , meta),  , v)))(*                                  fn V => k (I.Pi ((Whnf.normalizeDec (D, s), DP), V))) *)
 mapp (marg (minus,  , _),  , mS') -> let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in(*                  val CompSyn.SClause r = CompSyn.sProgLookup sk *)
let  inlet  in in installSkolem' (d,  , (v,  , mS'),  , dot (exp (root (h,  , s)),  , s),  , k)) installSkolem'(_,  , (uni _,  , mnil),  , _,  , _) () in installSkolem' (0,  , (v,  , mS),  , id,  , fun v -> v)(* install L = ()

       Invariant:
           L is a list of a's (mututal inductive theorems)
           which have an associated mode declaration

       Effect: Skolem constants for all theorems are generated, named, and indexed
    *)
let rec installnil () install(a :: aL) let let  inlet  inlet  in in install aLlet  in(* local *)
end