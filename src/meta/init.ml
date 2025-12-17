MTPInit  MTPGlobal MTPGLOBAL    MTPData MTPDATA    Names NAMES    StateSyn' STATESYN    Formatter FORMATTER    Whnf WHNF    Print PRINT    Print Formatter  Formatter   FunPrint FUNPRINT    FunPrint Formatter  Formatter    MTPINIT  struct (*! structure FunSyn = FunSyn' !*)
module exception module module module module (* init (F, OF) = Ss'

       Invariant:
       If   . |- F formula    and   F in nf
       and  . |- OF order
       then Ss' is a list of initial states for the theorem prover
    *)
let rec init(f,  , oF) let let rec init'((g,  , b),  , all (_,  , o),  , all (prim d,  , f'),  , ss) let let  in in init' ((decl (g,  , d'),  , decl (b,  , lemma (splits (! maxSplit)))),  , o,  , f',  , ss) init'(gB,  , and (o1,  , o2),  , and (f1,  , f2),  , ss) init' (gB,  , o1,  , f1,  , init' (gB,  , o2,  , f2,  , ss)) init'(gB,  , o,  , f' as ex _,  , ss) state (length ss + 1,  , gB,  , (f,  , oF),  , 1,  , o,  , nil,  , f') :: ss init'(gB,  , o,  , f' as true,  , ss) state (length ss + 1,  , gB,  , (f,  , oF),  , 1,  , o,  , nil,  , f') :: ss(* added in case there are no existentials -fp *)
 in (varReset null; maxFill := 0; init' ((null,  , null),  , oF,  , f,  , nil))let  in(* local *)
end