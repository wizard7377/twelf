Fquery  Global GLOBAL    Names NAMES    ReconQuery RECON_QUERY    Timers TIMERS    Print PRINT     FQUERY  struct module exception module module module module (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
let rec evarInstToString(xs) if ! chatter >= 3 then evarInstToString (xs) else ""(* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
let rec expToStringgU if ! chatter >= 3 then expToString gU else ""let rec lower(0,  , g,  , v) (g,  , v) lower(n,  , g,  , pi ((d,  , _),  , v)) lower (n - 1,  , decl (g,  , d),  , v)let rec run(quy,  , loc (fileName,  , r)) let (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
let  in(* times itself *)
let  inlet  inlet  inlet  inlet  in(* G |- V'' : type *)
let  inlet  inlet  inlet  inlet  inlet  in in print ("Delphin: " ^ prgToString (null,  , v) ^ "\n")end