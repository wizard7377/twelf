CSIntWord  Whnf WHNF    Unify UNIFY    wordSize Int    CS  struct (*! structure CSManager = CSManager !*)
open IntSyn module module module (* CSManager.ModeSyn *)
exception (* FgnCnstr Representation: (G, proof, U1, U2, U3) *)
exception exception let  inlet  inlet  in(* numCheck (d) = true iff d <= max *)
let rec numCheck(d) <= (d,  , max)(* plusCheck (d1, d2) = true iff d1 + d2 <= max *)
let rec plusCheck(d1,  , d2) let let  in in >= (d3,  , d1) && >= (d3,  , d2) && <= (d3,  , max)(* timesCheck (d1, d2) = true iff d1 * d2 <= max *)
let rec timesCheck(d1,  , d2) if (d1 = zero || d2 = zero) then true else let let  in in > (d3,  , zero)(* quotCheck (d1, d2) = true iff  d2 != zero *)
let rec quotCheck(d1,  , d2) > (d2,  , zero)(* constraint solver ID of this module *)
let  in(* constant ID of the type family constant "wordXX" *)
let  inlet rec word() root (const (! wordID),  , nil)(* constant ID's of the operators defined by this module *)
let  in(* + : wordXX -> wordXX -> wordXX -> type *)
let  in(* * : wordXX -> wordXX -> wordXX -> type *)
let  in(* / : wordXX -> wordXX -> wordXX -> type *)
let rec plusExp(u,  , v,  , w) root (const (! plusID),  , app (u,  , app (v,  , app (w,  , nil))))let rec timesExp(u,  , v,  , w) root (const (! timesID),  , app (u,  , app (v,  , app (w,  , nil))))let rec quotExp(u,  , v,  , w) root (const (! quotID),  , app (u,  , app (v,  , app (w,  , nil))))(* constant ID's of the proof object generators and their proof objects *)
(* (these are used as workaround for the lack of sigma types in Twelf)  *)
let  in(* prove+ : {U}{V}{W} + U V W -> type *)
let  in(* prove* : {U}{V}{W} * U V W -> type *)
let  in(* prove/ : {U}{V}{W} / U V W -> type *)
let  in(* proof* : {U}{V}{W}{P} prove+ U V W P *)
let  in(* proof* : {U}{V}{W}{P} prove* U V W P *)
let  in(* proof/ : {U}{V}{W}{P} prove/ U V W P *)
let rec provePlusExp(u,  , v,  , w,  , p) root (const (! provePlusID),  , app (u,  , app (v,  , app (w,  , app (p,  , nil)))))let rec proofPlusExp(u,  , v,  , w,  , p) root (const (! proofPlusID),  , app (u,  , app (v,  , app (w,  , app (p,  , nil)))))let rec proofTimesExp(u,  , v,  , w,  , p) root (const (! proofTimesID),  , app (u,  , app (v,  , app (w,  , app (p,  , nil)))))let rec proveTimesExp(u,  , v,  , w,  , p) root (const (! proveTimesID),  , app (u,  , app (v,  , app (w,  , app (p,  , nil)))))let rec proveQuotExp(u,  , v,  , w,  , p) root (const (! proveQuotID),  , app (u,  , app (v,  , app (w,  , app (p,  , nil)))))let rec proofQuotExp(u,  , v,  , w,  , p) root (const (! proofQuotID),  , app (u,  , app (v,  , app (w,  , app (p,  , nil)))))let rec numberConDec(d) conDec (fmt dEC (d),  , nONE,  , 0,  , normal,  , word (),  , type)let rec numberExp(d) root (fgnConst (! myID,  , numberConDec (d)),  , nil)(* scanNumber (str) = numOpt

       Invariant:
         numOpt = SOME(n) if str is the decimal representation of the number n
                = NONE otherwise
    *)
let rec scanNumber(str) let let rec check(chars as (_ :: _)) (all isDigit chars) checknil false in if check (explode str) then match (scanString (scan dEC) str) with sOME (d) -> (if numCheck (d) then sOME (d) else nONE) nONE -> nONE else nONE(* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
let rec parseNumberstring match (scanNumber string) with sOME (d) -> sOME (numberConDec d) nONE -> nONElet rec plusPfConDec(d1,  , d2) let let  in in conDec (fmt dEC d1 ^ "+" ^ fmt dEC d2,  , nONE,  , 0,  , normal,  , plusExp (numberExp d1,  , numberExp d2,  , numberExp d3),  , type)let rec plusPfExpds root (fgnConst (! myID,  , plusPfConDec ds),  , nil)let rec timesPfConDec(d1,  , d2) let let  in in conDec (fmt dEC d1 ^ "*" ^ fmt dEC d2,  , nONE,  , 0,  , normal,  , timesExp (numberExp d1,  , numberExp d2,  , numberExp d3),  , type)let rec timesPfExpds root (fgnConst (! myID,  , timesPfConDec ds),  , nil)let rec quotPfConDec(d1,  , d2) let let  in in conDec (fmt dEC d1 ^ "/" ^ fmt dEC d2,  , nONE,  , 0,  , normal,  , quotExp (numberExp d1,  , numberExp d2,  , numberExp d3),  , type)let rec quotPfExpds root (fgnConst (! myID,  , quotPfConDec ds),  , nil)let rec scanBinopPfoperstring let let  in in match args with [arg1; arg2] -> (match (scanString (scan dEC) arg1,  , scanString (scan dEC) arg2) with (sOME (d1),  , sOME (d2)) -> sOME (d1,  , d2) _ -> nONE) _ -> nONE(* parseBinopPf operator string = SOME(conDec) or NONE

       Invariant:
       If string parses to the proof object of n1<operator>n2
       then conDec is the (foreign) constant declaration of n1<operator>n2
    *)
let rec parseBinopPfoperstring match (oper,  , scanBinopPf oper string) with ('+',  , sOME (ds)) -> sOME (plusPfConDec ds) ('*',  , sOME (ds)) -> sOME (timesPfConDec ds) ('/',  , sOME (ds)) -> sOME (quotPfConDec ds) _ -> nONElet  inlet  inlet  inlet rec parseAllstring (match (parseNumber (string)) with sOME (conDec) -> sOME (conDec) nONE -> (match (parsePlusPf (string)) with sOME (conDec) -> sOME (conDec) nONE -> (match (parseTimesPf (string)) with sOME (conDec) -> sOME (conDec) nONE -> parseQuotPf (string))))type FixTerm(*        | <Expr>            *)
(* fromExpW (U, s) = t

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then t is the internal representation of U[s] as term
    *)
let rec fromExpW(us as (root (fgnConst (cs,  , conDec),  , _),  , _)) if (cs = ! myID) then let let  in in (match (scanNumber string) with sOME (d) -> num d nONE -> (match (scanBinopPf '/' string) with sOME (ds) -> quotPf ds nONE -> (match (scanBinopPf '+' string) with sOME (ds) -> plusPf ds nONE -> (match (scanBinopPf '*' string) with sOME (ds) -> timesPf ds nONE -> expr us)))) else expr us fromExpW(us as (root (def (d),  , _),  , _)) fromExpW (expandDef (us)) fromExpWus expr us(* fromExp (U, s) = t

       Invariant:
       If   G' |- s : G    G |- U : V
       then t is the internal representation of U[s] as term
    *)
 fromExpus fromExpW (whnf us)(* toExp t = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of t
    *)
let rec toExp(num d) numberExp d toExp(plusPf ds) plusPfExp ds toExp(timesPf ds) timesPfExp ds toExp(quotPf ds) quotPfExp ds toExp(expr us) eClo uslet rec solveNumber(g,  , s,  , k) sOME (numberExp (fromInt k))(* fst (S, s) = U1, the first argument in S[s] *)
let rec fst(app (u1,  , _),  , s) (u1,  , s) fst(sClo (s,  , s'),  , s) fst (s,  , comp (s',  , s))(* snd (S, s) = U2, the second argument in S[s] *)
let rec snd(app (_,  , s),  , s) fst (s,  , s) snd(sClo (s,  , s'),  , s) snd (s,  , comp (s',  , s))(* trd (S, s) = U1, the third argument in S[s] *)
let rec trd(app (_,  , s),  , s) snd (s,  , s) trd(sClo (s,  , s'),  , s) trd (s,  , comp (s',  , s))(* fth (S, s) = U1, the fourth argument in S[s] *)
let rec fth(app (_,  , s),  , s) trd (s,  , s) fth(sClo (s,  , s'),  , s) fth (s,  , comp (s',  , s))let rec toInternalPlus(g,  , u1,  , u2,  , u3)() [(g,  , plusExp (u1,  , u2,  , u3))] awakePlus(g,  , proof,  , u1,  , u2,  , u3)() match (solvePlus (g,  , app (u1,  , app (u2,  , app (u3,  , nil))),  , 0)) with sOME (proof') -> unifiable (g,  , (proof,  , id),  , (proof',  , id)) nONE -> false(* constraint constructor *)
 makeCnstrPlus(g,  , proof,  , u1,  , u2,  , u3) fgnCnstr (! myID,  , myFgnCnstrRepPlus (g,  , proof,  , u1,  , u2,  , u3))(* solvePlus (G, S, n) tries to find the n-th solution to
          G |- '+' @ S : type
    *)
 solvePlus(g,  , s,  , 0) let let  inlet  inlet  in in (match (fromExp (us1),  , fromExp (us2),  , fromExp (us3)) with (num d1,  , num d2,  , num d3) -> if (d3 = + (d1,  , d2) && plusCheck (d1,  , d2)) then sOME (plusPfExp (d1,  , d2)) else nONE (expr us1,  , num d2,  , num d3) -> if (>= (d3,  , d2) && unifiable (g,  , us1,  , (numberExp (- (d3,  , d2)),  , id))) then sOME (plusPfExp (- (d3,  , d2),  , d2)) else nONE (num d1,  , expr us2,  , num d3) -> if (>= (d3,  , d1) && unifiable (g,  , us2,  , (numberExp (- (d3,  , d1)),  , id))) then sOME (plusPfExp (d1,  , - (d3,  , d1))) else nONE (num d1,  , num d2,  , expr us3) -> if (plusCheck (d1,  , d2) && unifiable (g,  , us3,  , (numberExp (+ (d1,  , d2)),  , id))) then sOME (plusPfExp (d1,  , d2)) else nONE _ -> let let  inlet  inlet  in in sOME (proof)) solvePlus(g,  , s,  , n) nONE toInternalTimes(g,  , u1,  , u2,  , u3)() [(g,  , timesExp (u1,  , u2,  , u3))] awakeTimes(g,  , proof,  , u1,  , u2,  , u3)() match (solveTimes (g,  , app (u1,  , app (u2,  , app (u3,  , nil))),  , 0)) with sOME (proof') -> unifiable (g,  , (proof,  , id),  , (proof',  , id)) nONE -> false makeCnstrTimes(g,  , proof,  , u1,  , u2,  , u3) fgnCnstr (! myID,  , myFgnCnstrRepTimes (g,  , proof,  , u1,  , u2,  , u3))(* solveTimes (G, S, n) tries to find the n-th solution to
         G |- '*' @ S : type
    *)
 solveTimes(g,  , s,  , 0) let let  inlet  inlet  in in (match (fromExp us1,  , fromExp us2,  , fromExp us3) with (num d1,  , num d2,  , num d3) -> if (d3 = * (d1,  , d2) && timesCheck (d1,  , d2)) then sOME (timesPfExp (d1,  , d2)) else nONE (expr us1,  , num d2,  , num d3) -> if (d3 = zero && unifiable (g,  , us1,  , (numberExp (zero),  , id))) then sOME (timesPfExp (zero,  , d2)) else if (> (d2,  , zero) && > (d3,  , zero) && mod (d3,  , d2) = zero && unifiable (g,  , us1,  , (numberExp (div (d3,  , d2)),  , id))) then sOME (timesPfExp (div (d3,  , d2),  , d2)) else nONE (num d1,  , expr us2,  , num d3) -> if (d3 = zero && unifiable (g,  , us2,  , (numberExp (zero),  , id))) then sOME (timesPfExp (d1,  , zero)) else if (> (d1,  , zero) && > (d3,  , zero) && mod (d3,  , d1) = zero && unifiable (g,  , us2,  , (numberExp (div (d3,  , d1)),  , id))) then sOME (timesPfExp (d1,  , div (d3,  , d1))) else nONE (num d1,  , num d2,  , expr us3) -> if (timesCheck (d1,  , d2) && unifiable (g,  , us3,  , (numberExp (* (d1,  , d2)),  , id))) then sOME (timesPfExp (d1,  , d2)) else nONE _ -> let let  inlet  inlet  in in sOME (proof)) solveTimes(g,  , s,  , n) nONE toInternalQuot(g,  , u1,  , u2,  , u3)() [(g,  , quotExp (u1,  , u2,  , u3))] awakeQuot(g,  , proof,  , u1,  , u2,  , u3)() match (solveQuot (g,  , app (u1,  , app (u2,  , app (u3,  , nil))),  , 0)) with sOME (proof') -> unifiable (g,  , (proof,  , id),  , (proof',  , id)) nONE -> false(* constraint constructor *)
 makeCnstrQuot(g,  , proof,  , u1,  , u2,  , u3) fgnCnstr (! myID,  , myFgnCnstrRepQuot (g,  , proof,  , u1,  , u2,  , u3))(* solveQuot (G, S, n) tries to find the n-th solution to
         G |- '/' @ S : type
    *)
 solveQuot(g,  , s,  , 0) let let  inlet  inlet  in in (match (fromExp us1,  , fromExp us2,  , fromExp us3) with (num d1,  , num d2,  , num d3) -> if (quotCheck (d1,  , d2) && d3 = div (d1,  , d2)) then sOME (quotPfExp (d1,  , d2)) else nONE (num d1,  , num d2,  , expr us3) -> if (quotCheck (d1,  , d2) && unifiable (g,  , us3,  , (numberExp (div (d1,  , d2)),  , id))) then sOME (quotPfExp (d1,  , d2)) else nONE _ -> let let  inlet  inlet  in in sOME (proof)) solveQuot(g,  , s,  , n) nONE(* solveProvePlus (G, S, n) tries to find the n-th solution to
         G |- prove+ @ S : type
    *)
let rec solveProvePlus(g,  , s,  , k) let let  inlet  inlet  inlet  in in match (solvePlus (g,  , app (eClo us1,  , app (eClo us2,  , app (eClo us3,  , nil))),  , k)) with sOME (u) -> if unifiable (g,  , us4,  , (u,  , id)) then sOME (proofPlusExp (eClo us1,  , eClo us2,  , eClo us3,  , eClo us4)) else nONE nONE -> nONE(* solveProveTimes (G, S, n) tries to find the n-th solution to
         G |- prove* @ S : type
    *)
let rec solveProveTimes(g,  , s,  , k) let let  inlet  inlet  inlet  in in match (solveTimes (g,  , app (eClo us1,  , app (eClo us2,  , app (eClo us3,  , nil))),  , k)) with sOME (u) -> if unifiable (g,  , us4,  , (u,  , id)) then sOME (proofTimesExp (eClo us1,  , eClo us2,  , eClo us3,  , eClo us4)) else nONE nONE -> nONE(* solveProveQuot (G, S, n) tries to find the n-th solution to
         G |- prove/ @ S : type
    *)
let rec solveProveQuot(g,  , s,  , k) let let  inlet  inlet  inlet  in in match (solveQuot (g,  , app (eClo us1,  , app (eClo us2,  , app (eClo us3,  , nil))),  , k)) with sOME (u) -> if unifiable (g,  , us4,  , (u,  , id)) then sOME (proofQuotExp (eClo us1,  , eClo us2,  , eClo us3,  , eClo us4)) else nONE nONE -> nONElet rec arrow(u,  , v) pi ((dec (nONE,  , u),  , no),  , v)let rec pi(name,  , u,  , v) pi ((dec (sOME (name),  , u),  , maybe),  , v)let rec bvarn root (bVar n,  , nil)let rec installFgnCnstrOps() let let  inlet  inlet  inlet  in in ()(* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
let rec init(cs,  , installF) (myID := cs; wordID := installF (conDec ("word" ^ toString (wordSize'),  , nONE,  , 0,  , constraint (! myID,  , solveNumber),  , uni (type),  , kind),  , nONE :  Fixity Option,  , [mnil]); plusID := installF (conDec ("+",  , nONE,  , 0,  , constraint (! myID,  , solvePlus),  , arrow (word (),  , arrow (word (),  , arrow (word (),  , uni (type)))),  , kind),  , nONE,  , [mapp (marg (plus,  , sOME "X"),  , mapp (marg (plus,  , sOME "Y"),  , mapp (marg (minus,  , sOME "Z"),  , mnil))); mapp (marg (plus,  , sOME "X"),  , mapp (marg (minus,  , sOME "Y"),  , mapp (marg (plus,  , sOME "Z"),  , mnil))); mapp (marg (minus,  , sOME "X"),  , mapp (marg (plus,  , sOME "Y"),  , mapp (marg (plus,  , sOME "Z"),  , mnil)))]); timesID := installF (conDec ("*",  , nONE,  , 0,  , constraint (! myID,  , solveTimes),  , arrow (word (),  , arrow (word (),  , arrow (word (),  , uni (type)))),  , kind),  , nONE,  , [mapp (marg (plus,  , sOME "X"),  , mapp (marg (plus,  , sOME "Y"),  , mapp (marg (minus,  , sOME "Z"),  , mnil))); mapp (marg (plus,  , sOME "X"),  , mapp (marg (minus,  , sOME "Y"),  , mapp (marg (plus,  , sOME "Z"),  , mnil))); mapp (marg (minus,  , sOME "X"),  , mapp (marg (plus,  , sOME "Y"),  , mapp (marg (plus,  , sOME "Z"),  , mnil)))]); quotID := installF (conDec ("/",  , nONE,  , 0,  , constraint (! myID,  , solveQuot),  , arrow (word (),  , arrow (word (),  , arrow (word (),  , uni (type)))),  , kind),  , nONE,  , [mapp (marg (plus,  , sOME "X"),  , mapp (marg (plus,  , sOME "Y"),  , mapp (marg (minus,  , sOME "Z"),  , mnil))); mapp (marg (plus,  , sOME "X"),  , mapp (marg (minus,  , sOME "Y"),  , mapp (marg (plus,  , sOME "Z"),  , mnil)))]); provePlusID := installF (conDec ("prove+",  , nONE,  , 0,  , constraint (! myID,  , solveProvePlus),  , pi ("X",  , word (),  , pi ("Y",  , word (),  , pi ("Z",  , word (),  , pi ("P",  , plusExp (bvar 3,  , bvar 2,  , bvar 1),  , uni (type))))),  , kind),  , nONE,  , [mapp (marg (star,  , sOME "X"),  , mapp (marg (star,  , sOME "Y"),  , mapp (marg (star,  , sOME "Z"),  , mapp (marg (star,  , sOME "P"),  , mnil))))]); proofPlusID := installF (conDec ("proof+",  , nONE,  , 0,  , normal,  , pi ("X",  , word (),  , pi ("Y",  , word (),  , pi ("Z",  , word (),  , pi ("P",  , plusExp (bvar 3,  , bvar 2,  , bvar 1),  , provePlusExp (bvar 4,  , bvar 3,  , bvar 2,  , bvar 1))))),  , type),  , nONE,  , nil); proveTimesID := installF (conDec ("prove*",  , nONE,  , 0,  , constraint (! myID,  , solveProveTimes),  , pi ("X",  , word (),  , pi ("Y",  , word (),  , pi ("Z",  , word (),  , pi ("P",  , timesExp (bvar 3,  , bvar 2,  , bvar 1),  , uni (type))))),  , kind),  , nONE,  , [mapp (marg (star,  , sOME "X"),  , mapp (marg (star,  , sOME "Y"),  , mapp (marg (star,  , sOME "Z"),  , mapp (marg (star,  , sOME "P"),  , mnil))))]); proofTimesID := installF (conDec ("proof*",  , nONE,  , 0,  , normal,  , pi ("X",  , word (),  , pi ("Y",  , word (),  , pi ("Z",  , word (),  , pi ("P",  , timesExp (bvar 3,  , bvar 2,  , bvar 1),  , proveTimesExp (bvar 4,  , bvar 3,  , bvar 2,  , bvar 1))))),  , type),  , nONE,  , nil); proveQuotID := installF (conDec ("prove/",  , nONE,  , 0,  , constraint (! myID,  , solveProveQuot),  , pi ("X",  , word (),  , pi ("Y",  , word (),  , pi ("Z",  , word (),  , pi ("P",  , quotExp (bvar 3,  , bvar 2,  , bvar 1),  , uni (type))))),  , kind),  , nONE,  , [mapp (marg (star,  , sOME "X"),  , mapp (marg (star,  , sOME "Y"),  , mapp (marg (star,  , sOME "Z"),  , mapp (marg (star,  , sOME "P"),  , mnil))))]); proofQuotID := installF (conDec ("proof/",  , nONE,  , 0,  , normal,  , pi ("X",  , word (),  , pi ("Y",  , word (),  , pi ("Z",  , word (),  , pi ("P",  , quotExp (bvar 3,  , bvar 2,  , bvar 1),  , proveQuotExp (bvar 4,  , bvar 3,  , bvar 2,  , bvar 1))))),  , type),  , nONE,  , nil); installFgnCnstrOps (); ())let  inend