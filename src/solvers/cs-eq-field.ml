CSEqField  Field FIELD    Whnf WHNF    Unify UNIFY     CS_EQ_FIELD  struct (*! structure CSManager = CSManager !*)
module (*! structure IntSyn = IntSyn !*)
type Mset(* MultiSet                   *)
type Sum(* Sum ::= m + M1 + ...       *)
 Mon(* Mon ::= n * U1[s1] * ...   *)
(* A monomial (n * U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) the coefficient n is different from zero;
       (b) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)
open IntSyn open Field module module (* CSManager.ModeSyn *)
exception (* FgnExp representation for this domain *)
let rec extractSum(myIntsynRep sum) sum extractSumfe raise ((unexpectedFgnExp fe))(* constraint solver ID of this module *)
let  in(* constant ID of the type family constant "number" *)
let  inlet rec number() root (const (! numberID),  , nil)(* constant ID's of the object constants defined by this module *)
let  in(* ~ : number -> number           *)
let  in(* + : number -> number -> number *)
let  in(* - : number -> number -> number *)
let  in(* * : number -> number -> number *)
let rec unaryMinusExp(u) root (const (! unaryMinusID),  , app (u,  , nil))let rec plusExp(u,  , v) root (const (! plusID),  , app (u,  , app (v,  , nil)))let rec minusExp(u,  , v) root (const (! minusID),  , app (u,  , app (v,  , nil)))let rec timesExp(u,  , v) root (const (! timesID),  , app (u,  , app (v,  , nil)))let rec numberConDec(d) conDec (toString (d),  , nONE,  , 0,  , normal,  , number (),  , type)let rec numberExp(d) root (fgnConst (! myID,  , numberConDec (d)),  , nil)(* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
let rec parseNumberstring (match fromString (string) with sOME (d) -> sOME (numberConDec (d)) nONE -> nONE)(* solveNumber k = SOME(U)

       Invariant:
       U is the term obtained applying the foreign constant
       corresponding to the number k to an empty spine
    *)
let rec solveNumber(g,  , s,  , k) sOME (numberExp (fromInt k))(* findMset eq (x, L) =
         SOME (y, L') if there exists y such that eq (x, y)
                         and L ~ (y :: L') (multiset equality)
         NONE if there is no y in L such that eq (x, y)
    *)
let rec findMSeteq(x,  , l) let let rec findMSet'(tried,  , nil) nONE findMSet'(tried,  , y :: l) if eq (x,  , y) then sOME (y,  , tried @ l) else findMSet' (y :: tried,  , l) in findMSet' (nil,  , l)(* equalMset eq (L, L') = true iff L ~ L' (multiset equality) *)
let rec equalMSeteq let let rec equalMSet'(nil,  , nil) true equalMSet'(x :: l1',  , l2) (match (findMSet eq (x,  , l2)) with sOME (y,  , l2') -> (equalMSet' (l1',  , l2')) nONE -> false) equalMSet'_ false in equalMSet'(* toExp sum = U

       Invariant:
       If sum is normal
       G |- U : V and U is the Twelf syntax conversion of sum
    *)
let rec toExp(sum (m,  , nil)) numberExp m toExp(sum (m,  , [mon])) if (m = zero) then toExpMon mon else plusExp (toExp (sum (m,  , nil)),  , toExpMon mon) toExp(sum (m,  , monLL as (mon :: monL))) plusExp (toExp (sum (m,  , monL)),  , toExpMon mon)(* toExpMon mon = U

       Invariant:
       If mon is normal
       G |- U : V and U is the Twelf syntax conversion of mon
    *)
 toExpMon(mon (n,  , nil)) numberExp n toExpMon(mon (n,  , [us])) if (n = one) then toExpEClo us else timesExp (toExpMon (mon (n,  , nil)),  , toExpEClo us) toExpMon(mon (n,  , us :: usL)) timesExp (toExpMon (mon (n,  , usL)),  , toExpEClo us)(* toExpEClo (U,s) = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of Us
    *)
 toExpEClo(u,  , shift (0)) u toExpEClous eClo us(* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *)
let rec compatibleMon(mon (_,  , usL1),  , mon (_,  , usL2)) equalMSet (fun (us1,  , us2) -> sameExpW (us1,  , us2)) (usL1,  , usL2)(* sameExpW ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1)  in whnf
       and  G |- s2 : G2    G2 |- U2 : V2    (U2,s2)  in whnf
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
 sameExpW(us1 as (root (h1,  , s1),  , s1),  , us2 as (root (h2,  , s2),  , s2)) (match (h1,  , h2) with (bVar (k1),  , bVar (k2)) -> (k1 = k2) && sameSpine ((s1,  , s1),  , (s2,  , s2)) (fVar (n1,  , _,  , _),  , fVar (n2,  , _,  , _)) -> (n1 = n2) && sameSpine ((s1,  , s1),  , (s2,  , s2)) _ -> false) sameExpW(us1 as (u1 as eVar (r1,  , g1,  , v1,  , cnstrs1),  , s1),  , us2 as (u2 as eVar (r2,  , g2,  , v2,  , cnstrs2),  , s2)) (r1 = r2) && sameSub (s1,  , s2) sameExpW_ false(* sameExp ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1
       and  G |- s2 : G2    G2 |- U2 : V2
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
 sameExp(us1,  , us2) sameExpW (whnf us1,  , whnf us2)(* sameSpine (S1, S2) = T

       Invariant:
       If   G |- S1 : V > W
       and  G |- S2 : V > W
       then T only if S1 = S2 (as spines)
    *)
 sameSpine((nil,  , s1),  , (nil,  , s2)) true sameSpine((sClo (s1,  , s1'),  , s1),  , ss2) sameSpine ((s1,  , comp (s1',  , s1)),  , ss2) sameSpine(ss1,  , (sClo (s2,  , s2'),  , s2)) sameSpine (ss1,  , (s2,  , comp (s2',  , s2))) sameSpine((app (u1,  , s1),  , s1),  , (app (u2,  , s2),  , s2)) sameExp ((u1,  , s1),  , (u2,  , s2)) && sameSpine ((s1,  , s1),  , (s2,  , s2)) sameSpine_ false(* sameSub (s1, s2) = T

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then T only if s1 = s2 (as substitutions)
    *)
 sameSub(shift _,  , shift _) true sameSub(dot (idx (k1),  , s1),  , dot (idx (k2),  , s2)) (k1 = k2) && sameSub (s1,  , s2) sameSub(s1 as dot (idx _,  , _),  , shift (k2)) sameSub (s1,  , dot (idx (+ (k2,  , 1)),  , shift (+ (k2,  , 1)))) sameSub(shift (k1),  , s2 as dot (idx _,  , _)) sameSub (dot (idx (+ (k1,  , 1)),  , shift (+ (k1,  , 1))),  , s2) sameSub_ false(* plusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 + sum2
    *)
let rec plusSum(sum (m1,  , nil),  , sum (m2,  , monL2)) sum (m1 + m2,  , monL2) plusSum(sum (m1,  , monL1),  , sum (m2,  , nil)) sum (m1 + m2,  , monL1) plusSum(sum (m1,  , mon1 :: monL1),  , sum (m2,  , monL2)) plusSumMon (plusSum (sum (m1,  , monL1),  , sum (m2,  , monL2)),  , mon1)(* plusSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 + mon2
    *)
 plusSumMon(sum (m,  , nil),  , mon) sum (m,  , [mon]) plusSumMon(sum (m,  , monL),  , mon as mon (n,  , usL)) (match (findMSet compatibleMon (mon,  , monL)) with sOME (mon (n',  , _),  , monL') -> let let  in in if (n'' = zero) then sum (m,  , monL') else sum (m,  , (mon (n'',  , usL)) :: monL') nONE -> sum (m,  , mon :: monL))(* timesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 * sum2
    *)
let rec timesSum(sum (m1,  , nil),  , sum (m2,  , nil)) sum (m1 * m2,  , nil) timesSum(sum (m1,  , mon1 :: monL1),  , sum2) plusSum (timesSumMon (sum2,  , mon1),  , timesSum (sum (m1,  , monL1),  , sum2)) timesSum(sum1,  , sum (m2,  , mon2 :: monL2)) plusSum (timesSumMon (sum1,  , mon2),  , timesSum (sum1,  , sum (m2,  , monL2)))(* timesSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 * mon2
    *)
 timesSumMon(sum (m,  , nil),  , mon (n,  , usL)) let let  in in if (n' = zero) then sum (n',  , nil) else sum (zero,  , [mon (n',  , usL)]) timesSumMon(sum (m,  , (mon (n',  , usL')) :: monL),  , mon as mon (n,  , usL)) let let  inlet  inlet  in in sum (m',  , (mon (n'',  , usL'')) :: monL')(* unaryMinusSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = ~1 * sum
    *)
let rec unaryMinusSum(sum) timesSum (sum (~ one,  , nil),  , sum)(* minusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 - sum2
    *)
let rec minusSum(sum1,  , sum2) plusSum (sum1,  , unaryMinusSum (sum2))(* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
let rec fromExpW(us as (fgnExp (cs,  , fe),  , _)) if (cs = ! myID) then normalizeSum (extractSum fe) else sum (zero,  , [mon (one,  , [us])]) fromExpW(us as (root (fgnConst (cs,  , conDec),  , _),  , _)) if (cs = ! myID) then (match (fromString (conDecName (conDec))) with sOME (m) -> sum (m,  , nil)) else sum (zero,  , [mon (one,  , [us])]) fromExpW(us as (root (def (d),  , _),  , _)) fromExpW (expandDef (us)) fromExpWus sum (zero,  , [mon (one,  , [us])])(* fromExp (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
 fromExpus fromExpW (whnf us)(* normalizeSum sum = sum', where sum' normal and sum' = sum *)
 normalizeSum(sum as (sum (m,  , nil))) sum normalizeSum(sum (m,  , [mon])) plusSum (sum (m,  , nil),  , normalizeMon mon) normalizeSum(sum (m,  , mon :: monL)) plusSum (normalizeMon mon,  , normalizeSum (sum (m,  , monL)))(* normalizeMon mon = mon', where mon' normal and mon' = mon *)
 normalizeMon(mon as (mon (n,  , nil))) sum (n,  , nil) normalizeMon(mon (n,  , [us])) timesSum (sum (n,  , nil),  , fromExp us) normalizeMon(mon as (mon (n,  , us :: usL))) timesSum (fromExp us,  , normalizeMon (mon (n,  , usL)))(* mapSum (f, m + M1 + ...) = m + mapMon(f,M1) + ... *)
 mapSum(f,  , sum (m,  , monL)) sum (m,  , map (fun mon -> mapMon (f,  , mon)) monL)(* mapMon (f, n * (U1,s1) + ...) = n * f(U1,s1) * ... *)
 mapMon(f,  , mon (n,  , usL)) mon (n,  , map (fun us -> whnf (f (eClo us),  , id)) usL)(* appSum (f, m + M1 + ...) = ()     and appMon (f, Mi) for each i *)
let rec appSum(f,  , sum (m,  , monL)) app (fun mon -> appMon (f,  , mon)) monL(* appMon (f, n * (U1, s1) + ... ) = () and f (Ui[si]) for each i *)
 appMon(f,  , mon (n,  , usL)) app (fun us -> f (eClo us)) usL(* findMon f (G, sum) =
         SOME(x) if f(M) = SOME(x) for some monomial M in sum
         NONE    if f(M) = NONE for all monomials M in sum
    *)
let rec findMonf(g,  , sum (m,  , monL)) let let rec findMon'(nil,  , monL2) nONE findMon'(mon :: monL1,  , monL2) (match (f (g,  , mon,  , sum (m,  , monL1 @ monL2))) with (result as sOME _) -> result nONE -> findMon' (monL1,  , mon :: monL2)) in findMon' (monL,  , nil)(* unifySum (G, sum1, sum2) = result

       Invariant:
       If   G |- sum1 : number     sum1 normal
       and  G |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by gaussian elimination.
    *)
let rec unifySum(g,  , sum1,  , sum2) let let rec invertMon(g,  , mon (n,  , [(lHS as eVar (r,  , _,  , _,  , _),  , s)]),  , sum) if isPatSub s then let let  inlet  in in if invertible (g,  , (rHS,  , id),  , ss,  , r) then sOME (g,  , lHS,  , rHS,  , ss) else nONE else nONE invertMon_ nONE in match minusSum (sum2,  , sum1) with sum (m,  , nil) -> if (m = zero) then succeed nil else fail sum -> (match findMon invertMon (g,  , sum) with sOME assignment -> succeed [assign assignment] nONE -> let let  inlet  in in succeed [delay (u,  , cnstr)])(* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *)
 toFgn(sum as sum (m,  , nil)) toExp (sum) toFgn(sum as sum (m,  , monL)) fgnExp (! myID,  , myIntsynRep sum)(* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep sum) and sum : normal
       then U is the Twelf syntax conversion of sum
    *)
let rec toInternal(myIntsynRep sum)() toExp (normalizeSum sum) toInternalfe() raise ((unexpectedFgnExp fe))(* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep sum)   sum : normal
       and
         f sum = f (m + mon1 + ... + monN) =
               = m + f (m1 * Us1 * ... * UsM) + ...
               = m + (m1 * (f Us1) * ... * f (UsM))
               = sum'           sum' : normal
       then
         U' is a foreign expression representing sum'
    *)
let rec map(myIntsynRep sum)f toFgn (normalizeSum (mapSum (f,  , sum))) mapfe_ raise ((unexpectedFgnExp fe))(* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep sum)     sum : normal
       and
          sum = m + mon1 + ... monN
          where moni = mi * Usi1 * ... UsiMi
       then f is applied to each Usij
         (since sum : normal, each Usij is in whnf)
    *)
let rec app(myIntsynRep sum)f appSum (f,  , sum) appfe_ raise ((unexpectedFgnExp fe))let rec equalTo(myIntsynRep sum)u2 (match minusSum (normalizeSum sum,  , (fromExp (u2,  , id))) with sum (m,  , nil) -> (m = zero) _ -> false) equalTofe_ raise ((unexpectedFgnExp fe))let rec unifyWith(myIntsynRep sum)(g,  , u2) unifySum (g,  , normalizeSum sum,  , (fromExp (u2,  , id))) unifyWithfe_ raise ((unexpectedFgnExp fe))let rec installFgnExpOps() let let  inlet  inlet  inlet  inlet  inlet  in in ()let rec makeFgn(arity,  , opExp)(s) let let rec makeParams0 nil makeParamsn app (root (bVar (n),  , nil),  , makeParams (- (n,  , 1)))let rec makeLame0 e makeLamen lam (dec (nONE,  , number ()),  , makeLam e (- (n,  , 1)))let rec expand((nil,  , s),  , arity) (makeParams arity,  , arity) expand((app (u,  , s),  , s),  , arity) let let  in in (app (eClo (u,  , comp (s,  , shift (arity'))),  , s'),  , arity') expand((sClo (s,  , s'),  , s),  , arity) expand ((s,  , comp (s',  , s)),  , arity)let  in in makeLam (toFgn (opExp s')) arity'let rec makeFgnUnaryopSum makeFgn (1,  , fun (app (u,  , nil)) -> opSum (fromExp (u,  , id)))let rec makeFgnBinaryopSum makeFgn (2,  , fun (app (u1,  , app (u2,  , nil))) -> opSum (fromExp (u1,  , id),  , fromExp (u2,  , id)))let rec arrow(u,  , v) pi ((dec (nONE,  , u),  , no),  , v)(* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
let rec init(cs,  , installF) (myID := cs; numberID := installF (conDec (name,  , nONE,  , 0,  , constraint (! myID,  , solveNumber),  , uni (type),  , kind),  , nONE,  , [mnil]); unaryMinusID := installF (conDec ("~",  , nONE,  , 0,  , foreign (! myID,  , makeFgnUnary unaryMinusSum),  , arrow (number (),  , number ()),  , type),  , sOME (prefix (maxPrec)),  , nil); plusID := installF (conDec ("+",  , nONE,  , 0,  , foreign (! myID,  , makeFgnBinary plusSum),  , arrow (number (),  , arrow (number (),  , number ())),  , type),  , sOME (infix (dec (dec maxPrec),  , left)),  , nil); minusID := installF (conDec ("-",  , nONE,  , 0,  , foreign (! myID,  , makeFgnBinary minusSum),  , arrow (number (),  , arrow (number (),  , number ())),  , type),  , sOME (infix (dec (dec maxPrec),  , left)),  , nil); timesID := installF (conDec ("*",  , nONE,  , 0,  , foreign (! myID,  , makeFgnBinary timesSum),  , arrow (number (),  , arrow (number (),  , number ())),  , type),  , sOME (infix (dec maxPrec,  , left)),  , nil); installFgnExpOps (); ())let  inlet  inlet  inlet  inlet  inlet  inlet rec unaryMinusu toFgn (unaryMinusSum (fromExp (u,  , id)))let rec plus(u,  , v) toFgn (plusSum (fromExp (u,  , id),  , fromExp (v,  , id)))let rec minus(u,  , v) toFgn (minusSum (fromExp (u,  , id),  , fromExp (v,  , id)))let rec times(u,  , v) toFgn (timesSum (fromExp (u,  , id),  , fromExp (v,  , id)))let  in(* local *)
end