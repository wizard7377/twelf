CSEqBools  Whnf WHNF    Unify UNIFY     CS  struct (*! structure CSManager = CSManager !*)
(*! structure IntSyn = IntSyn !*)
type Set(* Set                        *)
type Sum(* Sum ::= m + M1 + ...       *)
 Mon(* Mon ::= U1[s1] * ...       *)
(* A monomial (U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum;
       (b) the terms Ui[si] are pairwise distinct.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)
open IntSyn module module (* CSManager.ModeSyn *)
exception let rec extractSum(myIntsynRep sum) sum extractSumfe raise ((unexpectedFgnExp fe))let  inlet  inlet rec bool() root (const (! boolID),  , nil)let  inlet  inlet rec trueExp() root (const (! trueID),  , nil)let rec falseExp() root (const (! falseID),  , nil)let rec solveBool(g,  , s,  , 0) sOME (trueExp ()) solveBool(g,  , s,  , 1) sOME (falseExp ()) solveBool(g,  , s,  , k) nONElet  inlet  inlet  inlet  inlet  inlet  inlet rec notExp(u) root (const (! notID),  , app (u,  , nil))let rec xorExp(u,  , v) root (const (! xorID),  , app (u,  , app (v,  , nil)))let rec andExp(u,  , v) root (const (! andID),  , app (u,  , app (v,  , nil)))let rec orExp(u,  , v) root (const (! orID),  , app (u,  , app (v,  , nil)))let rec impliesExp(u,  , v) root (const (! impliesID),  , app (u,  , app (v,  , nil)))let rec iffExp(u,  , v) root (const (! iffID),  , app (u,  , app (v,  , nil)))(* member eq (x, L) = true iff there there is a y in L s.t. eq(y, x) *)
let rec membereq(x,  , l) exists (fun y -> eq (x,  , y)) l(* differenceSet eq L1 L2 = (L1 \ L2) U (L2 \ L1) *)
let rec differenceSeteq(l1,  , l2) let let  inlet  in in l1' @ l2'(* equalSet eq (L1, L2) = true iff L1 is equal to L2 (both seen as sets) *)
let rec equalSeteq(l1,  , l2) (match differenceSet eq (l1,  , l2) with nil -> true (_ :: _) -> false)(* unionSet eq (L1, L2) = L1 U L2 *)
let rec unionSeteq(l1,  , l2) let let  in in l1 @ l2'(* toExp sum = U

       Invariant:
       If sum is normal
       G |- U : V and U is the Twelf syntax conversion of sum
    *)
let rec toExp(sum (m,  , nil)) let let  in in root (const (cid),  , nil) toExp(sum (m,  , [mon])) if (m = false) then toExpMon mon else xorExp (toExp (sum (m,  , nil)),  , toExpMon mon) toExp(sum (m,  , monLL as (mon :: monL))) xorExp (toExp (sum (m,  , monL)),  , toExpMon mon)(* toExpMon mon = U

       Invariant:
       If mon is normal
       G |- U : V and U is the Twelf syntax conversion of mon
    *)
 toExpMon(mon [us]) toExpEClo us toExpMon(mon (us :: usL)) andExp (toExpMon (mon usL),  , toExpEClo us)(* toExpEClo (U,s) = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of Us
    *)
 toExpEClo(u,  , shift (0)) u toExpEClous eClo us(* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *)
let rec compatibleMon(mon usL1,  , mon usL2) equalSet (fun (us1,  , us2) -> sameExp (us1,  , us2)) (usL1,  , usL2)(* sameExpW ((U1,s1), (U2,s2)) = T

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
 sameSub(shift _,  , shift _) true sameSub(dot (idx (k1),  , s1),  , dot (idx (k2),  , s2)) (k1 = k2) && sameSub (s1,  , s2) sameSub(s1 as dot (idx _,  , _),  , shift (k2)) sameSub (s1,  , dot (idx (+ (k2,  , 1)),  , shift (+ (k2,  , 1)))) sameSub(shift (k1),  , s2 as dot (idx _,  , _)) sameSub (dot (idx (+ (k1,  , 1)),  , shift (+ (k1,  , 1))),  , s2) sameSub_ false(* xorSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 xor sum2
    *)
let rec xorSum(sum (m1,  , monL1),  , sum (m2,  , monL2)) sum (not (m1 = m2),  , differenceSet compatibleMon (monL1,  , monL2))(* andSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 and sum2
    *)
let rec andSum(sum1 as sum (false,  , nil),  , sum2) sum1 andSum(sum1,  , sum2 as sum (false,  , nil)) sum2 andSum(sum1 as sum (true,  , nil),  , sum2) sum2 andSum(sum1,  , sum2 as sum (true,  , nil)) sum1 andSum(sum (m1,  , mon1 :: monL1),  , sum2) xorSum (andSumMon (sum2,  , mon1),  , andSum (sum (m1,  , monL1),  , sum2))(* andSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 and mon2
    *)
 andSumMon(sum (true,  , nil),  , mon) sum (false,  , [mon]) andSumMon(sum1 as sum (false,  , nil),  , mon) sum1 andSumMon(sum (m1,  , (mon usL1) :: monL1),  , mon2 as mon usL2) let let  in in xorSum (sum (false,  , [mon usL]),  , andSumMon (sum (m1,  , monL1),  , mon2))(* notSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = not sum
    *)
let rec notSum(sum (m,  , monL)) sum (not m,  , monL)(* orSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 or sum2
    *)
let rec orSum(sum1,  , sum2) xorSum (sum1,  , xorSum (sum2,  , andSum (sum1,  , sum2)))(* impliesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 implies sum2
    *)
let rec impliesSum(sum1,  , sum2) notSum (xorSum (sum1,  , andSum (sum1,  , sum2)))(* iffSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 iff sum2
    *)
let rec iffSum(sum1,  , sum2) notSum (xorSum (sum1,  , sum2))(* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
let rec fromExpW(us as (fgnExp (cs,  , fe),  , _)) if (cs = ! myID) then normalizeSum (extractSum fe) else sum (false,  , [mon [us]]) fromExpWus sum (false,  , [mon [us]]) fromExpus fromExpW (whnf us)(* normalizeSum sum = sum', where sum' normal and sum' = sum *)
 normalizeSum(sum as (sum (m,  , nil))) sum normalizeSum(sum (m,  , [mon])) xorSum (sum (m,  , nil),  , normalizeMon mon) normalizeSum(sum (m,  , mon :: monL)) xorSum (normalizeMon mon,  , normalizeSum (sum (m,  , monL)))(* normalizeMon mon = mon', where mon' normal and mon' = mon *)
 normalizeMon(mon [us]) fromExp us normalizeMon(mon (us :: usL)) andSum (fromExp us,  , normalizeMon (mon usL))(* mapSum (f, m + M1 + ...) = m + mapMon(f,M1) + ... *)
 mapSum(f,  , sum (m,  , monL)) sum (m,  , map (fun mon -> mapMon (f,  , mon)) monL)(* mapMon (f, n * (U1,s1) + ...) = n * f(U1,s1) * ... *)
 mapMon(f,  , mon usL) mon (map (fun us -> whnf (f (eClo us),  , id)) usL)(* appSum (f, m + M1 + ...) = ()     and appMon (f, Mi) for each i *)
let rec appSum(f,  , sum (m,  , monL)) app (fun mon -> appMon (f,  , mon)) monL(* appMon (f, n * (U1, s1) + ... ) = () and f (Ui[si]) for each i *)
 appMon(f,  , mon usL) app (fun us -> f (eClo us)) usL(* findMon f (G, sum) =
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
let rec unifySum(g,  , sum1,  , sum2) let let rec invertMon(g,  , mon [(lHS as eVar (r,  , _,  , _,  , _),  , s)],  , sum) if isPatSub s then let let  inlet  in in if invertible (g,  , (rHS,  , id),  , ss,  , r) then sOME (g,  , lHS,  , rHS,  , ss) else nONE else nONE invertMon_ nONE in match xorSum (sum2,  , sum1) with sum (false,  , nil) -> succeed nil sum (true,  , nil) -> fail sum -> (match findMon invertMon (g,  , sum) with sOME assignment -> succeed [assign assignment] nONE -> let let  inlet  in in succeed [delay (u,  , cnstr)])(* toFgn sum = U

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
let rec app(myIntsynRep sum)f appSum (f,  , sum) appfe_ raise ((unexpectedFgnExp fe))let rec equalTo(myIntsynRep sum)u2 (match xorSum (normalizeSum (sum),  , fromExp (u2,  , id))(* AK: redundant normalizeSum ? *)
 with sum (m,  , nil) -> (m = false) _ -> false) equalTofe_ raise ((unexpectedFgnExp fe))let rec unifyWith(myIntsynRep sum)(g,  , u2) unifySum (g,  , normalizeSum sum,  , fromExp (u2,  , id)) unifyWithfe_ raise ((unexpectedFgnExp fe))let rec installFgnExpOps() let let  inlet  inlet  inlet  inlet  inlet  in in ()let rec makeFgn(arity,  , opExp)(s) let let rec makeParams0 nil makeParamsn app (root (bVar (n),  , nil),  , makeParams (- (n,  , 1)))let rec makeLame0 e makeLamen lam (dec (nONE,  , bool ()),  , makeLam e (- (n,  , 1)))let rec expand((nil,  , s),  , arity) (makeParams arity,  , arity) expand((app (u,  , s),  , s),  , arity) let let  in in (app (eClo (u,  , comp (s,  , shift (arity'))),  , s'),  , arity') expand((sClo (s,  , s'),  , s),  , arity) expand ((s,  , comp (s',  , s)),  , arity)let  in in makeLam (toFgn (opExp s')) arity'let rec makeFgnUnaryopSum makeFgn (1,  , fun (app (u,  , nil)) -> opSum (fromExp (u,  , id)))let rec makeFgnBinaryopSum makeFgn (2,  , fun (app (u1,  , app (u2,  , nil))) -> opSum (fromExp (u1,  , id),  , fromExp (u2,  , id)))let rec arrow(u,  , v) pi ((dec (nONE,  , u),  , no),  , v)(* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
let rec init(cs,  , installF) (myID := cs; boolID := installF (conDec ("bool",  , nONE,  , 0,  , constraint (! myID,  , solveBool),  , uni (type),  , kind),  , nONE,  , [mnil]); trueID := installF (conDec ("true",  , nONE,  , 0,  , foreign (! myID,  , (fun _ -> toFgn (sum (true,  , nil)))),  , bool (),  , type),  , nONE,  , nil); falseID := installF (conDec ("false",  , nONE,  , 0,  , foreign (! myID,  , (fun _ -> toFgn (sum (false,  , nil)))),  , bool (),  , type),  , nONE,  , nil); notID := installF (conDec ("!",  , nONE,  , 0,  , foreign (! myID,  , makeFgnUnary notSum),  , arrow (bool (),  , bool ()),  , type),  , sOME (prefix (maxPrec)),  , nil); xorID := installF (conDec ("||",  , nONE,  , 0,  , foreign (! myID,  , makeFgnBinary xorSum),  , arrow (bool (),  , arrow (bool (),  , bool ())),  , type),  , sOME (infix (dec maxPrec,  , left)),  , nil); andID := installF (conDec ("&",  , nONE,  , 0,  , foreign (! myID,  , makeFgnBinary andSum),  , arrow (bool (),  , arrow (bool (),  , bool ())),  , type),  , sOME (infix (dec maxPrec,  , left)),  , nil); orID := installF (conDec ("|",  , nONE,  , 0,  , foreign (! myID,  , makeFgnBinary orSum),  , arrow (bool (),  , arrow (bool (),  , bool ())),  , type),  , sOME (infix (dec maxPrec,  , left)),  , nil); impliesID := installF (conDec ("=>",  , nONE,  , 0,  , foreign (! myID,  , makeFgnBinary impliesSum),  , arrow (bool (),  , arrow (bool (),  , bool ())),  , type),  , sOME (infix (dec (dec maxPrec),  , left)),  , nil); iffID := installF (conDec ("<=>",  , nONE,  , 0,  , foreign (! myID,  , makeFgnBinary iffSum),  , arrow (bool (),  , arrow (bool (),  , bool ())),  , type),  , sOME (infix (dec (dec maxPrec),  , left)),  , nil); installFgnExpOps (); ())let  inend