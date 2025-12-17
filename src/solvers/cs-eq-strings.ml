CSEqStrings  Whnf WHNF    Unify UNIFY     CS  struct (*! structure CSManager = CSManager !*)
open IntSyn module module (* CSManager.ModeSyn *)
let  inlet  inlet rec string() root (const (! stringID),  , nil)let  inlet rec concatExp(u,  , v) root (const (! concatID),  , app (u,  , app (v,  , nil)))let rec toStrings ("\"" ^ s ^ "\"")let rec stringConDec(str) conDec (toString (str),  , nONE,  , 0,  , normal,  , string (),  , type)let rec stringExp(str) root (fgnConst (! myID,  , stringConDec (str)),  , nil)(* fromString string =
         SOME(str)  if string parses to the string str
         NONE       otherwise
    *)
let rec fromStringstring let let  in in if (sub (string,  , 0) = '\"') && (sub (string,  , len - 1) = '\"') then sOME (substring (string,  , 1,  , len - 2)) else nONE(* parseString string = SOME(conDec) or NONE

       Invariant:
       If str parses to the string str
       then conDec is the (foreign) constant declaration of str
    *)
let rec parseStringstring (match fromString (string) with sOME (str) -> sOME (stringConDec (str)) nONE -> nONE)(* solveString str = SOME(U)

       Invariant:
       U is the term obtained applying the foreign constant
       corresponding to the string str to an empty spine
    *)
let rec solveString(g,  , s,  , k) sOME (stringExp (toString k))type Concat(* Concatenation:             *)
(* Concat::= A1 ++ A2 ++ ...  *)
 Atom(*        | (U,s)             *)
exception (* Internal syntax representation of this module *)
let rec extractConcat(myIntsynRep concat) concat extractConcatfe raise ((unexpectedFgnExp fe))(* A concatenation is said to be normal if
         (a) it does not contain empty string atoms
         (b) it does not contain two consecutive string atoms
    *)
(* ... and Exp atoms are in whnf?  - ak *)
(* toExp concat = U

       Invariant:
       If concat is normal
       G |- U : V and U is the Twelf syntax conversion of concat
    *)
let rec toExp(concat nil) stringExp "" toExp(concat [string str]) stringExp str toExp(concat [exp (u,  , shift (0))]) u toExp(concat [exp us]) eClo us toExp(concat (a :: aL)) concatExp (toExp (concat [a]),  , toExp (concat aL))(* catConcat (concat1, concat2) = concat3

       Invariant:
       If   concat1 normal
       and  concat2 normal
       then concat3 normal
       and  concat3 = concat1 ++ concat2
    *)
let rec catConcat(concat nil,  , concat2) concat2 catConcat(concat1,  , concat nil) concat1 catConcat(concat aL1,  , concat aL2) (match (rev aL1,  , aL2) with ((string str1) :: revAL1',  , (string str2) :: aL2') -> concat ((rev revAL1') @ ((string (str1 ^ str2)) :: aL2')) (_,  , _) -> concat (aL1 @ aL2))(* fromExpW (U, s) = concat

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then concat is the representation of U[s] as concatenation of atoms
       and  concat is normal
    *)
let rec fromExpW(us as (fgnExp (cs,  , fe),  , _)) if (cs = ! myID) then normalize (extractConcat fe) else concat [exp us] fromExpW(us as (root (fgnConst (cs,  , conDec),  , _),  , _)) if (cs = ! myID) then (match fromString (conDecName (conDec)) with sOME (str) -> if (str = "") then concat nil else concat [string str]) else concat [exp us] fromExpWus concat [exp us](* fromExp (U, s) = concat

       Invariant:
       If   G' |- s : G    G |- U : V
       then concat is the representation of U[s] as concatenation of atoms
       and  concat is normal
    *)
 fromExpus fromExpW (whnf us)(* normalize concat = concat', where concat' normal and concat' = concat *)
 normalize(concat as (concat nil)) concat normalize(concat as (concat [string str])) concat normalize(concat [exp us]) fromExp us normalize(concat (a :: aL)) catConcat (normalize (concat [a]),  , normalize (concat aL))(* mapSum (f, A1 + ...) = f(A1) ++ ... *)
let rec mapConcat(f,  , concat aL) let let rec mapConcat'nil nil mapConcat'((exp us) :: aL) (exp (f (eClo us),  , id)) :: mapConcat' aL mapConcat'((string str) :: aL) (string str) :: mapConcat' aL in concat (mapConcat' aL)(* appConcat (f, A1 + ... ) = ()  and f(Ui) for Ai = Exp Ui *)
let rec appConcat(f,  , concat aL) let let rec appAtom(exp us) f (eClo us) appAtom(string _) () in app appAtom aL(* Split:                                         *)
(* Split ::= str1 ++ str2                         *)
type Split(* Decomposition:                                 *)
(* Decomp ::= toParse | [parsed1, ..., parsedn]   *)
type Decomp(* index (str1, str2) = [idx1, ..., idxn]
       where the idxk are all the positions in str2 where str1 appear.
    *)
let rec index(str1,  , str2) let let  inlet rec index'i if (i <= max) then if isPrefix str1 (extract (str2,  , i,  , nONE)) then i :: index' (i + 1) else index' (i + 1) else nil in index' 0(* split (str1, str2) = [Split(l1,r1), ..., Split(ln,rn)]
       where, for each k, str2 = lk ++ str1 ++ rk.
    *)
let rec split(str1,  , str2) let let  inlet rec split'i split (extract (str2,  , 0,  , sOME (i)),  , extract (str2,  , i + len,  , nONE)) in map split' (index (str1,  , str2))(* sameConcat (concat1, concat2) =
         true only if concat1 = concat2 (as concatenations)
    *)
let rec sameConcat(concat aL1,  , concat aL2) let let rec sameConcat'(nil,  , nil) true sameConcat'((string str1) :: aL1,  , (string str2) :: aL2) (str1 = str2) && sameConcat' (aL1,  , aL2) sameConcat'((exp us1) :: aL1,  , (exp us2) :: aL2) sameExp (us1,  , us2) && sameConcat' (aL1,  , aL2) sameConcat'_ false in sameConcat' (aL1,  , aL2)(* sameExpW ((U1,s1), (U2,s2)) = T

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
 sameSub(shift _,  , shift _) true sameSub(dot (idx (k1),  , s1),  , dot (idx (k2),  , s2)) (k1 = k2) && sameSub (s1,  , s2) sameSub(s1 as dot (idx _,  , _),  , shift (k2)) sameSub (s1,  , dot (idx (+ (k2,  , 1)),  , shift (+ (k2,  , 1)))) sameSub(shift (k1),  , s2 as dot (idx _,  , _)) sameSub (dot (idx (+ (k1,  , 1)),  , shift (+ (k1,  , 1))),  , s2) sameSub_ false(* Unification Result:
       StringUnify ::= {G1 |- X1 := U1[s1], ..., Gn |- Xn := Un[sn]}
                     | {delay U1 on cnstr1, ..., delay Un on cnstrn}
                     | Failure
    *)
type StringUnify(* toFgnUnify stringUnify = result
       where result is obtained translating stringUnify.
    *)
let rec toFgnUnify(multAssign l) succeed (map (fun gXUss -> assign gXUss) l) toFgnUnify(multDelay (uL,  , cnstr)) succeed (map (fun u -> delay (u,  , cnstr)) uL) toFgnUnify(failure) fail(* unifyRigid (G, concat1, concat2) = stringUnify

       Invariant:
       If   G |- concat1 : string    concat1 normal
       and  G |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. G |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else stringUnify = Failure
    *)
 unifyRigid(g,  , concat aL1,  , concat aL2) let let rec unifyRigid'(nil,  , nil) multAssign nil unifyRigid'((string str1) :: aL1,  , (string str2) :: aL2) if (str1 = str2) then unifyRigid' (aL1,  , aL2) else failure unifyRigid'((exp (u1 as (eVar (r,  , _,  , _,  , _)),  , s)) :: aL1,  , (exp (u2 as (root (fVar _,  , _)),  , _)) :: aL2) let let  in in if invertible (g,  , (u2,  , id),  , ss,  , r) then (match (unifyRigid' (aL1,  , aL2)) with multAssign l -> multAssign ((g,  , u1,  , u2,  , ss) :: l) failure -> failure) else failure unifyRigid'((exp (u1 as (root (fVar _,  , _)),  , _)) :: aL1,  , (exp (u2 as (eVar (r,  , _,  , _,  , _)),  , s)) :: aL2) let let  in in if invertible (g,  , (u1,  , id),  , ss,  , r) then (match (unifyRigid' (aL1,  , aL2)) with multAssign l -> multAssign ((g,  , u2,  , u1,  , ss) :: l) failure -> failure) else failure unifyRigid'((exp (us1 as (root (fVar _,  , _),  , _))) :: aL1,  , (exp (us2 as (root (fVar _,  , _),  , _))) :: aL2) if (sameExpW (us1,  , us2)) then unifyRigid' (aL1,  , aL2) else failure unifyRigid'((exp (us1 as (eVar (_,  , _,  , _,  , _),  , _))) :: aL1,  , (exp (us2 as (eVar (_,  , _,  , _,  , _),  , _))) :: aL2) if (sameExpW (us1,  , us2)) then unifyRigid' (aL1,  , aL2) else failure unifyRigid'_ failure in unifyRigid' (aL1,  , aL2)(* unifyString (G, concat, str, cnstr) = stringUnify

       Invariant:
       If   G |- concat : string    concat1 normal
       then if there is an instantiation I :
               s.t. G |- concat <I> == str
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [U1, ..., Un] cnstr
                   where U1, ..., Un are expression to be delayed on cnstr
    *)
let rec unifyString(g,  , concat (string prefix :: aL),  , str,  , cnstr) if (isPrefix prefix str) then let let  in in unifyString (g,  , concat aL,  , suffix,  , cnstr) else failure unifyString(g,  , concat aL,  , str,  , cnstr) let let rec unifyString'(aL,  , nil) (failure,  , nil) unifyString'(nil,  , [decomp (parse,  , parsedL)]) (multAssign nil,  , parse :: parsedL) unifyString'(nil,  , candidates) (multDelay (nil,  , cnstr),  , nil) unifyString'((exp us1) :: (exp us2) :: aL,  , _) (multDelay ([eClo us1; eClo us2],  , cnstr),  , nil) unifyString'((exp (u as (eVar (r,  , _,  , _,  , _)),  , s)) :: aL,  , candidates) if (isPatSub s) then let let rec assignrnil nONE assignr((_,  , eVar (r',  , _,  , _,  , _),  , root (fgnConst (cs,  , conDec),  , nil),  , _) :: l) if (r = r') then fromString (conDecName (conDec)) else assign r l assignr(_ :: l) assign r l in (match unifyString' (aL,  , candidates) with (multAssign l,  , parsed :: parsedL) -> (match (assign r l) with nONE -> let let  inlet  in in (multAssign ((g,  , u,  , w,  , ss) :: l),  , parsedL) sOME (parsed') -> if (parsed = parsed') then (multAssign l,  , parsedL) else (failure,  , nil)) (multDelay (uL,  , cnstr),  , _) -> (multDelay ((eClo (u,  , s)) :: uL,  , cnstr),  , nil) (failure,  , _) -> (failure,  , nil)) else (multDelay ([eClo (u,  , s)],  , cnstr),  , nil) unifyString'((exp us) :: aL,  , _) (multDelay ([eClo us],  , cnstr),  , nil) unifyString'([string str],  , candidates) let let rec successors(decomp (parse,  , parsedL)) mapPartial (fun (split (prefix,  , "")) -> sOME (decomp (prefix,  , parsedL)) (split (prefix,  , suffix)) -> nONE) (split (str,  , parse))let  in in unifyString' (nil,  , candidates') unifyString'((string str) :: aL,  , candidates) let let rec successors(decomp (parse,  , parsedL)) map (fun (split (prefix,  , suffix)) -> decomp (suffix,  , prefix :: parsedL)) (split (str,  , parse))let  in in unifyString' (aL,  , candidates') in (match unifyString' (aL,  , [decomp (str,  , nil)]) with (result,  , nil) -> result (result,  , [""]) -> result (result,  , parsedL) -> failure)(* unifyConcat (G, concat1, concat2) = stringUnify

       Invariant:
       If   G |- concat1 : string    concat1 normal
       and  G |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. G |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [U1, ..., Un] cnstr
                   where U1, ..., Un are expression to be delayed on cnstr
    *)
let rec unifyConcat(g,  , concat1 as (concat aL1),  , concat2 as (concat aL2)) let let  inlet  inlet  in in match (aL1,  , aL2) with (nil,  , nil) -> multAssign nil(* FIX: the next two cases are wrong -kw *)
 (nil,  , _) -> failure (_,  , nil) -> failure ([string str1],  , [string str2]) -> if (str1 = str2) then (multAssign nil) else failure ([exp (u as (eVar (r,  , _,  , _,  , _)),  , s)],  , _) -> if (isPatSub s) then let let  in in if invertible (g,  , (u2,  , id),  , ss,  , r) then (multAssign [(g,  , u,  , u2,  , ss)]) else multDelay ([u1; u2],  , cnstr) else multDelay ([u1; u2],  , cnstr) (_,  , [exp (u as (eVar (r,  , _,  , _,  , _)),  , s)]) -> if (isPatSub s) then let let  in in if invertible (g,  , (u1,  , id),  , ss,  , r) then (multAssign [(g,  , u,  , u1,  , ss)]) else multDelay ([u1; u2],  , cnstr) else multDelay ([u1; u2],  , cnstr) ([string str],  , _) -> unifyString (g,  , concat2,  , str,  , cnstr) (_,  , [string str]) -> unifyString (g,  , concat1,  , str,  , cnstr) _ -> (match (unifyRigid (g,  , concat1,  , concat2)) with (result as (multAssign _)) -> result failure -> if (sameConcat (concat1,  , concat2)) then multAssign nil else multDelay ([u1; u2],  , cnstr))(* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *)
 toFgn(concat as (concat [string str])) stringExp (str) toFgn(concat as (concat [exp (u,  , id)])) u toFgn(concat) fgnExp (! myID,  , myIntsynRep concat)(* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep concat) and concat : normal
       then U is the Twelf syntax conversion of concat
    *)
let rec toInternal(myIntsynRep concat)() toExp (normalize concat) toInternalfe() raise ((unexpectedFgnExp fe))(* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep concat)   concat : normal
       and
         f concat = f (A1 ++ ... ++ AN )
                  = f (A1) ++ ... ++ f (AN)
                  = concat'           concat' : normal
       then
         U' is a foreign expression representing concat'
    *)
let rec map(myIntsynRep concat)f toFgn (normalize (mapConcat (f,  , concat))) mapfe_ raise ((unexpectedFgnExp fe))(* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep concat)     concat : normal
       and
          concat = A1 ++ ... ++ AN
          where some Ai are (Exp Usi)
       then f is applied to each Usi
       (since concat : normal, each Usij is in whnf)
    *)
let rec app(myIntsynRep concat)f appConcat (f,  , concat) appfe_ raise ((unexpectedFgnExp fe))let rec equalTo(myIntsynRep concat)u2 sameConcat (normalize (concat),  , fromExp (u2,  , id)) equalTofe_ raise ((unexpectedFgnExp fe))let rec unifyWith(myIntsynRep concat)(g,  , u2) toFgnUnify (unifyConcat (g,  , normalize (concat),  , fromExp (u2,  , id))) unifyWithfe_ raise ((unexpectedFgnExp fe))let rec installFgnExpOps() let let  inlet  inlet  inlet  inlet  inlet  in in ()let rec makeFgn(arity,  , opExp)(s) let let rec makeParams0 nil makeParamsn app (root (bVar (n),  , nil),  , makeParams (n - 1))let rec makeLame0 e makeLamen lam (dec (nONE,  , string ()),  , makeLam e (n - 1))let rec expand((nil,  , s),  , arity) (makeParams arity,  , arity) expand((app (u,  , s),  , s),  , arity) let let  in in (app (eClo (u,  , comp (s,  , shift (arity'))),  , s'),  , arity') expand((sClo (s,  , s'),  , s),  , arity) expand ((s,  , comp (s,  , s')),  , arity)let  in in makeLam (toFgn (opExp s')) arity'let rec makeFgnBinaryopConcat makeFgn (2,  , fun (app (u1,  , app (u2,  , nil))) -> opConcat (fromExp (u1,  , id),  , fromExp (u2,  , id)))let rec arrow(u,  , v) pi ((dec (nONE,  , u),  , no),  , v)(* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
let rec init(cs,  , installF) (myID := cs; stringID := installF (conDec ("string",  , nONE,  , 0,  , constraint (! myID,  , solveString),  , uni (type),  , kind),  , nONE,  , [mnil]); concatID := installF (conDec ("++",  , nONE,  , 0,  , foreign (! myID,  , makeFgnBinary catConcat),  , arrow (string (),  , arrow (string (),  , string ())),  , type),  , sOME (infix (maxPrec,  , right)),  , nil); installFgnExpOps (); ())let  inend