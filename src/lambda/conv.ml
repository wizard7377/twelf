Conv  Whnf WHNF     CONV  struct (*! structure IntSyn = IntSyn' !*)
open IntSyn (* eqUni (L1, L2) = B iff L1 = L2 *)
let rec eqUni(type,  , type) true eqUni(kind,  , kind) true eqUni_ false(* convExpW ((U1, s1), (U2, s2)) = B

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1) in whnf
            G |- s2 : G2    G2 |- U2 : V2    (U2,s2) in whnf
            G |- V1[s1] == V2[s2] == V : L
       then B iff G |- U1[s1] == U2[s2] : V

       Effects: EVars may be lowered
    *)
let rec convExpW((uni (l1),  , _),  , (uni (l2),  , _)) eqUni (l1,  , l2) convExpW(us1 as (root (h1,  , s1),  , s1),  , us2 as (root (h2,  , s2),  , s2)) (match (h1,  , h2) with (bVar (k1),  , bVar (k2)) -> (k1 = k2) && convSpine ((s1,  , s1),  , (s2,  , s2)) (const (c1),  , const (c2)) -> (c1 = c2) && convSpine ((s1,  , s1),  , (s2,  , s2)) (skonst c1,  , skonst c2) -> (c1 = c2) && convSpine ((s1,  , s1),  , (s2,  , s2)) (proj (bidx v1,  , i1),  , proj (bidx v2,  , i2)) -> (v1 = v2) && (i1 = i2) && convSpine ((s1,  , s1),  , (s2,  , s2)) (fVar (n1,  , _,  , s1'),  , fVar (n2,  , _,  , s2')) -> (* s1' = s2' = ^|G| *)
(n1 = n2) && convSpine ((s1,  , s1),  , (s2,  , s2)) (fgnConst (cs1,  , cD1),  , fgnConst (cs2,  , cD2)) -> (* they must have the same string representation *)
(cs1 = cs2) && (conDecName (cD1) = conDecName (cD2)) && convSpine ((s1,  , s1),  , (s2,  , s2)) (def (d1),  , def (d2)) -> (* because of strict *)
((d1 = d2) && convSpine ((s1,  , s1),  , (s2,  , s2))) || convExpW (expandDef (us1),  , expandDef (us2)) (def (d1),  , _) -> convExpW (expandDef us1,  , us2) (_,  , def (d2)) -> convExpW (us1,  , expandDef us2) _ -> false) convExpW((pi (dP1,  , v1),  , s1),  , (pi (dP2,  , v2),  , s2)) convDecP ((dP1,  , s1),  , (dP2,  , s2)) && convExp ((v1,  , dot1 s1),  , (v2,  , dot1 s2)) convExpW(us1 as (pi _,  , _),  , us2 as (root (def _,  , _),  , _)) convExpW (us1,  , expandDef us2) convExpW(us1 as (root (def _,  , _),  , _),  , us2 as (pi _,  , _)) convExpW (expandDef us1,  , us2) convExpW((lam (d1,  , u1),  , s1),  , (lam (d2,  , u2),  , s2)) convExp ((u1,  , dot1 s1),  , (u2,  , dot1 s2)) convExpW((lam (d1,  , u1),  , s1),  , (u2,  , s2)) convExp ((u1,  , dot1 s1),  , (redex (eClo (u2,  , shift),  , app (root (bVar (1),  , nil),  , nil)),  , dot1 s2)) convExpW((u1,  , s1),  , (lam (d2,  , u2),  , s2)) convExp ((redex (eClo (u1,  , shift),  , app (root (bVar (1),  , nil),  , nil)),  , dot1 s1),  , (u2,  , dot1 s2)) convExpW((fgnExp csfe1,  , s1),  , us2) apply csfe1 (eClo us2) convExpW(us1,  , (fgnExp csfe2,  , s2)) apply csfe2 (eClo us1) convExpW((eVar (r1,  , _,  , _,  , _),  , s1),  , (eVar (r2,  , _,  , _,  , _),  , s2)) (r1 = r2) && convSub (s1,  , s2) convExpW_ false(* Possible are:
           L <> Pi D. V   Pi D. V <> L
           X <> U         U <> X
        *)
(* convExp ((U1, s1), (U2, s2)) = B

       Invariant:
       as above, but (U1, s1), (U2, s2) need not to be in whnf
       Effects: EVars may be lowered
    *)
 convExp(us1,  , us2) convExpW (whnf us1,  , whnf us2)(* convSpine ((S1, s1), (S2, s2)) = B

       Invariant:
       If   G |- s1 : G1     G1 |- S1 : V1 > W1
            G |- s2 : G2    G2 |- S2 : V2 > W2
            G |- V1[s1] = V2[s2] = V : L
            G |- W1[s1] = W2[s2] = W : L
       then B iff G |- S1 [s1] = S2 [s2] : V > W

       Effects: EVars may be lowered
    *)
 convSpine((nil,  , _),  , (nil,  , _)) true convSpine((app (u1,  , s1),  , s1),  , (app (u2,  , s2),  , s2)) convExp ((u1,  , s1),  , (u2,  , s2)) && convSpine ((s1,  , s1),  , (s2,  , s2)) convSpine((sClo (s1,  , s1'),  , s1),  , ss2) convSpine ((s1,  , comp (s1',  , s1)),  , ss2) convSpine(ss1,  , (sClo (s2,  , s2'),  , s2)) convSpine (ss1,  , (s2,  , comp (s2',  , s2))) convSpine(_,  , _) false(* bp*)
(* no others are possible due to typing invariants *)
(* convSub (s1, s2) = B

     Invariant:
     If  G |- s1 : G'
         G |- s2 : G'
     then B iff G |- s1 = s2 : G'
     Effects: EVars may be lowered
    *)
 convSub(shift (n),  , shift (m)) true convSub(shift (n),  , s2 as dot _) convSub (dot (idx (n + 1),  , shift (n + 1)),  , s2) convSub(s1 as dot _,  , shift (m)) convSub (s1,  , dot (idx (m + 1),  , shift (m + 1))) convSub(dot (ft1,  , s1),  , dot (ft2,  , s2)) (match (ft1,  , ft2) with (idx (n1),  , idx (n2)) -> (n1 = n2) (exp (u1),  , exp (u2)) -> convExp ((u1,  , id),  , (u2,  , id)) (block (bidx k1),  , block (bidx k2)) -> (k1 = k2)(* other block cases don't matter -cs 2/18/03 *)
 (exp (u1),  , idx (n2)) -> convExp ((u1,  , id),  , (root (bVar (n2),  , nil),  , id)) (idx (n1),  , exp (u2)) -> convExp ((root (bVar (n1),  , nil),  , id),  , (u2,  , id)) (undef,  , undef) -> true _ -> false) && convSub (s1,  , s2)(* convDec ((x1:V1, s1), (x2:V2, s2)) = B

       Invariant:
       If   G |- s1 : G'     G'  |- V1 : L
            G |- s2 : G''    G'' |- V2 : L
       then B iff G |- V1 [s1]  = V2 [s2] : L
       Effects: EVars may be lowered
    *)
 convDec((dec (_,  , v1),  , s1),  , (dec (_,  , v2),  , s2)) convExp ((v1,  , s1),  , (v2,  , s2)) convDec((bDec (_,  , (c1,  , s1)),  , t1),  , (bDec (_,  , (c2,  , s2)),  , t2)) c1 = c2 && convSub (comp (s1,  , t1),  , comp (s2,  , t2))(* convDecP see convDec *)
 convDecP(((d1,  , p1),  , s1),  , ((d2,  , p2),  , s2)) convDec ((d1,  , s1),  , (d2,  , s2))let  inlet  inlet  in(* local *)
end