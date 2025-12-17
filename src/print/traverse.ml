Traverse  Whnf WHNF    Names NAMES    Traverser' TRAVERSER     TRAVERSE  struct (*! structure IntSyn = IntSyn' !*)
module exception module module (* from typecheck.fun *)
(* inferCon (G, C) = V'

     Invariant:
     If    G |- C : V
     and  (C  doesn't contain FVars)
     then  G' |- V' : L      (for some level L)
     and   G |- V = V' : L
     else exception Error is raised.
  *)
let rec inferConW(g,  , bVar (k')) let let  in in whnf (v,  , id) inferConW(g,  , const (c)) (constType (c),  , id) inferConW(g,  , def (d)) (constType (d),  , id)(* no case for FVar, Skonst *)
let rec fromHead(g,  , bVar (n)) bvar (bvarName (g,  , n)) fromHead(g,  , const (cid)) let let  in in const (ids,  , id) fromHead(g,  , def (cid)) let let  in in def (ids,  , id) fromHead_ raise (error ("Head not recognized"))(* see also: print.fun *)
let rec impCon(const (cid)) constImp (cid) impCon(def (cid)) constImp (cid) impCon_ 0(* see also: print.fun *)
(*
  fun dropImp (0, S) = S
    | dropImp (i, I.App (U, S)) = dropImp (i-1, S)
    | dropImp (i, I.SClo (S, s)) = I.SClo (dropImp (i, S), s)
    | dropImp _ = raise Error ("Missing implicit arguments")
  *)
let rec fromTpW(g,  , (root (c,  , s),  , s)) atom (fromHead (g,  , c),  , fromSpine (impCon c,  , g,  , (s,  , s),  , inferConW (g,  , c))) fromTpW(g,  , (pi ((d as dec (_,  , v1),  , no),  , v2),  , s)) arrow (fromTp (g,  , (v1,  , s)),  , fromTp (decl (g,  , decSub (d,  , s)),  , (v2,  , dot1 s))) fromTpW(g,  , (pi ((d,  , maybe),  , v2),  , s)) let let  in in pi (fromDec (g,  , (d',  , s)),  , fromTp (decl (g,  , decSub (d',  , s)),  , (v2,  , dot1 s))) fromTpW_ raise (error ("Type not recognized")) fromTp(g,  , vs) fromTpW (g,  , whnf vs) fromObjW(g,  , (root (c,  , s),  , s),  , (v,  , t)) root (fromHead (g,  , c),  , fromSpine (impCon c,  , g,  , (s,  , s),  , inferConW (g,  , c)),  , fromTp (g,  , (v,  , t))) fromObjW(g,  , (lam (d,  , u),  , s),  , (pi (_,  , v),  , t)) let let  in in lam (fromDec (g,  , (d',  , s)),  , fromObj (decl (g,  , decSub (d',  , s)),  , (u,  , dot1 s),  , (v,  , dot1 t))) fromObjW_ raise (error ("Object not recognized")) fromObj(g,  , us,  , vt) fromObjW (g,  , whnf us,  , whnf vt) fromSpine(i,  , g,  , (nil,  , s),  , vt) nils fromSpine(i,  , g,  , (sClo (s,  , s'),  , s),  , vt) fromSpine (i,  , g,  , (s,  , comp (s',  , s)),  , vt) fromSpine(i,  , g,  , (app (u,  , s),  , s),  , (pi ((dec (_,  , v1),  , _),  , v2),  , t)) if i > 0(* drop implicit arg *)
 then fromSpine (i - 1,  , g,  , (s,  , s),  , whnf (v2,  , dot (exp (eClo (u,  , s)),  , t))) else app (fromObj (g,  , (u,  , s),  , (v1,  , t)),  , fromSpine (i,  , g,  , (s,  , s),  , whnf (v2,  , dot (exp (eClo (u,  , s)),  , t)))) fromDec(g,  , (dec (sOME (x),  , v),  , s)) dec (x,  , fromTp (g,  , (v,  , s)))(* NONE should not occur because of call to decName *)
(*
    | fromDec (G, (I.Dec (NONE, V), s)) =
        T.dec ("_", fromTp (G, (V, s)))
    *)
(* ignore a : K, d : A = M, b : K = A, and skolem constants *)
let rec fromConDec(conDec (c,  , parent,  , i,  , _,  , v,  , type)) sOME (objdec (c,  , fromTp (null,  , (v,  , id)))) fromConDec_ nONElet  inlet rec const(name) let let  inlet  inlet rec getConDec(nONE) raise (error ("Undeclared identifier " ^ qidToString qid)) getConDec(sOME cid) sgnLookup cidlet  inlet  inlet rec result(nONE) raise (error ("Wrong kind of declaration")) result(sOME (r)) r in result (fromConDec conDec)(* local ... *)
end