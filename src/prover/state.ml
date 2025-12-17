State  Formatter FORMATTER     STATE  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
module type State(* StateLF X, X is always lowered *)
type Focus(* datatype State
    = State of (Tomega.Dec IntSyn.Ctx * Tomega.For) * Tomega.Worlds
 *)
(*  datatype SideCondition  (* we need some work here *)
    = None
    | All   of SideCondition
    | And   of SideCondition * SideCondition
    | Order of Order.Predicate
*)
exception module module (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
let rec findPrg(lam (_,  , p)) findPrg p findPrg(new p) findPrg p findPrg(choose p) findPrg p findPrg(pairExp (_,  , p)) findPrg p findPrg(pairBlock (b,  , p)) findPrg p findPrg(pairPrg (p1,  , p2)) findPrg p1 @ findPrg p2 findPrg(unit) [] findPrg(rec (_,  , p)) findPrg p findPrg(case (cases c)) findCases c findPrg(pClo (p,  , t)) findPrg p @ findSub t findPrg(let (d,  , p1,  , p2)) findPrg p1 @ findPrg p2 findPrg(letPairExp (d1,  , d2,  , p1,  , p2)) findPrg p1 @ findPrg p2 findPrg(letUnit (p1,  , p2)) findPrg p1 @ findPrg p2 findPrg(x as eVar (_,  , ref nONE,  , _,  , _,  , _,  , _)) [x] findPrg(x as eVar (_,  , ref (sOME p),  , _,  , _,  , _,  , _)) findPrg p findPrg(const _) [] findPrg(var _) [] findPrg(redex (p,  , s)) findPrg p @ findSpine s findCasesnil [] findCases((_,  , _,  , p) :: c) findPrg p @ findCases c findSub(shift _) [] findSub(dot (f,  , t)) findFront f @ findSub t findFront(idx _) [] findFront(prg p) findPrg p findFront(exp _) [] findFront(block _) [] findFront(undef) [] findSpine(nil) [] findSpine(appPrg (p,  , s)) findPrg p @ findSpine s findSpine(appExp (_,  , s)) findSpine s findSpine(appBlock (_,  , s)) findSpine s(* by invariant: blocks don't contain free evars *)
(* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
let rec findExp(psi,  , lam (d,  , p))k findExp (decl (psi,  , d),  , p) k findExp(psi,  , new p)k findExp (psi,  , p) k findExp(psi,  , choose p)k findExp (psi,  , p) k findExp(psi,  , pairExp (m,  , p))k findExp (psi,  , p) (collectEVars (coerceCtx psi,  , (m,  , id),  , k)) findExp(psi,  , pairBlock (b,  , p))k findExp (psi,  , p) k findExp(psi,  , pairPrg (p1,  , p2))k findExp (psi,  , p2) (findExp (psi,  , p1) k) findExp(psi,  , unit)k k findExp(psi,  , rec (d,  , p))k findExp (psi,  , p) k findExp(psi,  , case (cases c))k findExpCases (psi,  , c) k findExp(psi,  , pClo (p,  , t))k findExpSub (psi,  , t) (findExp (psi,  , p) k) findExp(psi,  , let (d,  , p1,  , p2))k findExp (decl (psi,  , d),  , p2) (findExp (psi,  , p1) k) findExp(psi,  , letPairExp (d1,  , d2,  , p1,  , p2))k findExp (decl (decl (psi,  , uDec d1),  , d2),  , p2) (findExp (psi,  , p1) k) findExp(psi,  , letUnit (p1,  , p2))k findExp (psi,  , p2) (findExp (psi,  , p1) k) findExp(psi,  , x as eVar _)k k findExp(psi,  , const _)k k findExp(psi,  , var _)k k findExp(psi,  , redex (p,  , s))k findExpSpine (psi,  , s) k findExpSpine(psi,  , nil)k k findExpSpine(psi,  , appPrg (_,  , s))k findExpSpine (psi,  , s) k findExpSpine(psi,  , appExp (m,  , s))k findExpSpine (psi,  , s) (collectEVars (coerceCtx psi,  , (m,  , id),  , k)) findExpSpine(psi,  , appBlock (_,  , s))k findExpSpine (psi,  , s) k findExpCases(psi,  , nil)k k findExpCases(psi,  , (_,  , _,  , p) :: c)k findExpCases (psi,  , c) (findExp (psi,  , p) k) findExpSub(psi,  , shift _)k k findExpSub(psi,  , dot (f,  , t))k findExpSub (psi,  , t) (findExpFront (psi,  , f) k) findExpFront(psi,  , idx _)k k findExpFront(psi,  , prg p)k findExp (psi,  , p) k findExpFront(psi,  , exp m)k collectEVars (coerceCtx psi,  , (m,  , id),  , k) findExpFront(psi,  , block _)k k findExpFront(psi,  , undef)k k(* init F = S

       Invariant:
       S = (. |> F) is the initial state
    *)
let rec init(f,  , w) let let  in in state (w,  , null,  , x,  , f)(* close S = B

       Invariant:
       If  B holds iff S  doesn't contain any free subgoals
    *)
let rec close(state (w,  , _,  , p,  , _)) (match (findPrg p,  , findExp (null,  , p) []) with (nil,  , nil) -> true _ -> false)let  inlet  inlet  inlet  inlet  inend