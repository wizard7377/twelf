(* Solver for_sml machine integers *)


(* Author: Roberto Virga *)


module CSIntWord val wordSize : int (Whnf : WHNF) (Unify : UNIFY) : CS = struct (*! structure CSManager = CSManager !*)

open IntSyn
module W = LargeWord
module FX = CSManagerFixity
module MS = ModeSyn
(* CSManager.ModeSyn *)

exception MyFgnCnstrRepPlus of dctx * exp * exp * exp * exp
(* FgnCnstr Representation: (G, proof, U1, U2, U3) *)

exception MyFgnCnstrRepTimes of dctx * exp * exp * exp * exp
exception MyFgnCnstrRepQuot of dctx * exp * exp * exp * exp
let wordSize' = Int.min (wordSize, W.wordSize)
let zero = W.fromInt 0
let max = W.>> (W.notb zero, Word.fromInt (W.wordSize - wordSize'))
(* numCheck (d) = true iff d <= max *)

let rec numCheck (d)  = W.<= (d, max)
(* plusCheck (d1, d2) = true iff d1 + d2 <= max *)

let rec plusCheck (d1, d2)  = ( let d3 = W.+ (d1, d2) in  W.>= (d3, d1) && W.>= (d3, d2) && W.<= (d3, max) )
(* timesCheck (d1, d2) = true iff d1 * d2 <= max *)

let rec timesCheck (d1, d2)  = if (d1 = zero || d2 = zero) then true else ( let d3 = W.div (W.div (max, d1), d2) in  W.> (d3, zero) )
(* quotCheck (d1, d2) = true iff  d2 != zero *)

let rec quotCheck (d1, d2)  = W.> (d2, zero)
(* constraint solver ID of this module *)

let myID = (ref -1 : csid ref)
(* constant ID of the type family constant "wordXX" *)

let wordID = (ref -1 : cid ref)
let rec word ()  = Root (Const (! wordID), Nil)
(* constant ID's of the operators defined by this module *)

let plusID = (ref -1 : cid ref)
(* + : wordXX -> wordXX -> wordXX -> type *)

let timesID = (ref -1 : cid ref)
(* * : wordXX -> wordXX -> wordXX -> type *)

let quotID = (ref -1 : cid ref)
(* / : wordXX -> wordXX -> wordXX -> type *)

let rec plusExp (U, V, W)  = Root (Const (! plusID), App (U, App (V, App (W, Nil))))
let rec timesExp (U, V, W)  = Root (Const (! timesID), App (U, App (V, App (W, Nil))))
let rec quotExp (U, V, W)  = Root (Const (! quotID), App (U, App (V, App (W, Nil))))
(* constant ID's of the proof object generators and their proof objects *)

(* (these are workaround for_sml the lack of sigma types in Twelf)  *)

let provePlusID = (ref -1 : cid ref)
(* prove+ : {U}{V}{W} + U V W -> type *)

let proveTimesID = (ref -1 : cid ref)
(* prove* : {U}{V}{W} * U V W -> type *)

let proveQuotID = (ref -1 : cid ref)
(* prove/ : {U}{V}{W} / U V W -> type *)

let proofPlusID = (ref -1 : cid ref)
(* proof* : {U}{V}{W}{P} prove+ U V W P *)

let proofTimesID = (ref -1 : cid ref)
(* proof* : {U}{V}{W}{P} prove* U V W P *)

let proofQuotID = (ref -1 : cid ref)
(* proof/ : {U}{V}{W}{P} prove/ U V W P *)

let rec provePlusExp (U, V, W, P)  = Root (Const (! provePlusID), App (U, App (V, App (W, App (P, Nil)))))
let rec proofPlusExp (U, V, W, P)  = Root (Const (! proofPlusID), App (U, App (V, App (W, App (P, Nil)))))
let rec proofTimesExp (U, V, W, P)  = Root (Const (! proofTimesID), App (U, App (V, App (W, App (P, Nil)))))
let rec proveTimesExp (U, V, W, P)  = Root (Const (! proveTimesID), App (U, App (V, App (W, App (P, Nil)))))
let rec proveQuotExp (U, V, W, P)  = Root (Const (! proveQuotID), App (U, App (V, App (W, App (P, Nil)))))
let rec proofQuotExp (U, V, W, P)  = Root (Const (! proofQuotID), App (U, App (V, App (W, App (P, Nil)))))
let rec numberConDec (d)  = ConDec (W.fmt StringCvt.DEC (d), None, 0, Normal, word (), Type)
let rec numberExp (d)  = Root (FgnConst (! myID, numberConDec (d)), Nil)
(* scanNumber (str) = numOpt

       Invariant:
         numOpt = SOME(n) if str is the decimal representation of the number n
                = NONE otherwise
    *)

let rec scanNumber (str)  = ( let rec check = function (chars) -> (List.all Char.isDigit chars) | [] -> false in  if check (String.explode str) then match (StringCvt.scanString (W.scan StringCvt.DEC) str) with Some (d) -> (if numCheck (d) then Some (d) else None) | None -> None else None )
(* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)

let rec parseNumber string  = match (scanNumber string) with Some (d) -> Some (numberConDec d) | None -> None
let rec plusPfConDec (d1, d2)  = ( let d3 = W.+ (d1, d2) in  ConDec (W.fmt StringCvt.DEC d1 ^ "+" ^ W.fmt StringCvt.DEC d2, None, 0, Normal, plusExp (numberExp d1, numberExp d2, numberExp d3), Type) )
let rec plusPfExp ds  = Root (FgnConst (! myID, plusPfConDec ds), Nil)
let rec timesPfConDec (d1, d2)  = ( let d3 = W.* (d1, d2) in  ConDec (W.fmt StringCvt.DEC d1 ^ "*" ^ W.fmt StringCvt.DEC d2, None, 0, Normal, timesExp (numberExp d1, numberExp d2, numberExp d3), Type) )
let rec timesPfExp ds  = Root (FgnConst (! myID, timesPfConDec ds), Nil)
let rec quotPfConDec (d1, d2)  = ( let d3 = W.div (d1, d2) in  ConDec (W.fmt StringCvt.DEC d1 ^ "/" ^ W.fmt StringCvt.DEC d2, None, 0, Normal, quotExp (numberExp d1, numberExp d2, numberExp d3), Type) )
let rec quotPfExp ds  = Root (FgnConst (! myID, quotPfConDec ds), Nil)
let rec scanBinopPf oper string  = ( let args = String.tokens (fun c -> c = oper) string in  match args with [arg1; arg2] -> (match (StringCvt.scanString (W.scan StringCvt.DEC) arg1, StringCvt.scanString (W.scan StringCvt.DEC) arg2) with (Some (d1), Some (d2)) -> Some (d1, d2) | _ -> None) | _ -> None )
(* parseBinopPf operator string = SOME(conDec) or NONE

       Invariant:
       If string parses to the proof object of n1<operator>n2
       then conDec is the (foreign) constant declaration of n1<operator>n2
    *)

let rec parseBinopPf oper string  = match (oper, scanBinopPf oper string) with ('+', Some (ds)) -> Some (plusPfConDec ds) | ('*', Some (ds)) -> Some (timesPfConDec ds) | ('/', Some (ds)) -> Some (quotPfConDec ds) | _ -> None
let parsePlusPf = parseBinopPf '+'
let parseTimesPf = parseBinopPf '*'
let parseQuotPf = parseBinopPf '/'
let rec parseAll string  = (match (parseNumber (string)) with Some (conDec) -> Some (conDec) | None -> (match (parsePlusPf (string)) with Some (conDec) -> Some (conDec) | None -> (match (parseTimesPf (string)) with Some (conDec) -> Some (conDec) | None -> parseQuotPf (string))))
type fixTerm = Num of W.word | PlusPf of (W.word * W.word) | TimesPf of (W.word * W.word) | QuotPf of (W.word * W.word) | Expr of (exp * sub)
(*        | <Expr>            *)

(* fromExpW (U, s) = t

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then t is the internal representation of U[s] as term
    *)

let rec fromExpW = function (Us) -> if (cs = ! myID) then ( let string = conDecName conDec in  (match (scanNumber string) with Some (d) -> Num d | None -> (match (scanBinopPf '/' string) with Some (ds) -> QuotPf ds | None -> (match (scanBinopPf '+' string) with Some (ds) -> PlusPf ds | None -> (match (scanBinopPf '*' string) with Some (ds) -> TimesPf ds | None -> Expr Us)))) ) else Expr Us | (Us) -> fromExpW (Whnf.expandDef (Us)) | Us -> Expr Us
and fromExp Us  = fromExpW (Whnf.whnf Us)
(* toExp t = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of t
    *)

let rec toExp = function (Num d) -> numberExp d | (PlusPf ds) -> plusPfExp ds | (TimesPf ds) -> timesPfExp ds | (QuotPf ds) -> quotPfExp ds | (Expr Us) -> EClo Us
let rec solveNumber (G, S, k)  = Some (numberExp (W.fromInt k))
(* fst (S, s) = U1, the first argument in S[s] *)

let rec fst = function (App (U1, _), s) -> (U1, s) | (SClo (S, s'), s) -> fst (S, comp (s', s))
(* snd (S, s) = U2, the second argument in S[s] *)

let rec snd = function (App (_, S), s) -> fst (S, s) | (SClo (S, s'), s) -> snd (S, comp (s', s))
(* trd (S, s) = U1, the third argument in S[s] *)

let rec trd = function (App (_, S), s) -> snd (S, s) | (SClo (S, s'), s) -> trd (S, comp (s', s))
(* fth (S, s) = U1, the fourth argument in S[s] *)

let rec fth = function (App (_, S), s) -> trd (S, s) | (SClo (S, s'), s) -> fth (S, comp (s', s))
let rec toInternalPlus (G, U1, U2, U3) ()  = [(G, plusExp (U1, U2, U3))]
and awakePlus (G, proof, U1, U2, U3) ()  = match (solvePlus (G, App (U1, App (U2, App (U3, Nil))), 0)) with Some (proof') -> Unify.unifiable (G, (proof, id), (proof', id)) | None -> false
and makeCnstrPlus (G, proof, U1, U2, U3)  = FgnCnstr (! myID, MyFgnCnstrRepPlus (G, proof, U1, U2, U3))
and solvePlus = function (G, S, 0) -> ( let Us1 = fst (S, id) in let Us2 = snd (S, id) in let Us3 = trd (S, id) in  (match (fromExp (Us1), fromExp (Us2), fromExp (Us3)) with (Num d1, Num d2, Num d3) -> if (d3 = W.+ (d1, d2) && plusCheck (d1, d2)) then Some (plusPfExp (d1, d2)) else None | (Expr Us1, Num d2, Num d3) -> if (W.>= (d3, d2) && Unify.unifiable (G, Us1, (numberExp (W.- (d3, d2)), id))) then Some (plusPfExp (W.- (d3, d2), d2)) else None | (Num d1, Expr Us2, Num d3) -> if (W.>= (d3, d1) && Unify.unifiable (G, Us2, (numberExp (W.- (d3, d1)), id))) then Some (plusPfExp (d1, W.- (d3, d1))) else None | (Num d1, Num d2, Expr Us3) -> if (plusCheck (d1, d2) && Unify.unifiable (G, Us3, (numberExp (W.+ (d1, d2)), id))) then Some (plusPfExp (d1, d2)) else None | _ -> ( let proof = newEVar (G, plusExp (EClo Us1, EClo Us2, EClo Us3)) in let cnstr = makeCnstrPlus (G, proof, EClo Us1, EClo Us2, EClo Us3) in let _ = List.app (fun Us -> Unify.delay (Us, ref cnstr)) [Us1; Us2; Us3] in  Some (proof) )) ) | (G, S, n) -> None
and toInternalTimes (G, U1, U2, U3) ()  = [(G, timesExp (U1, U2, U3))]
and awakeTimes (G, proof, U1, U2, U3) ()  = match (solveTimes (G, App (U1, App (U2, App (U3, Nil))), 0)) with Some (proof') -> Unify.unifiable (G, (proof, id), (proof', id)) | None -> false
and makeCnstrTimes (G, proof, U1, U2, U3)  = FgnCnstr (! myID, MyFgnCnstrRepTimes (G, proof, U1, U2, U3))
and solveTimes = function (G, S, 0) -> ( let Us1 = fst (S, id) in let Us2 = snd (S, id) in let Us3 = trd (S, id) in  (match (fromExp Us1, fromExp Us2, fromExp Us3) with (Num d1, Num d2, Num d3) -> if (d3 = W.* (d1, d2) && timesCheck (d1, d2)) then Some (timesPfExp (d1, d2)) else None | (Expr Us1, Num d2, Num d3) -> if (d3 = zero && Unify.unifiable (G, Us1, (numberExp (zero), id))) then Some (timesPfExp (zero, d2)) else if (W.> (d2, zero) && W.> (d3, zero) && W.mod_ (d3, d2) = zero && Unify.unifiable (G, Us1, (numberExp (W.div (d3, d2)), id))) then Some (timesPfExp (W.div (d3, d2), d2)) else None | (Num d1, Expr Us2, Num d3) -> if (d3 = zero && Unify.unifiable (G, Us2, (numberExp (zero), id))) then Some (timesPfExp (d1, zero)) else if (W.> (d1, zero) && W.> (d3, zero) && W.mod_ (d3, d1) = zero && Unify.unifiable (G, Us2, (numberExp (W.div (d3, d1)), id))) then Some (timesPfExp (d1, W.div (d3, d1))) else None | (Num d1, Num d2, Expr Us3) -> if (timesCheck (d1, d2) && Unify.unifiable (G, Us3, (numberExp (W.* (d1, d2)), id))) then Some (timesPfExp (d1, d2)) else None | _ -> ( let proof = newEVar (G, timesExp (EClo Us1, EClo Us2, EClo Us3)) in let cnstr = makeCnstrTimes (G, proof, EClo Us1, EClo Us2, EClo Us3) in let _ = List.app (fun Us -> Unify.delay (Us, ref cnstr)) [Us1; Us2; Us3] in  Some (proof) )) ) | (G, S, n) -> None
and toInternalQuot (G, U1, U2, U3) ()  = [(G, quotExp (U1, U2, U3))]
and awakeQuot (G, proof, U1, U2, U3) ()  = match (solveQuot (G, App (U1, App (U2, App (U3, Nil))), 0)) with Some (proof') -> Unify.unifiable (G, (proof, id), (proof', id)) | None -> false
and makeCnstrQuot (G, proof, U1, U2, U3)  = FgnCnstr (! myID, MyFgnCnstrRepQuot (G, proof, U1, U2, U3))
and solveQuot = function (G, S, 0) -> ( let Us1 = fst (S, id) in let Us2 = snd (S, id) in let Us3 = trd (S, id) in  (match (fromExp Us1, fromExp Us2, fromExp Us3) with (Num d1, Num d2, Num d3) -> if (quotCheck (d1, d2) && d3 = W.div (d1, d2)) then Some (quotPfExp (d1, d2)) else None | (Num d1, Num d2, Expr Us3) -> if (quotCheck (d1, d2) && Unify.unifiable (G, Us3, (numberExp (W.div (d1, d2)), id))) then Some (quotPfExp (d1, d2)) else None | _ -> ( let proof = newEVar (G, quotExp (EClo Us1, EClo Us2, EClo Us3)) in let cnstr = makeCnstrQuot (G, proof, EClo Us1, EClo Us2, EClo Us3) in let _ = List.app (fun Us -> Unify.delay (Us, ref cnstr)) [Us1; Us2; Us3] in  Some (proof) )) ) | (G, S, n) -> None
(* solveProvePlus (G, S, n) tries to find the n-th solution to
         G |- prove+ @ S : type
    *)

let rec solveProvePlus (G, S, k)  = ( let Us1 = fst (S, id) in let Us2 = snd (S, id) in let Us3 = trd (S, id) in let Us4 = fth (S, id) in  match (solvePlus (G, App (EClo Us1, App (EClo Us2, App (EClo Us3, Nil))), k)) with Some (U) -> if Unify.unifiable (G, Us4, (U, id)) then Some (proofPlusExp (EClo Us1, EClo Us2, EClo Us3, EClo Us4)) else None | None -> None )
(* solveProveTimes (G, S, n) tries to find the n-th solution to
         G |- prove* @ S : type
    *)

let rec solveProveTimes (G, S, k)  = ( let Us1 = fst (S, id) in let Us2 = snd (S, id) in let Us3 = trd (S, id) in let Us4 = fth (S, id) in  match (solveTimes (G, App (EClo Us1, App (EClo Us2, App (EClo Us3, Nil))), k)) with Some (U) -> if Unify.unifiable (G, Us4, (U, id)) then Some (proofTimesExp (EClo Us1, EClo Us2, EClo Us3, EClo Us4)) else None | None -> None )
(* solveProveQuot (G, S, n) tries to find the n-th solution to
         G |- prove/ @ S : type
    *)

let rec solveProveQuot (G, S, k)  = ( let Us1 = fst (S, id) in let Us2 = snd (S, id) in let Us3 = trd (S, id) in let Us4 = fth (S, id) in  match (solveQuot (G, App (EClo Us1, App (EClo Us2, App (EClo Us3, Nil))), k)) with Some (U) -> if Unify.unifiable (G, Us4, (U, id)) then Some (proofQuotExp (EClo Us1, EClo Us2, EClo Us3, EClo Us4)) else None | None -> None )
let rec arrow (U, V)  = Pi ((Dec (None, U), No), V)
let rec pi (name, U, V)  = Pi ((Dec (Some (name), U), Maybe), V)
let rec bvar n  = Root (BVar n, Nil)
let rec installFgnCnstrOps ()  = ( let csid = ! myID in let _ = FgnCnstrStd.ToInternal.install (csid, (fun (MyFgnCnstrRepPlus (G, _, U1, U2, U3)) -> toInternalPlus (G, U1, U2, U3) | (MyFgnCnstrRepTimes (G, _, U1, U2, U3)) -> toInternalTimes (G, U1, U2, U3) | (MyFgnCnstrRepQuot (G, _, U1, U2, U3)) -> toInternalQuot (G, U1, U2, U3) | fc -> raise ((UnexpectedFgnCnstr fc)))) in let _ = FgnCnstrStd.Awake.install (csid, (fun (MyFgnCnstrRepPlus (G, proof, U1, U2, U3)) -> awakePlus (G, proof, U1, U2, U3) | (MyFgnCnstrRepTimes (G, proof, U1, U2, U3)) -> awakeTimes (G, proof, U1, U2, U3) | (MyFgnCnstrRepQuot (G, proof, U1, U2, U3)) -> awakeQuot (G, proof, U1, U2, U3) | fc -> raise ((UnexpectedFgnCnstr fc)))) in let _ = FgnCnstrStd.Simplify.install (csid, (fun (MyFgnCnstrRepPlus _) -> (fun () -> false) | (MyFgnCnstrRepTimes _) -> (fun () -> false) | (MyFgnCnstrRepQuot _) -> (fun () -> false) | fc -> raise ((UnexpectedFgnCnstr fc)))) in  () )
(* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)

let rec init (cs, installF)  = (myID := cs; wordID := installF (ConDec ("word" ^ Int.toString (wordSize'), None, 0, Constraint (! myID, solveNumber), Uni (Type), Kind), (None : FX.fixity option), [MS.Mnil]); plusID := installF (ConDec ("+", None, 0, Constraint (! myID, solvePlus), arrow (word (), arrow (word (), arrow (word (), Uni (Type)))), Kind), None, [MS.Mapp (MS.Marg (MS.Plus, Some "X"), MS.Mapp (MS.Marg (MS.Plus, Some "Y"), MS.Mapp (MS.Marg (MS.Minus, Some "Z"), MS.Mnil))); MS.Mapp (MS.Marg (MS.Plus, Some "X"), MS.Mapp (MS.Marg (MS.Minus, Some "Y"), MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil))); MS.Mapp (MS.Marg (MS.Minus, Some "X"), MS.Mapp (MS.Marg (MS.Plus, Some "Y"), MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil)))]); timesID := installF (ConDec ("*", None, 0, Constraint (! myID, solveTimes), arrow (word (), arrow (word (), arrow (word (), Uni (Type)))), Kind), None, [MS.Mapp (MS.Marg (MS.Plus, Some "X"), MS.Mapp (MS.Marg (MS.Plus, Some "Y"), MS.Mapp (MS.Marg (MS.Minus, Some "Z"), MS.Mnil))); MS.Mapp (MS.Marg (MS.Plus, Some "X"), MS.Mapp (MS.Marg (MS.Minus, Some "Y"), MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil))); MS.Mapp (MS.Marg (MS.Minus, Some "X"), MS.Mapp (MS.Marg (MS.Plus, Some "Y"), MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil)))]); quotID := installF (ConDec ("/", None, 0, Constraint (! myID, solveQuot), arrow (word (), arrow (word (), arrow (word (), Uni (Type)))), Kind), None, [MS.Mapp (MS.Marg (MS.Plus, Some "X"), MS.Mapp (MS.Marg (MS.Plus, Some "Y"), MS.Mapp (MS.Marg (MS.Minus, Some "Z"), MS.Mnil))); MS.Mapp (MS.Marg (MS.Plus, Some "X"), MS.Mapp (MS.Marg (MS.Minus, Some "Y"), MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil)))]); provePlusID := installF (ConDec ("prove+", None, 0, Constraint (! myID, solveProvePlus), pi ("X", word (), pi ("Y", word (), pi ("Z", word (), pi ("P", plusExp (bvar 3, bvar 2, bvar 1), Uni (Type))))), Kind), None, [MS.Mapp (MS.Marg (MS.Star, Some "X"), MS.Mapp (MS.Marg (MS.Star, Some "Y"), MS.Mapp (MS.Marg (MS.Star, Some "Z"), MS.Mapp (MS.Marg (MS.Star, Some "P"), MS.Mnil))))]); proofPlusID := installF (ConDec ("proof+", None, 0, Normal, pi ("X", word (), pi ("Y", word (), pi ("Z", word (), pi ("P", plusExp (bvar 3, bvar 2, bvar 1), provePlusExp (bvar 4, bvar 3, bvar 2, bvar 1))))), Type), None, []); proveTimesID := installF (ConDec ("prove*", None, 0, Constraint (! myID, solveProveTimes), pi ("X", word (), pi ("Y", word (), pi ("Z", word (), pi ("P", timesExp (bvar 3, bvar 2, bvar 1), Uni (Type))))), Kind), None, [MS.Mapp (MS.Marg (MS.Star, Some "X"), MS.Mapp (MS.Marg (MS.Star, Some "Y"), MS.Mapp (MS.Marg (MS.Star, Some "Z"), MS.Mapp (MS.Marg (MS.Star, Some "P"), MS.Mnil))))]); proofTimesID := installF (ConDec ("proof*", None, 0, Normal, pi ("X", word (), pi ("Y", word (), pi ("Z", word (), pi ("P", timesExp (bvar 3, bvar 2, bvar 1), proveTimesExp (bvar 4, bvar 3, bvar 2, bvar 1))))), Type), None, []); proveQuotID := installF (ConDec ("prove/", None, 0, Constraint (! myID, solveProveQuot), pi ("X", word (), pi ("Y", word (), pi ("Z", word (), pi ("P", quotExp (bvar 3, bvar 2, bvar 1), Uni (Type))))), Kind), None, [MS.Mapp (MS.Marg (MS.Star, Some "X"), MS.Mapp (MS.Marg (MS.Star, Some "Y"), MS.Mapp (MS.Marg (MS.Star, Some "Z"), MS.Mapp (MS.Marg (MS.Star, Some "P"), MS.Mnil))))]); proofQuotID := installF (ConDec ("proof/", None, 0, Normal, pi ("X", word (), pi ("Y", word (), pi ("Z", word (), pi ("P", quotExp (bvar 3, bvar 2, bvar 1), proveQuotExp (bvar 4, bvar 3, bvar 2, bvar 1))))), Type), None, []); installFgnCnstrOps (); ())
let solver = {name = "word" ^ Int.toString (wordSize'); keywords = "numbers,equality"; needs = ["Unify"]; fgnConst = Some ({parse = parseAll}); init = init; reset = (fun () -> ()); mark = (fun () -> ()); unwind = (fun () -> ())}
 end

(* functor CSIntWord *)

