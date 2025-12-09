(* Solver for machine integers *)
(* Author: Roberto Virga *)

module CSIntWord ((*! (IntSyn : INTSYN) !*)
                   (Whnf : WHNF)
                   (*! sharing Whnf.IntSyn = IntSyn !*)
                   (Unify : UNIFY)
                   (*! sharing Unify.IntSyn = IntSyn !*)
                   (*! (CSManager : CS_MANAGER) !*)
                   (*! sharing CSManager.IntSyn = IntSyn !*)
                   let wordSize : int)
 : CS =
struct
  (*! module CSManager = CSManager !*)

  local
    open IntSyn

    module W = LargeWord;

    module FX = CSManager.Fixity
    module MS = ModeSyn (* CSManager.ModeSyn *)

    exception MyFgnCnstrRepPlus of dctx * Exp * Exp * Exp * Exp
                                        (* FgnCnstr Representation: (G, proof, U1, U2, U3) *)
    exception MyFgnCnstrRepTimes of dctx * Exp * Exp * Exp * Exp
    exception MyFgnCnstrRepQuot of dctx * Exp * Exp * Exp * Exp

    let wordSize' = Int.min (wordSize, W.wordSize);

    let zero = W.fromInt 0
    let max = W.>> (W.notb zero, Word.fromInt (W.wordSize - wordSize'))

    (* numCheck (d) = true iff d <= max *)
    let rec numCheck (d) = W.<= (d, max)

    (* plusCheck (d1, d2) = true iff d1 + d2 <= max *)
    let rec plusCheck (d1, d2) =
          let
            let d3 = W.+ (d1, d2)
          in
            W.>= (d3, d1)
            andalso W.>= (d3, d2)
            andalso W.<= (d3, max)
          end

    (* timesCheck (d1, d2) = true iff d1 * d2 <= max *)
    let rec timesCheck (d1, d2) =
          if(d1 = zero orelse d2 = zero) then true
          else let let d3 = W.div (W.div (max, d1), d2)
               in W.> (d3, zero) end

    (* quotCheck (d1, d2) = true iff  d2 != zero *)
    let rec quotCheck (d1, d2) = W.> (d2, zero)

    (* constraint solver ID of this module *)
    let myID = ref ~1 : csid ref

    (* constant ID of the type family constant "wordXX" *)
    let wordID = ref ~1 : cid ref

    let rec word () = Root (Const (!wordID), Nil)

    (* constant ID's of the operators defined by this module *)
    let plusID  = ref ~1 : cid ref   (* + : wordXX -> wordXX -> wordXX -> type *)
    let timesID = ref ~1 : cid ref   (* * : wordXX -> wordXX -> wordXX -> type *)
    let quotID  = ref ~1 : cid ref   (* / : wordXX -> wordXX -> wordXX -> type *)

    let rec plusExp (U, V, W) = Root (Const (!plusID),
                                  App (U, App (V, App (W , Nil))))

    let rec timesExp (U, V, W) = Root (Const (!timesID),
                                   App (U, App (V, App (W, Nil))))

    let rec quotExp (U, V, W) = Root (Const (!quotID),
                                  App (U, App (V, App (W , Nil))))

    (* constant ID's of the proof object generators and their proof objects *)
    (* (these are used as workaround for the lack of sigma types in Twelf)  *)
    let provePlusID  = ref ~1 : cid ref (* prove+ : {U}{V}{W} + U V W -> type *)
    let proveTimesID = ref ~1 : cid ref (* prove* : {U}{V}{W} * U V W -> type *)
    let proveQuotID  = ref ~1 : cid ref (* prove/ : {U}{V}{W} / U V W -> type *)
    let proofPlusID  = ref ~1 : cid ref (* proof* : {U}{V}{W}{P} prove+ U V W P *)
    let proofTimesID = ref ~1 : cid ref (* proof* : {U}{V}{W}{P} prove* U V W P *)
    let proofQuotID  = ref ~1 : cid ref (* proof/ : {U}{V}{W}{P} prove/ U V W P *)

    let rec provePlusExp (U, V, W, P) = Root (Const (!provePlusID),
                                          App (U, App (V, App (W, App (P , Nil)))))
    let rec proofPlusExp (U, V, W, P) = Root (Const (!proofPlusID),
                                          App (U, App (V, App (W, App (P , Nil)))))

    let rec proofTimesExp (U, V, W, P) = Root (Const (!proofTimesID),
                                           App (U, App (V, App (W, App (P , Nil)))))
    let rec proveTimesExp (U, V, W, P) = Root (Const (!proveTimesID),
                                           App (U, App (V, App (W, App (P , Nil)))))

    let rec proveQuotExp (U, V, W, P) = Root (Const (!proveQuotID),
                                          App (U, App (V, App (W, App (P , Nil)))))
    let rec proofQuotExp (U, V, W, P) = Root (Const (!proofQuotID),
                                          App (U, App (V, App (W, App (P , Nil)))))

    let rec numberConDec (d) = ConDec (W.fmt StringCvt.DEC (d), NONE, 0, Normal, word (), Type)

    let rec numberExp (d) = Root (FgnConst (!myID, numberConDec (d)), Nil)

    (* scanNumber (str) = numOpt

       Invariant:
         numOpt = SOME(n) if str is the decimal representation of the number n
                = NONE otherwise
    *)
    let rec scanNumber (str) =
          let
            let rec check = function (chars as (_ :: _)) -> 
                 (List.all Char.isDigit chars)
              | nil -> 
                  false
          in
            if check (String.explode str)
            then
              case (StringCvt.scanString (W.scan StringCvt.DEC) str)
                of SOME(d) => (if numCheck (d) then SOME(d) else NONE)
                 | NONE => NONE
            else NONE
          end

    (* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
    let rec parseNumber string =
          case (scanNumber string)
            of SOME(d) => SOME(numberConDec d)
             | NONE => NONE

    let rec plusPfConDec (d1, d2) =
          let
            let d3 = W.+ (d1, d2)
          in
            ConDec (W.fmt StringCvt.DEC d1
                    ^ "+"
                    ^ W.fmt StringCvt.DEC d2,
                    NONE, 0, Normal,
                    plusExp (numberExp d1, numberExp d2, numberExp d3),
                    Type)
          end

    let rec plusPfExp ds = Root (FgnConst (!myID, plusPfConDec ds), Nil)

    let rec timesPfConDec (d1, d2) =
          let
            let d3 = W.* (d1, d2)
          in
            ConDec (W.fmt StringCvt.DEC d1
                    ^ "*"
                    ^ W.fmt StringCvt.DEC d2,
                    NONE, 0, Normal,
                    timesExp (numberExp d1, numberExp d2, numberExp d3),
                    Type)
          end

    let rec timesPfExp ds = Root(FgnConst (!myID, timesPfConDec ds), Nil)

    let rec quotPfConDec (d1, d2) =
          let
            let d3 = W.div (d1, d2)
          in
            ConDec (W.fmt StringCvt.DEC d1
                    ^ "/"
                    ^ W.fmt StringCvt.DEC d2,
                    NONE, 0, Normal,
                    quotExp (numberExp d1, numberExp d2, numberExp d3),
                    Type)
          end

    let rec quotPfExp ds = Root (FgnConst (!myID, quotPfConDec ds), Nil)

    let rec scanBinopPf oper string =
          let
            let args = String.tokens (fun c -> c = oper) string
          in
            case args
              of [arg1, arg2] =>
                (case (StringCvt.scanString (W.scan StringCvt.DEC) arg1,
                       StringCvt.scanString (W.scan StringCvt.DEC) arg2)
                   of (SOME(d1), SOME(d2)) => SOME(d1, d2)
                    | _ => NONE)
               | _ => NONE
          end

    (* parseBinopPf operator string = SOME(conDec) or NONE

       Invariant:
       If string parses to the proof object of n1<operator>n2
       then conDec is the (foreign) constant declaration of n1<operator>n2
    *)
    let rec parseBinopPf oper string =
          case (oper, scanBinopPf oper string)
            of (#"+", SOME(ds)) => SOME(plusPfConDec ds)
             | (#"*", SOME(ds)) => SOME(timesPfConDec ds)
             | (#"/", SOME(ds)) => SOME(quotPfConDec ds)
             | _ => NONE

    let parsePlusPf = parseBinopPf #"+"
    let parseTimesPf = parseBinopPf #"*"
    let parseQuotPf = parseBinopPf #"/"

    let rec parseAll string =
          (case (parseNumber (string))
             of SOME(conDec) => SOME(conDec)
              | NONE =>
          (case (parsePlusPf (string))
             of SOME(conDec) => SOME(conDec)
              | NONE =>
          (case (parseTimesPf (string))
             of SOME(conDec) => SOME(conDec)
              | NONE => parseQuotPf (string))))

    type FixTerm =                                      (* Term                       *)
      Num of W.word                                         (* Term ::= n                 *)
    | PlusPf of (W.word * W.word)                           (*        | n1+n2             *)
    | TimesPf of (W.word * W.word)                          (*        | n1*n2             *)
    | QuotPf of (W.word * W.word)                           (*        | n1/n2             *)
    | Expr of (Exp * Sub)                                   (*        | <Expr>            *)

    (* fromExpW (U, s) = t

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then t is the internal representation of U[s] as term
    *)
    let rec fromExpW = function (Us as (Root (FgnConst (cs, conDec), _), _)) -> 
          if (cs = !myID)
          then
            let
              let string = conDecName conDec
            in
              (case (scanNumber string)
                 of SOME(d) => Num d
                  | NONE =>
              (case (scanBinopPf #"/" string)
                 of SOME(ds) => QuotPf ds
                  | NONE =>
              (case (scanBinopPf #"+" string)
                 of SOME(ds) => PlusPf ds
                  | NONE =>
              (case (scanBinopPf #"*" string)
                 of SOME(ds) => TimesPf ds
                  | NONE => Expr Us))))
            end
          else Expr Us
      | (Us as (Root (Def(d), _), _)) -> 
          fromExpW (Whnf.expandDef (Us))
      | Us -> Expr Us

    (* fromExp (U, s) = t

       Invariant:
       If   G' |- s : G    G |- U : V
       then t is the internal representation of U[s] as term
    *)
    and fromExp Us = fromExpW (Whnf.whnf Us)

    (* toExp t = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of t
    *)
    let rec toExp = function (Num d) -> numberExp d
      | (PlusPf ds) -> plusPfExp ds
      | (TimesPf ds) -> timesPfExp ds
      | (QuotPf ds) -> quotPfExp ds
      | (Expr Us) -> EClo Us

    let rec solveNumber (G, S, k) = SOME(numberExp (W.fromInt k))

    (* fst (S, s) = U1, the first argument in S[s] *)
    let rec fst = function (App (U1, _), s) -> (U1, s)
      | (SClo (S, s'), s) -> fst (S, comp (s', s))

    (* snd (S, s) = U2, the second argument in S[s] *)
    let rec snd = function (App (_, S), s) -> fst (S, s)
      | (SClo (S, s'), s) -> snd (S, comp (s', s))

    (* trd (S, s) = U1, the third argument in S[s] *)
    let rec trd = function (App (_, S), s) -> snd (S, s)
      | (SClo (S, s'), s) -> trd (S, comp (s', s))

    (* fth (S, s) = U1, the fourth argument in S[s] *)
    let rec fth = function (App (_, S), s) -> trd (S, s)
      | (SClo (S, s'), s) -> fth (S, comp (s', s))

    let rec toInternalPlus (G, U1, U2, U3) () =
          [(G, plusExp(U1, U2, U3))]

    and awakePlus (G, proof, U1, U2, U3) () =
          case (solvePlus (G, App(U1, App (U2, App (U3, Nil))), 0))
            of SOME(proof') => Unify.unifiable(G, (proof, id), (proof', id))
             | NONE => false

    (* constraint constructor *)
    and makeCnstrPlus (G, proof, U1, U2, U3) =
          FgnCnstr (!myID, MyFgnCnstrRepPlus (G, proof, U1, U2, U3))

    (* solvePlus (G, S, n) tries to find the n-th solution to
          G |- '+' @ S : type
    *)
    and solvePlus (G, S, 0) =
          let
            let Us1 = fst (S, id)
            let Us2 = snd (S, id)
            let Us3 = trd (S, id)
          in
            (case (fromExp (Us1), fromExp (Us2), fromExp (Us3))
               of (Num d1, Num d2, Num d3) =>
                     if(d3 = W.+(d1, d2) andalso plusCheck (d1, d2))
                     then SOME(plusPfExp(d1, d2))
                     else NONE
                | (Expr Us1, Num d2, Num d3) =>
                     if (W.>=(d3, d2)
                         andalso Unify.unifiable (G, Us1, (numberExp (W.-(d3, d2)), id)))
                     then SOME(plusPfExp(W.-(d3, d2), d2))
                     else NONE
                | (Num d1, Expr Us2, Num d3) =>
                     if (W.>=(d3, d1)
                         andalso Unify.unifiable (G, Us2, (numberExp (W.-(d3, d1)), id)))
                     then SOME(plusPfExp(d1, W.-(d3, d1)))
                     else NONE
                | (Num d1, Num d2, Expr Us3) =>
                     if (plusCheck (d1, d2)
                         andalso Unify.unifiable (G, Us3, (numberExp (W.+(d1, d2)), id)))
                     then SOME(plusPfExp(d1, d2))
                     else NONE
                | _ => let
                         let proof = newEVar (G, plusExp(EClo Us1, EClo Us2, EClo Us3))
                         let cnstr = makeCnstrPlus (G, proof, EClo Us1, EClo Us2, EClo Us3)
                         let _ = List.app (fun Us -> Unify.delay (Us, ref cnstr))
                                          [Us1, Us2, Us3]
                       in
                         SOME(proof)
                       end)
          end
      | solvePlus (G, S, n) = NONE

    and toInternalTimes (G, U1, U2, U3) () =
          [(G, timesExp(U1, U2, U3))]

    and awakeTimes (G, proof, U1, U2, U3) () =
          case (solveTimes (G, App(U1, App (U2, App (U3, Nil))), 0))
            of SOME(proof') => Unify.unifiable(G, (proof, id), (proof', id))
             | NONE => false

    and makeCnstrTimes (G, proof, U1, U2, U3) =
          FgnCnstr (!myID, MyFgnCnstrRepTimes (G, proof, U1, U2, U3))

    (* solveTimes (G, S, n) tries to find the n-th solution to
         G |- '*' @ S : type
    *)
    and solveTimes (G, S, 0) =
          let
            let Us1 = fst (S, id)
            let Us2 = snd (S, id)
            let Us3 = trd (S, id)
          in
            (case (fromExp Us1, fromExp Us2, fromExp Us3)
               of (Num d1, Num d2, Num d3) =>
                     if (d3 = W.*(d1, d2) andalso timesCheck (d1, d2))
                     then SOME(timesPfExp (d1, d2))
                     else NONE
                | (Expr Us1, Num d2, Num d3) =>
                     if (d3 = zero
                         andalso Unify.unifiable
                                   (G, Us1, (numberExp(zero), id)))
                     then SOME(timesPfExp (zero, d2))
                     else if (W.>(d2, zero) andalso W.>(d3, zero)
                              andalso W.mod(d3, d2) = zero
                              andalso
                                Unify.unifiable (G, Us1, (numberExp(W.div (d3, d2)), id)))
                     then SOME(timesPfExp (W.div (d3, d2), d2))
                     else NONE
                | (Num d1, Expr Us2, Num d3) =>
                     if (d3 = zero
                         andalso Unify.unifiable
                                   (G, Us2, (numberExp(zero), id)))
                       then SOME(timesPfExp (d1, zero))
                     else if (W.>(d1, zero) andalso W.>(d3, zero)
                              andalso W.mod(d3, d1) = zero
                              andalso
                                Unify.unifiable
                                  (G, Us2, (numberExp(W.div(d3, d1)), id)))
                     then SOME(timesPfExp (d1, W.div (d3, d1)))
                     else NONE
                | (Num d1, Num d2, Expr Us3) =>
                     if (timesCheck (d1, d2)
                         andalso Unify.unifiable (G, Us3, (numberExp(W.*(d1, d2)), id)))
                     then SOME(timesPfExp (d1, d2))
                     else NONE
                | _ => let
                         let proof = newEVar (G, timesExp(EClo Us1, EClo Us2, EClo Us3))
                         let cnstr = makeCnstrTimes (G, proof, EClo Us1, EClo Us2, EClo Us3)
                         let _ = List.app (fun Us -> Unify.delay (Us, ref cnstr))
                                          [Us1, Us2, Us3]
                       in
                         SOME(proof)
                       end)
          end
      | solveTimes (G, S, n) = NONE

    and toInternalQuot (G, U1, U2, U3) () =
          [(G, quotExp(U1, U2, U3))]

    and awakeQuot (G, proof, U1, U2, U3) () =
          case (solveQuot (G, App(U1, App (U2, App (U3, Nil))), 0))
            of SOME(proof') => Unify.unifiable(G, (proof, id), (proof', id))
             | NONE => false

    (* constraint constructor *)
    and makeCnstrQuot (G, proof, U1, U2, U3) =
          FgnCnstr (!myID, MyFgnCnstrRepQuot (G, proof, U1, U2, U3))

    (* solveQuot (G, S, n) tries to find the n-th solution to
         G |- '/' @ S : type
    *)
    and solveQuot (G, S, 0) =
          let
            let Us1 = fst (S, id)
            let Us2 = snd (S, id)
            let Us3 = trd (S, id)
          in
            (case (fromExp Us1, fromExp Us2, fromExp Us3)
               of (Num d1, Num d2, Num d3) =>
                     if (quotCheck (d1, d2) andalso d3 = W.div(d1, d2))
                     then SOME(quotPfExp (d1, d2))
                     else NONE
                | (Num d1, Num d2, Expr Us3) =>
                     if (quotCheck (d1, d2)
                         andalso Unify.unifiable (G, Us3, (numberExp (W.div(d1, d2)), id)))
                     then SOME(quotPfExp (d1, d2))
                     else NONE
                | _ => let
                         let proof = newEVar (G, quotExp (EClo Us1, EClo Us2, EClo Us3))
                         let cnstr = makeCnstrQuot (G, proof, EClo Us1, EClo Us2, EClo Us3)
                         let _ = List.app (fun Us -> Unify.delay (Us, ref cnstr))
                                          [Us1, Us2, Us3]
                       in
                         SOME(proof)
                       end)
          end
      | solveQuot (G, S, n) = NONE

    (* solveProvePlus (G, S, n) tries to find the n-th solution to
         G |- prove+ @ S : type
    *)
    let rec solveProvePlus (G, S, k) =
          let
            let Us1 = fst (S, id)
            let Us2 = snd (S, id)
            let Us3 = trd (S, id)
            let Us4 = fth (S, id)
          in
            case (solvePlus (G, App (EClo Us1, App (EClo Us2, App (EClo Us3, Nil))), k))
              of SOME(U) =>
                   if Unify.unifiable(G, Us4, (U, id))
                   then SOME(proofPlusExp (EClo Us1, EClo Us2, EClo Us3, EClo Us4))
                   else NONE
               | NONE => NONE
          end

    (* solveProveTimes (G, S, n) tries to find the n-th solution to
         G |- prove* @ S : type
    *)
    let rec solveProveTimes (G, S, k) =
          let
            let Us1 = fst (S, id)
            let Us2 = snd (S, id)
            let Us3 = trd (S, id)
            let Us4 = fth (S, id)
          in
            case (solveTimes (G, App (EClo Us1, App (EClo Us2, App (EClo Us3, Nil))), k))
              of SOME(U) =>
                   if Unify.unifiable(G, Us4, (U, id))
                   then SOME(proofTimesExp (EClo Us1, EClo Us2, EClo Us3, EClo Us4))
                   else NONE
               | NONE => NONE
          end

    (* solveProveQuot (G, S, n) tries to find the n-th solution to
         G |- prove/ @ S : type
    *)
    let rec solveProveQuot (G, S, k) =
          let
            let Us1 = fst (S, id)
            let Us2 = snd (S, id)
            let Us3 = trd (S, id)
            let Us4 = fth (S, id)
          in
            case (solveQuot (G, App (EClo Us1, App (EClo Us2, App (EClo Us3, Nil))), k))
              of SOME(U) =>
                   if Unify.unifiable(G, Us4, (U, id))
                   then SOME(proofQuotExp (EClo Us1, EClo Us2, EClo Us3, EClo Us4))
                   else NONE
               | NONE => NONE
          end

    let rec arrow (U, V) = Pi ((Dec (NONE, U), No), V)
    let rec pi (name, U, V) = Pi ((Dec (SOME(name), U), Maybe), V)
    let rec bvar n = Root (BVar n, Nil)

    let rec installFgnCnstrOps () = let
        let csid = !myID
        let _ = FgnCnstrStd.ToInternal.install (csid,
                                                (fn (MyFgnCnstrRepPlus (G, _, U1, U2, U3)) => toInternalPlus (G, U1, U2, U3)
                                                  | (MyFgnCnstrRepTimes (G, _, U1, U2, U3)) => toInternalTimes (G, U1, U2, U3)
                                                  | (MyFgnCnstrRepQuot (G, _, U1, U2, U3)) => toInternalQuot (G, U1, U2, U3)
                                                  | fc => raise (UnexpectedFgnCnstr fc)))
        let _ = FgnCnstrStd.Awake.install (csid,
                                           (fn (MyFgnCnstrRepPlus (G, proof, U1, U2, U3)) => awakePlus (G, proof, U1, U2, U3)
                                             | (MyFgnCnstrRepTimes (G, proof, U1, U2, U3)) => awakeTimes (G, proof, U1, U2, U3)
                                             | (MyFgnCnstrRepQuot (G, proof, U1, U2, U3)) => awakeQuot (G, proof, U1, U2, U3)
                                             | fc => raise (UnexpectedFgnCnstr fc)))
        let _ = FgnCnstrStd.Simplify.install (csid,
                                              (fn (MyFgnCnstrRepPlus _) => (fn () => false)
                                                | (MyFgnCnstrRepTimes _) => (fn () => false)
                                                | (MyFgnCnstrRepQuot _) => (fn () => false)
                                                | fc => raise (UnexpectedFgnCnstr fc)))
    in
        ()
    end

    (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its module type symbols.
    *)
    let rec init (cs, installF) =
          (
            myID := cs;

            wordID :=
              installF (ConDec ("word" ^ Int.toString(wordSize'), NONE, 0,
                                Constraint (!myID, solveNumber),
                                Uni (Type), Kind),
                        NONE : FX.fixity option, [MS.Mnil]);

            plusID :=
              installF (ConDec ("+", NONE, 0,
                                Constraint (!myID, solvePlus),
                                arrow (word (),
                                  arrow (word (),
                                    arrow (word (), Uni (Type)))), Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Minus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Minus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Minus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil)))]);

            timesID :=
              installF (ConDec ("*", NONE, 0,
                                Constraint (!myID, solveTimes),
                                arrow (word (),
                                  arrow (word (),
                                    arrow (word (), Uni (Type)))), Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Minus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Minus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Minus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil)))]);

            quotID :=
              installF (ConDec ("/", NONE, 0,
                                Constraint (!myID, solveQuot),
                                arrow (word (),
                                  arrow (word (),
                                    arrow (word (), Uni (Type)))), Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Minus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Minus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil)))]);

            provePlusID :=
              installF (ConDec ("prove+", NONE, 0,
                                Constraint (!myID, solveProvePlus),
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", plusExp (bvar 3, bvar 2, bvar 1),
                                          Uni (Type))))),
                                Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Star, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Star, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Star, SOME "Z"),
                                                 MS.Mapp(MS.Marg(MS.Star, SOME "P"),
                                                         MS.Mnil))))]);
            proofPlusID :=
              installF (ConDec ("proof+", NONE, 0, Normal,
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", plusExp (bvar 3, bvar 2, bvar 1),
                                          provePlusExp (bvar 4, bvar 3, bvar 2, bvar 1))))),
                                Type),
                        NONE, nil);

            proveTimesID :=
              installF (ConDec ("prove*", NONE, 0,
                                Constraint (!myID, solveProveTimes),
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", timesExp (bvar 3, bvar 2, bvar 1),
                                          Uni (Type))))),
                                Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Star, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Star, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Star, SOME "Z"),
                                                 MS.Mapp(MS.Marg(MS.Star, SOME "P"),
                                                         MS.Mnil))))]);

            proofTimesID :=
              installF (ConDec ("proof*", NONE, 0, Normal,
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", timesExp (bvar 3, bvar 2, bvar 1),
                                          proveTimesExp (bvar 4, bvar 3, bvar 2, bvar 1))))),
                                Type),
                        NONE, nil);

            proveQuotID :=
              installF (ConDec ("prove/", NONE, 0,
                                Constraint (!myID, solveProveQuot),
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", quotExp (bvar 3, bvar 2, bvar 1),
                                          Uni (Type))))),
                                Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Star, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Star, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Star, SOME "Z"),
                                                 MS.Mapp(MS.Marg(MS.Star, SOME "P"),
                                                         MS.Mnil))))]);

            proofQuotID :=
              installF (ConDec ("proof/", NONE, 0, Normal,
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", quotExp (bvar 3, bvar 2, bvar 1),
                                          proveQuotExp (bvar 4, bvar 3, bvar 2, bvar 1))))),
                                Type),
                        NONE, nil);

            installFgnCnstrOps ();
            ()
          )
  in
    let solver =
          {
            name = "word" ^ Int.toString(wordSize'),
            keywords = "numbers,equality",
            needs = ["Unify"],

            fgnConst = SOME({parse = parseAll}),

            init = init,

            reset  = (fn () => ()),
            mark   = (fn () => ()),
            unwind = (fn () => ())
          }
  end
end  (* functor CSIntWord *)
