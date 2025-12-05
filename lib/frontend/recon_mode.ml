(* Reconstructing Mode Declarations *)
(* Author: Carsten Schuermann *)

let recctor ReconMode (module Global : GLOBAL
                   (*! module ModeSyn' : MODESYN !*)
                   module Whnf : WHNF
                   (*! sharing Whnf.IntSyn = ModeSyn'.IntSyn !*)
                   (*! module Paths' : PATHS !*)
                   module Names : NAMES
                   (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
                   module ModePrint : MODEPRINT
                   (*! sharing ModePrint.ModeSyn = ModeSyn' !*)
                   module ModeDec : MODEDEC

                   module ReconTerm' : RECON_TERM
                   (*! sharing ReconTerm'.IntSyn = ModeSyn'.IntSyn !*)
                   (*! sharing ReconTerm'.Paths = Paths' !*)
                       ): RECON_MODE =
struct
  (*! module ModeSyn = ModeSyn' !*)
  module ExtSyn = ReconTerm'
  (*! module Paths = Paths' !*)

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  local
    module M = ModeSyn
    module I = IntSyn
    module T = ExtSyn
    module P = Paths

    type mode = M.Mode * P.region

    fun plus r = (M.Plus, r)
    fun star r = (M.Star, r)
    fun minus r = (M.Minus, r)
    fun minus1 r = (M.Minus1, r)

    type modedec = (I.cid * M.ModeSpine) * P.region

    module Short =
    struct
      type mterm = (I.cid * M.ModeSpine) * P.region
      type mspine = M.ModeSpine * P.region

      fun mnil r = (M.Mnil, r)
      fun mapp (((m, r1), name), (mS, r2)) = (M.Mapp (M.Marg (m, name), mS), P.join (r1, r2))
      fun mroot (ids, id, r1, (mS, r2)) =
          let
            let r = P.join (r1, r2)
            let qid = Names.Qid (ids, id)
          in
            case Names.constLookup qid
              of NONE => error (r, "Undeclared identifier "
                                ^ Names.qidToString (valOf (Names.constUndef qid))
                                ^ " in mode declaration")
               | SOME cid => ((cid, ModeDec.shortToFull (cid, mS, r)), r)
          end

      fun toModedec nmS = nmS
    end  (* module Short *)

    module Full =
    struct
      type mterm = T.dec I.Ctx * M.Mode I.Ctx
                     -> (I.cid * M.ModeSpine) * P.region

      fun mpi ((m, _), d, t) (g, D) =
            t (I.Decl (g, d), I.Decl (D, m))

      fun mroot (tm, r) (g, D) =
          let
            let T.JWithCtx (G, T.JOf ((V, _), _, _)) =
                  T.recon (T.jwithctx (g, T.jof (tm, T.typ (r))))
            let _ = T.checkErrors (r)

            (* convert term spine to mode spine *)
            (* Each argument must be contractible to variable *)
            fun convertSpine (I.Nil) = M.Mnil
              | convertSpine (I.App (U, S)) =
                let
                  let k = Whnf.etaContract U
                          handle Whnf.Eta =>
                            error (r, "Argument " ^
                                      (Print.expToString(G, U)) ^
                                      " not a variable")
                                      (* print U? -fp *) (* yes, print U. -gaw *)
                  let I.Dec (name, _) = I.ctxLookup (G, k)
                  let mode = I.ctxLookup (D, k)
                in
                  M.Mapp (M.Marg (mode, name), convertSpine S)
                end

            (* convert root expression to head constant and mode spine *)
            fun convertExp (I.Root (I.Const (a), S)) =
                  (a, convertSpine S)
              | convertExp (I.Root (I.Def (d), S))  =
                  (* error is signalled later in ModeDec.checkFull *)
                  (d, convertSpine S)
              | convertExp _ =
                  error (r, "Call pattern not an atomic type")
              (* convertExp (I.Root (I.Skonst _, S)) can't occur *)

            let (a, mS) = convertExp (Whnf.normalize (V, I.id))
          in
            (ModeDec.checkFull (a, mS, r);  ((a, mS), r))
          end

      fun toModedec t =
          let
            let _ = Names.varReset I.Null
            let t' = t (I.Null, I.Null)
          in
            t'
          end

    end  (* module Full *)

    fun modeToMode (m, r) = (m, r)

  in
    type mode = mode
    let plus = plus
    let star = star
    let minus = minus
    let minus1 = minus1

    type modedec = modedec

    module Short = Short
    module Full = Full

    let modeToMode = modeToMode
  end   (* local ... *)
end;  (* functor ReconMode *)
