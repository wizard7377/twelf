(* Reconstructing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) ReconMode (structure Global : GLOBAL
                   (*! structure ModeSyn' : MODESYN !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = ModeSyn'.IntSyn !*)
                   (*! structure Paths' : PATHS !*)
                   structure Names : NAMES
                   (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
                   structure ModePrint : MODEPRINT
                   (*! sharing ModePrint.ModeSyn = ModeSyn' !*)
                   structure ModeDec : MODEDEC

                   structure ReconTerm' : RECON_TERM
                   (*! sharing ReconTerm'.IntSyn = ModeSyn'.IntSyn !*)
                   (*! sharing ReconTerm'.Paths = Paths' !*)
                       )
  : RECON_MODE =
struct
  (*! structure ModeSyn = ModeSyn' !*)
  structure ExtSyn = ReconTerm'
  (*! structure Paths = Paths' !*)

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  local
    structure M = ModeSyn
    structure I = IntSyn
    structure T = ExtSyn
    structure P = Paths

    type mode = M.mode * P.region

    fun plus r = (M.Plus, r)
    fun star r = (M.Star, r)
    fun minus r = (M.Minus, r)
    fun minus1 r = (M.Minus1, r)

    type modedec = (I.cid * M.mode_spine) * P.region

    structure Short =
    struct
      type mterm = (I.cid * M.mode_spine) * P.region
      type mspine = M.mode_spine * P.region

      fun mnil r = (M.Mnil, r)
      fun mapp (((m, r1), name), (mS, r2)) = (M.Mapp (M.Marg (m, name), mS), P.join (r1, r2))
      fun mroot (ids, id, r1, (mS, r2)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val r = P.join (r1, r2) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val qid = Names.Qid (ids, id) (* GEN END TAG OUTSIDE LET *)
          in
            case Names.constLookup qid
              of NONE => error (r, "Undeclared identifier "
                                ^ Names.qidToString (valOf (Names.constUndef qid))
                                ^ " in mode declaration")
               | SOME cid => ((cid, ModeDec.shortToFull (cid, mS, r)), r)
          end

      fun toModedec nmS = nmS
    end  (* structure Short *)

    structure Full =
    struct
      type mterm = T.dec I.ctx * M.mode I.ctx
                     -> (I.cid * M.mode_spine) * P.region

      fun mpi ((m, _), d, t) (g, D) =
            t (I.Decl (g, d), I.Decl (D, m))

      fun mroot (tm, r) (g, D) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val T.JWithCtx (G, T.JOf ((V, _), _, _)) =
                  T.recon (T.jwithctx (g, T.jof (tm, T.typ (r)))) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = T.checkErrors (r) (* GEN END TAG OUTSIDE LET *)
      
            (* convert term spine to mode spine *)
            (* Each argument must be contractible to variable *)
            fun (* GEN BEGIN FUN FIRST *) convertSpine (I.Nil) = M.Mnil (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) convertSpine (I.App (U, S)) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val k = Whnf.etaContract U
                          handle Whnf.Eta =>
                            error (r, "Argument " ^
                                      (Print.expToString(G, U)) ^
                                      " not a variable") (* GEN END TAG OUTSIDE LET *)
                                      (* print U? -fp *) (* yes, print U. -gaw *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val I.Dec (name, _) = I.ctxLookup (G, k) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val mode = I.ctxLookup (D, k) (* GEN END TAG OUTSIDE LET *)
                in
                  M.Mapp (M.Marg (mode, name), convertSpine S)
                end (* GEN END FUN BRANCH *)
      
            (* convert root expression to head constant and mode spine *)
            fun (* GEN BEGIN FUN FIRST *) convertExp (I.Root (I.Const (a), S)) =
                  (a, convertSpine S) (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) convertExp (I.Root (I.Def (d), S))  =
                  (* error is signalled later in ModeDec.checkFull *)
                  (d, convertSpine S) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) convertExp _ =
                  error (r, "Call pattern not an atomic type") (* GEN END FUN BRANCH *)
              (* convertExp (I.Root (I.Skonst _, S)) can't occur *)
      
            (* GEN BEGIN TAG OUTSIDE LET *) val (a, mS) = convertExp (Whnf.normalize (V, I.id)) (* GEN END TAG OUTSIDE LET *)
          in
            (ModeDec.checkFull (a, mS, r);  ((a, mS), r))
          end

      fun toModedec t =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset I.Null (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val t' = t (I.Null, I.Null) (* GEN END TAG OUTSIDE LET *)
          in
            t'
          end

    end  (* structure Full *)

    fun modeToMode (m, r) = (m, r)

  in
    type mode = mode
    (* GEN BEGIN TAG OUTSIDE LET *) val plus = plus (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val star = star (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val minus = minus (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val minus1 = minus1 (* GEN END TAG OUTSIDE LET *)

    type modedec = modedec

    structure Short = Short
    structure Full = Full

    (* GEN BEGIN TAG OUTSIDE LET *) val modeToMode = modeToMode (* GEN END TAG OUTSIDE LET *)
  end   (* local ... *)
end (* GEN END FUNCTOR DECL *);  (* functor ReconMode *)
