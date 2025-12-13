(* Reconstruct signature entries *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga, Jeff Polakow *)

functor (* GEN BEGIN FUNCTOR DECL *) ReconConDec (structure Global : GLOBAL
                     (*! structure IntSyn' : INTSYN !*)
                     structure Names : NAMES
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     structure Abstract : ABSTRACT
                     (*! sharing Abstract.IntSyn = IntSyn' !*)
                     (*! structure Paths' : PATHS !*)
                     structure ReconTerm' : RECON_TERM
                     (*! sharing ReconTerm'.IntSyn = IntSyn' !*)
                     (*! sharing ReconTerm'.Paths = Paths' !*)
                     structure Constraints : CONSTRAINTS
                     (*! sharing Constraints.IntSyn = IntSyn' !*)
                     structure Strict : STRICT
                     (*! sharing Strict.IntSyn = IntSyn' !*)
                     (*! sharing Strict.Paths = Paths' !*)
                     structure TypeCheck : TYPECHECK
                     (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                     structure Timers : TIMERS
                     structure Print : PRINT
                     (*! sharing Print.IntSyn = IntSyn' !*)
                     structure Msg : MSG
                       )
  : RECON_CONDEC =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)
  structure ExtSyn = ReconTerm'

  exception Error of string

  (* error (r, msg) raises a syntax error within region r with text msg *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  type name = string

  (* Constant declarations *)
  datatype condec =
      condec of name * ExtSyn.term
    | condef of name option * ExtSyn.term * ExtSyn.term option
    | blockdef of string *  (string list * string) list
    | blockdec of name * ExtSyn.dec list * ExtSyn.dec list

  (* condecToConDec (condec, r) = (SOME(cd), SOME(ocd))
     if condec is a named constant declaration with occurrence tree ocd,
     NONE if name or occurrence tree is missing

     Free variables in condec are interpreted universally (as FVars)
     then abstracted as implicit parameters.

     Only works properly when the declaration contains no EVars.
  *)
  (* should printing of result be moved to frontend? *)
  (* Wed May 20 08:08:50 1998 -fp *)
  fun (* GEN BEGIN FUN FIRST *) condecToConDec (condec(name, tm), Paths.Loc (fileName, r), abbFlag) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = ExtSyn.resetErrors fileName (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ExtSyn.JClass ((V, oc), L) =
              (Timers.time Timers.recon ExtSyn.recon) (ExtSyn.jclass tm) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = ExtSyn.checkErrors (r) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (i, V') = (Timers.time Timers.abstract Abstract.abstractDecImp) V
                        handle Abstract.Error (msg)
                               => raise Abstract.Error (Paths.wrap (r, msg)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val cd = Names.nameConDec (IntSyn.ConDec (name, NONE, i, IntSyn.Normal, V', L)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ocd = Paths.dec (i, oc) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                else () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.doubleCheck
                  then (Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni L)
                else () (* GEN END TAG OUTSIDE LET *)
      in
        (SOME(cd), SOME(ocd))
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) condecToConDec (condef(optName, tm1, tm2Opt), Paths.Loc (fileName, r), abbFlag) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = ExtSyn.resetErrors fileName (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val f = (case tm2Opt
                   of NONE => ExtSyn.jterm tm1
                    | SOME tm2 => ExtSyn.jof (tm1, tm2)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val f' = (Timers.time Timers.recon ExtSyn.recon) f (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ((U, oc1), (V, oc2Opt), L) =
            (case f'
               of ExtSyn.JTerm ((U, oc1), V, L) =>
                    ((U, oc1), (V, NONE), L)
                | ExtSyn.JOf ((U, oc1), (V, oc2), L) =>
                    ((U, oc1), (V, SOME oc2), L)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = ExtSyn.checkErrors (r) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (i, (U'', V'')) =
                (Timers.time Timers.abstract Abstract.abstractDef) (U, V)
                handle Abstract.Error (msg)
                          => raise Abstract.Error (Paths.wrap (r, msg)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val name = case optName of NONE => "_" | SOME(name) => name (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ocd = Paths.def (i, oc1, oc2Opt) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val cd = if abbFlag then Names.nameConDec (IntSyn.AbbrevDef (name, NONE, i, U'', V'', L))
                 else (Strict.check ((U'', V''), SOME(ocd));
                       (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
                       (* (case optName of NONE => () | _ => Strict.checkType ((i, V''), SOME(ocd))); *)
                       (Names.nameConDec (IntSyn.ConDef (name, NONE, i, U'', V'', L,
                                                         IntSyn.ancestor U'')))) (* GEN END TAG OUTSIDE LET *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                else () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.doubleCheck
                  then ((Timers.time Timers.checking TypeCheck.check) (V'', IntSyn.Uni L);
                        (Timers.time Timers.checking TypeCheck.check) (U'', V''))
                else () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val optConDec = case optName of NONE => NONE | SOME _ => SOME (cd) (* GEN END TAG OUTSIDE LET *)
      in
        (optConDec, SOME(ocd))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) condecToConDec (blockdec (name, Lsome, Lblock), Paths.Loc (fileName, r), abbFlag) =
      let
        fun (* GEN BEGIN FUN FIRST *) makectx nil = IntSyn.Null (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) makectx (D :: L) = IntSyn.Decl (makectx L, D) (* GEN END FUN BRANCH *)
        fun (* GEN BEGIN FUN FIRST *) ctxToList (IntSyn.Null, acc) = acc (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) ctxToList (IntSyn.Decl (G, D), acc) = ctxToList (G, D :: acc) (* GEN END FUN BRANCH *)
        fun (* GEN BEGIN FUN FIRST *) ctxAppend (G, IntSyn.Null) = G (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) ctxAppend (G, IntSyn.Decl (G', D)) = IntSyn.Decl (ctxAppend (G, G'), D) (* GEN END FUN BRANCH *)
        fun ctxBlockToString (G0, (G1, G2)) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val G0' = Names.ctxName G0 (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val G1' = Names.ctxLUName G1 (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val G2' = Names.ctxLUName G2 (* GEN END TAG OUTSIDE LET *)
            in
              Print.ctxToString (IntSyn.Null, G0') ^ "\n"
              ^ (case G1' of IntSyn.Null => "" | _ => "some " ^ Print.ctxToString (G0', G1') ^ "\n")
              ^ "pi " ^ Print.ctxToString (ctxAppend (G0', G1'), G2')
            end
        fun (* GEN BEGIN FUN FIRST *) checkFreevars (IntSyn.Null, (G1, G2), r) = () (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) checkFreevars (G0, (G1, G2), r) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val G0' = Names.ctxName G0 (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val G1' = Names.ctxLUName G1 (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val G2' = Names.ctxLUName G2 (* GEN END TAG OUTSIDE LET *)
            in
              error (r, "Free variables in context block after term reconstruction:\n"
                     ^ ctxBlockToString (G0', (G1', G2')))
            end (* GEN END FUN BRANCH *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val (gsome, gblock) = (makectx Lsome, makectx Lblock) (* GEN END TAG OUTSIDE LET *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val r' = (case (ExtSyn.ctxRegion gsome, ExtSyn.ctxRegion gblock)
                    of (SOME r1, SOME r2) => Paths.join (r1, r2)
                     | (_, SOME r2) => r2) (* GEN END TAG OUTSIDE LET *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Names.varReset IntSyn.Null (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = ExtSyn.resetErrors fileName (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val j = ExtSyn.jwithctx (gsome,
                  ExtSyn.jwithctx (gblock, ExtSyn.jnothing)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ExtSyn.JWithCtx (Gsome, ExtSyn.JWithCtx (Gblock, _)) =
              (Timers.time Timers.recon ExtSyn.recon) j (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = ExtSyn.checkErrors (r) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (G0, [Gsome', Gblock']) =   (* closed nf *)
          Abstract.abstractCtxs [Gsome, Gblock]
          handle Constraints.Error (C)
          => (raise error (r', "Constraints remain in context block after term reconstruction:\n"
                    ^ ctxBlockToString (IntSyn.Null, (Gsome, Gblock)) ^ "\n"
                    ^ Print.cnstrsToString C)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkFreevars (G0, (Gsome', Gblock'), r') (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val bd = IntSyn.BlockDec (name, NONE, Gsome', ctxToList (Gblock', nil)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) bd ^ "\n")
                else () (* GEN END TAG OUTSIDE LET *)
    
      in
        (SOME bd, NONE)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) condecToConDec (blockdef (name, W), Paths.Loc (fileName, r), abbFlag) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val W' = List.map Names.Qid W (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val W'' = (List.map ((* GEN BEGIN FUNCTION EXPRESSION *) fn qid => case Names.constLookup qid
                                    of NONE => raise Names.Error ("Undeclared label "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ ".")
                                     | SOME cid => cid (* GEN END FUNCTION EXPRESSION *))
              W') (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val bd = IntSyn.BlockDef (name, NONE, W'') (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) bd ^ "\n")
                else () (* GEN END TAG OUTSIDE LET *)
      in
        (SOME bd, NONE)
      end (* GEN END FUN BRANCH *)

  fun internalInst _ = raise Match
  fun externalInst _ = raise Match

end (* GEN END FUNCTOR DECL *) (* functor ReconConDec *)
