(* Reconstruct module type entries *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga, Jeff Polakow *)

module ReconConDec (Global : GLOBAL)
                     (*! module IntSyn' : INTSYN !*)
                     (Names : NAMES)
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     (Abstract : ABSTRACT)
                     (*! sharing Abstract.IntSyn = IntSyn' !*)
                     (*! module Paths' : PATHS !*)
                     module ReconTerm' : RECON_TERM
                     (*! sharing ReconTerm'.IntSyn = IntSyn' !*)
                     (*! sharing ReconTerm'.Paths = Paths' !*)
                     (Constraints : CONSTRAINTS)
                     (*! sharing Constraints.IntSyn = IntSyn' !*)
                     (Strict : STRICT)
                     (*! sharing Strict.IntSyn = IntSyn' !*)
                     (*! sharing Strict.Paths = Paths' !*)
                     (TypeCheck : TYPECHECK)
                     (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                     (Timers : TIMERS)
                     (Print : PRINT)
                     (*! sharing Print.IntSyn = IntSyn' !*)
                     (Msg : MSG): RECON_CONDEC =
struct
  (*! module IntSyn = IntSyn' !*)
  (*! module Paths = Paths' !*)
  module ExtSyn = ReconTerm'

  exception Error of string

  (* error (r, msg) raises a syntax error within region r with text msg *)
  let rec error (r, msg) = raise Error (Paths.wrap (r, msg))

  type name = string

  (* Constant declarations *)
  type condec =
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
  let rec condecToConDec = function (condec(name, tm), Paths.Loc (fileName, r), abbFlag) -> 
      let
        let _ = Names.varReset IntSyn.Null
        let _ = ExtSyn.resetErrors fileName
        let ExtSyn.JClass ((V, oc), L) =
              (Timers.time Timers.recon ExtSyn.recon) (ExtSyn.jclass tm)
        let _ = ExtSyn.checkErrors (r)
        let (i, V') = (Timers.time Timers.abstract Abstract.abstractDecImp) V
                        handle Abstract.Error (msg)
                               => raise Abstract.Error (Paths.wrap (r, msg))
        let cd = Names.nameConDec (IntSyn.conDec (name, NONE, i, IntSyn.Normal, V', L))
        let ocd = Paths.dec (i, oc)
        let _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                else ()
        let _ = if !Global.doubleCheck
                  then (Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni L)
                else ()
      in
        (SOME(cd), SOME(ocd))
      end
    | (condef(optName, tm1, tm2Opt), Paths.Loc (fileName, r), abbFlag) -> 
      let
        let _ = Names.varReset IntSyn.Null
        let _ = ExtSyn.resetErrors fileName
        let f = (case tm2Opt
                   of NONE => ExtSyn.jterm tm1
                    | SOME tm2 => ExtSyn.jof (tm1, tm2))
        let f' = (Timers.time Timers.recon ExtSyn.recon) f
        let ((U, oc1), (V, oc2Opt), L) =
            (case f'
               of ExtSyn.JTerm ((U, oc1), V, L) =>
                    ((U, oc1), (V, NONE), L)
                | ExtSyn.JOf ((U, oc1), (V, oc2), L) =>
                    ((U, oc1), (V, SOME oc2), L))
        let _ = ExtSyn.checkErrors (r)
        let (i, (U'', V'')) =
                (Timers.time Timers.abstract Abstract.abstractDef) (U, V)
                handle Abstract.Error (msg)
                          => raise Abstract.Error (Paths.wrap (r, msg))
        let name = case optName of NONE => "_" | SOME(name) => name
        let ocd = Paths.def (i, oc1, oc2Opt)
        let cd = if abbFlag then Names.nameConDec (IntSyn.AbbrevDef (name, NONE, i, U'', V'', L))
                 else (Strict.check ((U'', V''), SOME(ocd));
                       (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
                       (* (case optName of NONE => () | _ => Strict.checkType ((i, V''), SOME(ocd))); *)
                       (Names.nameConDec (IntSyn.ConDef (name, NONE, i, U'', V'', L,
                                                         IntSyn.ancestor U''))))

        let _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                else ()
        let _ = if !Global.doubleCheck
                  then ((Timers.time Timers.checking TypeCheck.check) (V'', IntSyn.Uni L);
                        (Timers.time Timers.checking TypeCheck.check) (U'', V''))
                else ()
        let optConDec = case optName of NONE => NONE | SOME _ => SOME (cd)
      in
        (optConDec, SOME(ocd))
      end
    | (blockdec (name, Lsome, Lblock), Paths.Loc (fileName, r), abbFlag) -> 
      let
        let rec makectx nil = IntSyn.Null
          | makectx (D :: L) = IntSyn.Decl (makectx L, D)
        let rec ctxToList (IntSyn.Null, acc) = acc
          | ctxToList (IntSyn.Decl (G, D), acc) = ctxToList (G, D :: acc)
        let rec ctxAppend (G, IntSyn.Null) = G
          | ctxAppend (G, IntSyn.Decl (G', D)) = IntSyn.Decl (ctxAppend (G, G'), D)
        let rec ctxBlockToString (G0, (G1, G2)) =
            let
              let _ = Names.varReset IntSyn.Null
              let G0' = Names.ctxName G0
              let G1' = Names.ctxLUName G1
              let G2' = Names.ctxLUName G2
            in
              Print.ctxToString (IntSyn.Null, G0') ^ "\n"
              ^ (case G1' of IntSyn.Null => "" | _ => "some " ^ Print.ctxToString (G0', G1') ^ "\n")
              ^ "pi " ^ Print.ctxToString (ctxAppend (G0', G1'), G2')
            end
        let rec checkFreevars (IntSyn.Null, (G1, G2), r) = ()
          | checkFreevars (G0, (G1, G2), r) =
            let
              let _ = Names.varReset IntSyn.Null
              let G0' = Names.ctxName G0
              let G1' = Names.ctxLUName G1
              let G2' = Names.ctxLUName G2
            in
              error (r, "Free variables in context block after term reconstruction:\n"
                     ^ ctxBlockToString (G0', (G1', G2')))
            end

        let (gsome, gblock) = (makectx Lsome, makectx Lblock)

        let r' = (case (ExtSyn.ctxRegion gsome, ExtSyn.ctxRegion gblock)
                    of (SOME r1, SOME r2) => Paths.join (r1, r2)
                     | (_, SOME r2) => r2)

        let _ = Names.varReset IntSyn.Null
        let _ = ExtSyn.resetErrors fileName
        let j = ExtSyn.jwithctx (gsome,
                  ExtSyn.jwithctx (gblock, ExtSyn.jnothing))
        let ExtSyn.JWithCtx (Gsome, ExtSyn.JWithCtx (Gblock, _)) =
              (Timers.time Timers.recon ExtSyn.recon) j
        let _ = ExtSyn.checkErrors (r)
        let (G0, [Gsome', Gblock']) =   (* closed nf *)
          Abstract.abstractCtxs [Gsome, Gblock]
          handle Constraints.Error (C)
          => (raise error (r', "Constraints remain in context block after term reconstruction:\n"
                    ^ ctxBlockToString (IntSyn.Null, (Gsome, Gblock)) ^ "\n"
                    ^ Print.cnstrsToString C))
        let _ = checkFreevars (G0, (Gsome', Gblock'), r')
        let bd = IntSyn.BlockDec (name, NONE, Gsome', ctxToList (Gblock', nil))
        let _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) bd ^ "\n")
                else ()

      in
        (SOME bd, NONE)
      end
    | (blockdef (name, W), Paths.Loc (fileName, r), abbFlag) -> 
      let
        let W' = List.map Names.Qid W
        let W'' = (List.map (fun qid -> case Names.constLookup qid
                                    of NONE => raise Names.Error ("Undeclared label "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ ".")
                                     | SOME cid => cid)
              W')
        let bd = IntSyn.BlockDef (name, NONE, W'')
        let _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) bd ^ "\n")
                else ()
      in
        (SOME bd, NONE)
      end

  let rec internalInst _ = raise Match
  let rec externalInst _ = raise Match

end (* functor ReconConDec *)
