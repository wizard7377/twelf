(* Delphin Frontend *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Delphin ((* structure Tomega : TOMEGA *)
                 structure Parser : PARSER
                 structure DextSyn : DEXTSYN
                 structure Parse : PARSE
                   sharing Parse.DextSyn = DextSyn
                 structure Twelf : TWELF
                 structure Trans : TRANS
                   sharing Trans.DextSyn = DextSyn) : DELPHIN =
struct
  local
    (* GEN BEGIN TAG OUTSIDE LET *) val version = "Delphin, Version 0.5, July 2003" (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val prompt = "> " (* GEN END TAG OUTSIDE LET *)

    exception What of Tomega.prg

    (* Added by ABP - Temporary to run tests *)
    structure I = IntSyn
    structure T = Tomega

    fun chatter chlev f =
        if !Global.chatter >= chlev
          then print (f ())
        else ()

    fun loadFile (s1, s2) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.reset () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.loadFile s1 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 1 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "[Opening file " ^ s2 ^ "]\n" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Trans.internalizeSig () (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 4 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "[Parsing ..." (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (DextSyn.Ast EDs) = Parse.gparse s2 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 4 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "]\n[Translation ..." (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val P = Trans.transDecs EDs (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 4 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "]\n[Externalization ..." (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (*      val _ = print "* Type reconstruction done\n" *)
        (* GEN BEGIN TAG OUTSIDE LET *) val P' = Trans.externalizePrg P (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 4 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "]\n" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 4 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "[Operational Semantics ..." (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (*      val _ = raise What P'
        val _ = print "* Externalization done\n" *)
    (*      val _  = TomegaTypeCheck.checkPrg (IntSyn.Null, (P', Tomega.True))
        val _ = print "* Typechecking done\n"
    *)      (* GEN BEGIN TAG OUTSIDE LET *) val V  = Opsem.topLevel P' (* GEN END TAG OUTSIDE LET *)  (* was evalPrg --cs Mon Jun 30 12:09:21 2003*)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 4 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "]\n" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (*      val _ = print "* Operational semantics done\n" *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = chatter 1 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => "[Closing file " ^ s2 ^ "]\n" (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
      in
        V
      end

    fun top () = loop ()

    and loop () =
      let
         (* GEN BEGIN TAG OUTSIDE LET *) val _ = print prompt (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (DextSyn.Ast ED) = Parse.sparse () (* GEN END TAG OUTSIDE LET *)
    (*         val res = Trans.transDecs ED    *)
      in
         loop ()
      end



  (* input:
      sourcesFile = .elf file to load
      funcList = list of functions that need to be loaded
                 first element is the function that will be called
      arg = LF object which is the argument
   *)

    fun runSimpleTest sourcesFile funcList args  =
      let
    
        fun (* GEN BEGIN FUN FIRST *) test (names as [name]) =
          (let
             (* GEN BEGIN TAG OUTSIDE LET *) val La = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => valOf (Names.constLookup (valOf (Names.stringToQid x))) (* GEN END FUNCTION EXPRESSION *)) names (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val (lemma, projs, sels) = Converter.installPrg La (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val P = Tomega.lemmaDef lemma (* GEN END TAG OUTSIDE LET *)
            (*           val P = Redundant.convert (Tomega.lemmaDef lemma) *)
             (* GEN BEGIN TAG OUTSIDE LET *) val F = Converter.convertFor La (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val _ = TextIO.print ("\n" ^ TomegaPrint.funToString ((map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid) (* GEN END FUNCTION EXPRESSION *)) La,
                                                     projs), P) ^ "\n") (* GEN END TAG OUTSIDE LET *)
           in (P, F)
           end) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) test names =
          (let
             (* GEN BEGIN TAG OUTSIDE LET *) val La = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => valOf (Names.constLookup (valOf (Names.stringToQid x))) (* GEN END FUNCTION EXPRESSION *)) names (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val (lemma, projs, sels) = Converter.installPrg La (* GEN END TAG OUTSIDE LET *)
             (* val P = Tomega.lemmaDef lemma *)
             (* GEN BEGIN TAG OUTSIDE LET *) val P = Redundant.convert (Tomega.lemmaDef lemma) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val F = Converter.convertFor La (* GEN END TAG OUTSIDE LET *)
              
             (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val _ = TextIO.print ("\n" ^ TomegaPrint.funToString ((map ((* GEN BEGIN FUNCTION EXPRESSION *) fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid) (* GEN END FUNCTION EXPRESSION *)) La,
                                                     projs), P) ^ "\n") (* GEN END TAG OUTSIDE LET *)
           in (Tomega.lemmaDef (hd sels), F)
           end) (* GEN END FUN BRANCH *)
    
        fun checkDec (u, D as T.UDec (I.Dec (_, V))) =  (print "$"; TypeCheck.typeCheck (I.Null, (u, V)))
    (*        | checkDec (u, D as PDec (_, T.All (D, F')))) = ???  *)
    
    
    
        fun (* GEN BEGIN FUN FIRST *) makeSpine ([], F) = (T.Nil, F) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) makeSpine (x :: L, F' as T.And (F1, F2)) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val (S', F') =  makeSpine (L, T.forSub (F', T.Dot (T.Exp (I.Root (I.Def x, I.Nil)), T.id))) (* GEN END TAG OUTSIDE LET *)
            in
              (T.AppExp (I.Root (I.Def x, I.Nil), S'), F')
            end (* GEN END FUN BRANCH *)
    
          | (* GEN BEGIN FUN BRANCH *) makeSpine (x :: L, T.All ((D, _), F')) =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkDec(I.Root (I.Def x, I.Nil), D) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (S', F') =  makeSpine (L, T.forSub (F', T.Dot (T.Exp (I.Root (I.Def x, I.Nil)), T.id))) (* GEN END TAG OUTSIDE LET *)
            in
              (T.AppExp (I.Root (I.Def x, I.Nil), S'), F')
            end (* GEN END FUN BRANCH *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.make sourcesFile (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (P, F) = test funcList (* GEN END TAG OUTSIDE LET *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = print ((TomegaPrint.forToString (I.Null, F)) ^ "\n") (* GEN END TAG OUTSIDE LET *)
    (*      val _ = TextIO.print ("\n" ^ TomegaPrint.funToString (([name], []), P) ^ "\n") *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val xs = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn a => valOf (Names.constLookup (valOf (Names.stringToQid a))) (* GEN END FUNCTION EXPRESSION *)) args (* GEN END TAG OUTSIDE LET *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val  (S', F') = makeSpine (xs, F) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val P' = T.Redex(P, S') (* GEN END TAG OUTSIDE LET *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = TomegaTypeCheck.checkPrg (I.Null, (P', F')) (* GEN END TAG OUTSIDE LET *)
    
    
    (*      val P' = if isDef then (T.Redex(P, T.AppExp (I.Root (I.Def x, I.Nil), T.
    Nil))) else (T.Redex(P, T.AppExp (I.Root (I.Const x, I.Nil), T.Nil)))
    *)
    
          (*
        val _ = TextIO.print "\n"
        val _ = TextIO.print (TomegaPrint.prgToString (I.Null, P'))
        val _ = TextIO.print "\n"
           *)
    
    
    (*  T.AppExp (I.Root (I.Def x, I.Nil), T.Nil) *)
        (* GEN BEGIN TAG OUTSIDE LET *) val result = Opsem.evalPrg P' (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = TextIO.print "\n\nEOC\n\n" (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = TextIO.print (TomegaPrint.prgToString (I.Null, result)) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val _ = TextIO.print "\n" (* GEN END TAG OUTSIDE LET *)
      in
        ()
      end

    fun eval P =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val V = Opsem.evalPrg P (* GEN END TAG OUTSIDE LET *)
        in
          V
        end


    (* **************************************** *)


  in
    (* GEN BEGIN TAG OUTSIDE LET *) val version = version (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val loadFile = loadFile (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val top = top (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val runSimpleTest = runSimpleTest (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val eval = eval (* GEN END TAG OUTSIDE LET *)

  end
end (* GEN END FUNCTOR DECL *)  (* functor Delphin *)
