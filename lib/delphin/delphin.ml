(* Delphin Frontend *)
(* Author: Carsten Schuermann *)

module Delphin ((* (Tomega : TOMEGA) *)
                 (Parser : PARSER)
                 (DextSyn : DEXTSYN)
                 (Parse : PARSE)
                   sharing Parse.DextSyn = DextSyn
                 (Twelf : TWELF)
                 (Trans : TRANS)
                   sharing Trans.DextSyn = DextSyn) : DELPHIN =
struct
  local
    let version = "Delphin, Version 0.5, July 2003"

    let prompt = "> "

    exception What of Tomega.Prg

    (* Added by ABP - Temporary to run tests *)
    module I = IntSyn
    module T = Tomega

    fun chatter chlev f =
        if !Global.chatter >= chlev
          then print (f ())
        else ()

    fun loadFile (s1, s2) =
      let
        let _ = Twelf.reset ()
        let _ = Twelf.loadFile s1
        let _ = chatter 1 (fn () => "[Opening file " ^ s2 ^ "]\n")
        let _ = Trans.internalizeSig ()
        let _ = chatter 4 (fn () => "[Parsing ...")
        let (DextSyn.Ast EDs) = Parse.gparse s2
        let _ = chatter 4 (fn () => "]\n[Translation ...")
        let P = Trans.transDecs EDs
        let _ = chatter 4 (fn () => "]\n[Externalization ...")
(*      let _ = print "* Type reconstruction done\n" *)
        let P' = Trans.externalizePrg P
        let _ = chatter 4 (fn () => "]\n")
        let _ = chatter 4 (fn () => "[Operational Semantics ...")
(*      let _ = raise What P'
        let _ = print "* Externalization done\n" *)
(*      let _  = TomegaTypeCheck.checkPrg (IntSyn.Null, (P', Tomega.True))
        let _ = print "* Typechecking done\n"
*)      let V  = Opsem.topLevel P'  (* was evalPrg --cs Mon Jun 30 12:09:21 2003*)
        let _ = chatter 4 (fn () => "]\n")
(*      let _ = print "* Operational semantics done\n" *)
        let _ = chatter 1 (fn () => "[Closing file " ^ s2 ^ "]\n")
      in
        V
      end

    fun top () = loop ()

    and loop () =
      let
         let _ = print prompt
         let (DextSyn.Ast ED) = Parse.sparse ()
(*         let res = Trans.transDecs ED    *)
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

        fun test (names as [name]) =
          (let
             let La = map (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
             let (lemma, projs, sels) = Converter.installPrg La
             let P = Tomega.lemmaDef lemma
(*           let P = Redundant.convert (Tomega.lemmaDef lemma) *)
             let F = Converter.convertFor La
             let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
             let _ = TextIO.print ("\n" ^ TomegaPrint.funToString ((map (fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid)) La,
                                                     projs), P) ^ "\n")
           in (P, F)
           end)
          | test names =
          (let
             let La = map (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
             let (lemma, projs, sels) = Converter.installPrg La
             (* let P = Tomega.lemmaDef lemma *)
             let P = Redundant.convert (Tomega.lemmaDef lemma)
             let F = Converter.convertFor La

             let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
             let _ = TextIO.print ("\n" ^ TomegaPrint.funToString ((map (fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid)) La,
                                                     projs), P) ^ "\n")
           in (Tomega.lemmaDef (hd sels), F)
           end)

        fun checkDec (u, D as T.UDec (I.Dec (_, V))) =  (print "$"; TypeCheck.typeCheck (I.Null, (u, V)))
(*        | checkDec (u, D as PDec (_, T.All (D, F')))) = ???  *)



        fun makeSpine ([], F) = (T.Nil, F)
          | makeSpine (x :: L, F' as T.And (F1, F2)) =
            let
              let (S', F') =  makeSpine (L, T.forSub (F', T.Dot (T.Exp (I.Root (I.Def x, I.Nil)), T.id)))
            in
              (T.AppExp (I.Root (I.Def x, I.Nil), S'), F')
            end

          | makeSpine (x :: L, T.All ((D, _), F')) =
            let
              let _ = checkDec(I.Root (I.Def x, I.Nil), D)
              let (S', F') =  makeSpine (L, T.forSub (F', T.Dot (T.Exp (I.Root (I.Def x, I.Nil)), T.id)))
            in
              (T.AppExp (I.Root (I.Def x, I.Nil), S'), F')
            end
        let _ = Twelf.make sourcesFile
        let (P, F) = test funcList

        let _ = print ((TomegaPrint.forToString (I.Null, F)) ^ "\n")
(*      let _ = TextIO.print ("\n" ^ TomegaPrint.funToString (([name], []), P) ^ "\n") *)

        let xs = map (fun a -> valOf (Names.constLookup (valOf (Names.stringToQid a)))) args

        let  (S', F') = makeSpine (xs, F)
        let P' = T.Redex(P, S')

        let _ = TomegaTypeCheck.checkPrg (I.Null, (P', F'))


(*      let P' = if isDef then (T.Redex(P, T.AppExp (I.Root (I.Def x, I.Nil), T.
Nil))) else (T.Redex(P, T.AppExp (I.Root (I.Const x, I.Nil), T.Nil)))
*)

          (*
        let _ = TextIO.print "\n"
        let _ = TextIO.print (TomegaPrint.prgToString (I.Null, P'))
        let _ = TextIO.print "\n"
           *)


(*  T.AppExp (I.Root (I.Def x, I.Nil), T.Nil) *)
        let result = Opsem.evalPrg P'
        let _ = TextIO.print "\n\nEOC\n\n"
        let _ = TextIO.print (TomegaPrint.prgToString (I.Null, result))
        let _ = TextIO.print "\n"
      in
        ()
      end

    fun eval P =
        let
          let V = Opsem.evalPrg P
        in
          V
        end


    (* **************************************** *)


  in
    let version = version
    let loadFile = loadFile
    let top = top

    let runSimpleTest = runSimpleTest
    let eval = eval

  end
end  (* functor Delphin *)
