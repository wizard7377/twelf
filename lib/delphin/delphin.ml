(* Delphin Frontend *)

(* Author: Carsten Schuermann *)

module Delphin
    (Parser : PARSER)
    (DextSyn : DEXTSYN)
    (Parse : PARSE)
    (Twelf : TWELF)
    (Trans : TRANS) : DELPHIN = struct
  let version = "Delphin, Version 0.5, July 2003"
  let prompt = "> "

  exception What of Tomega.prg
  (* Added by ABP - Temporary to run tests *)

  module I = IntSyn
  module T = Tomega

  let rec chatter chlev f =
    if !Global.chatter >= chlev then print (f ()) else ()

  let rec loadFile (s1, s2) =
    (*      val _ = print "* Type reconstruction done\n" *)
    (*      val _ = raise What P'
        val _ = print "* Externalization done\n" *)
    (*      val _  = TomegaTypeCheck.checkPrg (IntSyn.Null, (P', Tomega.True))
        val _ = print "* Typechecking done\n"
*)
    (* was evalPrg --cs Mon Jun 30 12:09:21 2003*)
    (*      val _ = print "* Operational semantics done\n" *)
    let _ = Twelf.reset () in
    let _ = Twelf.loadFile s1 in
    let _ = chatter 1 (fun () -> "[Opening file " ^ s2 ^ "]\n") in
    let _ = Trans.internalizeSig () in
    let _ = chatter 4 (fun () -> "[Parsing ...") in
    let (DextSyn.Ast EDs) = Parse.gparse s2 in
    let _ = chatter 4 (fun () -> "]\n[Translation ...") in
    let P = Trans.transDecs EDs in
    let _ = chatter 4 (fun () -> "]\n[Externalization ...") in
    let P' = Trans.externalizePrg P in
    let _ = chatter 4 (fun () -> "]\n") in
    let _ = chatter 4 (fun () -> "[Operational Semantics ...") in
    let V = Opsem.topLevel P' in
    let _ = chatter 4 (fun () -> "]\n") in
    let _ = chatter 1 (fun () -> "[Closing file " ^ s2 ^ "]\n") in
    V

  let rec top () = loop ()

  and loop () =
    (*         val res = Trans.transDecs ED    *)
    let _ = print prompt in
    let (DextSyn.Ast ED) = Parse.sparse () in
    loop ()
  (* input:
      sourcesFile = .elf file to load
      funcList = list of functions that need to be loaded
                 first element is the function that will be called
      arg = LF object which is the argument
   *)

  let rec runSimpleTest sourcesFile funcList args =
    (*        | checkDec (u, PDec (_, T.All (D, F')))) = ???  *)
    (*      val _ = TextIO.print ("\n" ^ TomegaPrint.funToString (([name], []), P) ^ "\n") *)
    (*      val P' = if isDef then (T.Redex(P, T.AppExp (I.Root (I.Def x, I.Nil), T.
Nil))) else (T.Redex(P, T.AppExp (I.Root (I.Const x, I.Nil), T.Nil)))
*)
    (*
        val _ = TextIO.print "\n"
        val _ = TextIO.print (TomegaPrint.prgToString (I.Null, P'))
        val _ = TextIO.print "\n"
           *)
    (*  T.AppExp (I.Root (I.Def x, I.Nil), T.Nil) *)
    let rec test = function
      | names ->
          (*           val P = Redundant.convert (Tomega.lemmaDef lemma) *)
          let La =
            map
              (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
              names
          in
          let lemma, projs, sels = Converter.installPrg La in
          let P = Tomega.lemmaDef lemma in
          let F = Converter.convertFor La in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) in
          let _ =
            TextIO.print
              ("\n"
              ^ TomegaPrint.funToString
                  ( ( map
                        (fun cid -> IntSyn.conDecName (IntSyn.sgnLookup cid))
                        La,
                      projs ),
                    P )
              ^ "\n")
          in
          (P, F)
      | names ->
          (* val P = Tomega.lemmaDef lemma *)
          let La =
            map
              (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
              names
          in
          let lemma, projs, sels = Converter.installPrg La in
          let P = Redundant.convert (Tomega.lemmaDef lemma) in
          let F = Converter.convertFor La in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F)) in
          let _ =
            TextIO.print
              ("\n"
              ^ TomegaPrint.funToString
                  ( ( map
                        (fun cid -> IntSyn.conDecName (IntSyn.sgnLookup cid))
                        La,
                      projs ),
                    P )
              ^ "\n")
          in
          (Tomega.lemmaDef (hd sels), F)
    in
    let rec checkDec (u, D) =
      print "$";
      TypeCheck.typeCheck (I.Null, (u, V))
    in
    let rec makeSpine = function
      | [], F -> (T.Nil, F)
      | x :: L, F' ->
          let S', F' =
            makeSpine
              (L, T.forSub (F', T.Dot (T.Exp (I.Root (I.Def x, I.Nil)), T.id)))
          in
          (T.AppExp (I.Root (I.Def x, I.Nil), S'), F')
      | x :: L, T.All ((D, _), F') ->
          let _ = checkDec (I.Root (I.Def x, I.Nil), D) in
          let S', F' =
            makeSpine
              (L, T.forSub (F', T.Dot (T.Exp (I.Root (I.Def x, I.Nil)), T.id)))
          in
          (T.AppExp (I.Root (I.Def x, I.Nil), S'), F')
    in
    let _ = Twelf.make sourcesFile in
    let P, F = test funcList in
    let _ = print (TomegaPrint.forToString (I.Null, F) ^ "\n") in
    let xs =
      map
        (fun a -> valOf (Names.constLookup (valOf (Names.stringToQid a))))
        args
    in
    let S', F' = makeSpine (xs, F) in
    let P' = T.Redex (P, S') in
    let _ = TomegaTypeCheck.checkPrg (I.Null, (P', F')) in
    let result = Opsem.evalPrg P' in
    let _ = TextIO.print "\n\nEOC\n\n" in
    let _ = TextIO.print (TomegaPrint.prgToString (I.Null, result)) in
    let _ = TextIO.print "\n" in
    ()

  let rec eval P =
    let V = Opsem.evalPrg P in
    V
  (* **************************************** *)

  let version = version
  let loadFile = loadFile
  let top = top
  let runSimpleTest = runSimpleTest
  let eval = eval
end

(* functor Delphin *)
(* Delphin Frontend *)

(* Author: Carsten Schuermann *)

module type DELPHIN = sig
  val version : string
  val loadFile : string * string -> unit
  val top : unit -> unit
  val runSimpleTest : string -> string list -> string list -> unit
  val eval : Tomega.prg -> Tomega.prg
end
