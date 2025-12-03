

local
  module I = IntSyn
  module T = Tomega

  fun load file =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;
	

  fun printS nil = ()
    | printS (condec :: S) =
        (TextIO.print ((Print.conDecToString condec) ^ "\n"); printS S)
in

 let _ = Compiler.Control.Print.printDepth := 100;


  fun test names =
    (let 
      let a = map (fun x -> valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
      let name = foldr op^ "" names
      let _ = Names.varReset IntSyn.Null 
      let Ss = map Worldify.worldify a
      let S = foldr op@ nil Ss
      let _ = printS S
      let _ = TextIO.print "[convertPrg "
      let P = Converter.convertPrg a
      let _ = TextIO.print "convertFor... "
      let F = Converter.convertFor a
      let _ = TextIO.print "installPrg... "
      let _ = Converter.installPrg a
      let _ = TextIO.print "printing... "
      let _ = TextIO.print (TomegaPrint.forToString (I.Null, F) ^ "\n")
      let _ = TextIO.print (TomegaPrint.funToString P ^ "\n")
      let _ = TextIO.print "checking ... "
      let _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
      let _ = TextIO.print "]"
(*      let _ = (FunTypeCheck.check (P, F); Twelf.OK)   *)
(*      let LD = F.LemmaDec (names, P, F) *)
(*      let _ = TextIO.print (FunPrint.lemmaDecToString LD) *)
    in P
(*      FunNames.installName (name, F.lemmaAdd LD) *)
    end)

       
  fun print names =
    let
      let P = test names
    in
      (TextIO.print (TomegaPrint.funToString P ^ "\n"); P)
    end


  let _ = Twelf.chatter := 1
(*  let _ = FunNames.reset(); --cs *)

  let _ = load "/home/carsten/people/KarlCrary/sources.cfg";
  let _ = print ["foo"]

  let _ = load "examples/guide/sources.cfg"
  let _ = print ["cp"]


  (* Regression print for Mini-ML *)
  let _ = load "examples/mini-ml/sources.cfg"
  let _ = Twelf.loadFile "examples/mini-ml/reduce.elf"
  let _ = print ["eval"]
  let _ = print ["value"]
  let _ = print ["vs"]
  let _ = print ["tps"]
  let _ = print ["==>"]
  let _ = print ["==>*"]
  let _ = print ["closed"]

  (* Regression print for prop-calc *)
  let _ = load "examples/prop-calc/sources.cfg"
  let _ = print ["combdefn"]

  (* Regression print for ccc *)
  let _ = load "examples/ccc/sources.cfg"
  let _ = print ["conc"]

  (* Regression print for compile *)
  let _ = load "examples/compile/cpm/sources.cfg"
  let _ = print ["ccp"]
  let _ = print ["peq"]


  (* Regression print for copy *)
  let _ = Twelf.loadFile "TEST/cp.elf"
  let _ = print ["cpt"] 
  let _ = print ["new"]

(*  (* Regression test for Church-Rosser *)
  let _ = load "examples/church-rosser/sources.cfg"
  let _ = print ["identity"]
  let _ = print ["append"]
  let _ = print ["subst"] 
  let _ = print ["dia"] 
  let _ = print ["strip"] 
  let _ = print ["conf"]
  let _ = print ["cr"]
  let _ = print ["appd"]
  let _ = print ["lm1*"]
  let _ = print ["apr1*"]
  let _ = print ["apl1*"]
  let _ = print ["eq1"]
  let _ = print ["eq2"]

  (* Regression test for logic programming *)
  let _ = Twelf.loadFile "TEST/evenodd.elf"
  let _ = print ["even", "odd"]

*)
  (* Regression test for logic programming *)
  let _ = load "examples/lp-horn/sources.cfg"
  let _ = print ["can", "atm"]
  let _ = print ["iscan", "isatm"]
  let _ = print ["s_sound", "h_sound", "i_sound"]
  let _ = print ["cmpcs", "cmpai"]


  (* Regression test for logic programming *)
  let _ = load "examples/lp/sources.cfg"
  let _ = print ["can", "atm"]
  let _ = print ["iscan", "isatm"]
  let _ = print ["s_sound", "h_sound", "i_sound"]
  let _ = print ["cmpcs", "cmpai"]

  (* Regression test for Cut-Elimination *)
  let _ = load "examples/cut-elim/sources.cfg"
  let _ = print ["ca"]
  let _ = print ["ce"]
  let _ = print ["ca'"]
  let _ = print ["ce'"]

  (* Regression test for Kolmogoroff translation *)
  let _ = load "examples/kolm/sources.cfg"
  let _ = print ["kolm"]
  let _ = print ["existskolm"]
  let _ = print ["nj_nk"]
  let _ = print ["equiv"]
  let _ = print ["complete"]


  (* Regression test for compile *)
  let _ = load "examples/compile/cls/sources.cfg"
  let _ = test ["trans", "vtrans"]
  let _ = test ["feval"]
  let _ = test ["=>"]
  let _ = test [">=>*"]
  let _ = test [">ceval"] 
  let _ = test ["append"]
  let _ = test ["subcomp"] 
  let _ = test ["cev_complete"]
  let _ = test ["<"]
  let _ = test ["trans*"]
  let _ = test ["spl"]
  let _ = test ["cls_sound"]



end

