
local 
  module F = FunSyn
  module I = IntSyn 
  module S = StateSyn

  fun load file =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;
	

  (* just for non-inductive types *)
  fun transformOrder' (G, Order.Arg k) = 
      let 
	let k' = (I.ctxLength G) -k+1
	let I.Dec (_, V) = I.ctxDec (G, k')
      in
	S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
      end
    | transformOrder' (G, Order.Lex Os) = 
        S.Lex (map (fun O -> transformOrder' (G, O)) Os)
    | transformOrder' (G, Order.Simul Os) = 
        S.Simul (map (fun O -> transformOrder' (G, O)) Os)

  fun transformOrder (G, F.All (F.Prim D, F), Os) =
	S.All (D, transformOrder (I.Decl (G, D), F, Os))
    | transformOrder (G, F.And (F1, F2), O :: Os) =
	S.And (transformOrder (G, F1, [O]),
	       transformOrder (G, F2, Os))
    | transformOrder (G, F.Ex _, [O]) = transformOrder' (G, O) 

  fun select c = (Order.selLookup c handle _ => Order.Lex [])
    
  fun test (depth, names) =
    (let 
      let a = map (fun x -> valOf (Names.nameLookup x)) names
      let name = foldr op^ "" names
      let _ = Names.varReset ()
      let F = RelFun.convertFor a
      let Os =  map select a
      let _ = Twelf.chatter := 5
      let _ = MTPi.reset ()
      let _ = MTPi.init (depth, (F, transformOrder(I.Null, F, Os)))
let _ = raise Domain
      let _ = MTPi.auto ()
      let _ = Twelf.chatter := 3
    in
      ()
    end)
in
  let _ = Twelf.chatter := 3
  let _ = FunNames.reset();

(*
  (* Regression test for Mini-ML *)
  let _ = load "examples/mini-ml/test.cfg"
  let _ = Twelf.loadFile "examples/mini-ml/reduce.elf"
  let _ = test (5,["vs"])
  let _ = test (9, ["evalRed"])
(*  let _ = test ["tps"] *)


  let _ = load "examples/ccc/test.cfg";
  let _ = test (6, ["conc"])

  let _ = load "examples/prop-calc/test.cfg";
  let _ = test (6, ["abst"])


  (* Regression test for compile *)
  let _ = load "examples/compile/cpm/test.cfg"
  let _ = test (20, ["ccf"])
  let _ = test (6, ["peqr"])


  let _ = load "examples/lp-horn/test.cfg";
  let _ = test (4, ["s_snd", "h_snd", "i_snd"])
  let _ = test (4, ["ss_cn", "hs_at", "is_at"])
  let _ = test (4, ["compcs", "compai"])
*)

  let _ = load "examples/arith/test.cfg";
  let _ = test (3, ["assoc"]);

(* -----------------------
  let _ = load "TEST/fol.cfg";
 
  let _ = MTPGlobal.maxFill := 5
  let _ = test ["identity"]
  let _ = MTPGlobal.maxFill := 12
  let _ = test ["curry"]
(*  let _ = test ["uncurry"] 
  let _ = MTPGlobal.maxFill := 15
  let _ = test ["split"]  *)
(*  let _ = MTPGlobal.maxFill := 13
  let _ = test ["join"] *)
*)
end