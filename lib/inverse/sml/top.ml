(* -------------------------------------------------------------------------- *)
(*  Printing                                                                  *)
(* -------------------------------------------------------------------------- *)

Control.Print.printDepth := 50;
Control.Print.printLength := 1000;
Control.Print.stringDepth := 1000;

(* -------------------------------------------------------------------------- *)
(*  Loading                                                                   *)
(* -------------------------------------------------------------------------- *)

CM.make "sources.cm"; 

Twelf.doubleCheck := true;
Twelf.Print.depth := SOME 0
Twelf.Print.length := SOME 0
Twelf.Timers.reset()
let test = "../../../../test/";
Twelf.make (test ^ "talt/sources-chk.cfg");
Twelf.make (test ^ "talt/sources.cfg")
Twelf.make (test ^ "sml-sound/sources.cfg");
Twelf.make (test ^ "princeton/sources.cfg");
Twelf.make (test ^ "misc/sources.cfg");

Twelf.Timers.check()
Timers.reset()
let signat = (Translate.translate_signat ())
Timers.check()
Typecheck.EE.check_signat signat
Timers.reset()

Syntax.Signat.reset()


  handle Syntax.Fail_exp x => x;

(Lib.printl "";Timers.check())

Twelf.Timers.check()
Timers.check()

Twelf.Timers.reset()

(Translate.EE.translate_signature();raise Success)
  handle TypecheckEE.Fail_exp_skel x => x;

(Translate.EL.translate_signature();raise Success)
  handle TypecheckEE.Fail_exp_skel x => x;

(* -------------------------------------------------------------------------- *)
(*  Debug                                                                     *)
(* -------------------------------------------------------------------------- *)

module D = Debug;
module L = Lib;
module T = TranslateEE;
module S = TypecheckEE;
module Sgn = S.Sgn;
module I = IntSyn;
module D = Debug;
module C = Context;


T.translate_signature
 I.sgnLookup 9
S.

let rec name n = (n,I.conDecName (I.sgnLookup n));
let rec get x (I.ConDec(x',_,_,_,_,_)) = x = x' | get _ _ = false;
let (N,_) = I.sgnSize();
let cs = map I.sgnLookup (Lib.upto(0,N - 1)); 
let n = N-2;
let ns = L.upto(0,n);
let cds = map IntSyn.sgnLookup ns;
let cds' = L.filter (fn (id,dec) => T.can_translate dec) (L.zip ns cds);
let cds'' = map T.translate_condec cds';
let rec fold_fun (dec,sgn) = (D.print ("translating: " ^ I.conDecName (I.sgnLookup (S.id dec)) ^ "\n");Sgn.insert sgn dec);
let sgn = foldl fold_fun (Sgn.empty()) cds'';

let t_val = I.sgnLookup 11
let S.Decl s_val = Sgn.lookup sgn 10

let bug = Def{id=11,
              name="1+",
              exp=tm_tm,
              def=Lam{var=NONE,
                      body=Root(Const 4,App(Root(BVar 1,Nil),Nil))},
              height = 1,
              root = 4,
              uni = Type
             }


eta_expand sgn (Lam{var=NONE,body=Root(Const 4,App(Root(BVar 1,Nil),Nil))})


    fun insert sgn (Decl {id,name,exp,uni}) = 
        let
          let exp' = eta_expand sgn exp 
        in
          check sgn exp' (Uni uni);
          Sig.insert sgn (id,Decl {id=id,name=name,exp=exp',uni=uni})
        end
      | insert sgn (Def {id,name,exp,def,height,root,uni}) =
        let
          let exp' = eta_expand sgn exp 
          let def' = eta_expand sgn def 
        in
          check sgn exp' (Uni uni);
          check sgn def' exp';
          Sig.insert sgn (id,Def {id=id,name=name,exp=exp',def=def',
                                  height=height,root=root,uni=uni})
        end
      | insert sgn (Abbrev {id,name,exp,def,uni}) =
        let
          let exp' = eta_expand sgn exp 
          let def' = eta_expand sgn def 
        in
          check sgn exp' (Uni uni);
          check sgn def' exp';
          Sig.insert sgn (id,Abbrev{id=id,name=name,exp=exp',
                                    def=def',uni=uni})
        end


S.print_exp sgn t_val


S.print_exp sgn (#exp s_val)

- 
PI (PI (PI tm. 
	   tm). 
       tm). 
   PI (tm-eq ^ (1 ^ (LAM. f ^ 1)
		1 ^ (LAM. f ^ 1))). 
      type


open S
let f = Const 4
let tm_eqi = Const 8
let test6 = Const 9
let tm = Const 0
let tm_eq = Const 6

let tm_exp = Root(tm,Nil)
let tm_tm = Pi{var=NONE,arg=tm_exp,depend=No,body=tm_exp}
let tm_tm_tm = Pi{var=NONE,arg=tm_tm,depend=No,body=tm_exp}
let tp = expType





let one = Root(BVar 1,Nil)
let two = Root(BVar 2,Nil)
let f1 = Root(f,App(one,Nil))
let lam_f1 = Lam {var=NONE,body=f1}
let one_lam_f1 = Root(BVar 1,App(lam_f1,Nil))
let two_one = Root(BVar 2,App(one,Nil))
let lam_21 = Lam{var=NONE,body=two_one}
let tm_eqi_1_lam_f1 = Root(tm_eqi,App(one_lam_f1,Nil))
let spine0 = App(tm_eqi_1_lam_f1,Nil)
let spine1 = App(lam_21,spine0)
let test6_args = Root(test6,spine1)

let spine2 = App(one_lam_f1,App(one_lam_f1,Nil))
let tm_eq_args = Root(tm_eq,spine2)
let pi_tm_eq = Pi{var=NONE,arg=tm_eq_args,depend=No,body=tp}
let pi_tm_tm_tm = Pi{var=NONE,arg=tm_tm_tm,depend=No,body=pi_tm_eq}
let one_sp = App(one,Nil)

let ctx = C.push C.empty (NONE:string option,tm_tm_tm)

let ctx' = C.push ctx (NONE:string option,tm_tm)


check_exp sgn ctx test6_args tp

focus sgn ctx spine1 pi_tm_tm_tm

check_exp sgn ctx lam_21 tm_tm_tm

let sub1 = (Dot(lam_21,id_sub))




focus sgn ctx spine0 (apply_exp sub1 pi_tm_eq)

apply_exp sub1 tm_eq_args

print_exp sgn tm_eq_args

apply_spine sub1 spine2

print_spine sgn spine2

apply_exp sub1 one_lam_f1

apply_spine sub1 Nil

let RetExp tmp = apply_var sub1 1

print_exp sgn tmp

print_exp sgn one_lam_f1
print_sub sgn sub1




  and focus sgn ctx Nil E = E
    | focus sgn ctx (App(M,S)) (Pi {arg=A1,body=A2,...}) =
      (check_exp sgn ctx M A1;
       focus sgn ctx S (apply_exp (Dot(M,id_sub)) A2))
    | focus _ _ S E = raise Fail_spine_exp("focus: bad case",S,E)


focus sgn ctx' one tm_tm_tm


check_exp sgn ctx' two_one tm_exp

focus sgn ctx' one_sp tm_tm_tm


check_exp sgn ctx' one tm_tm

focus sgn ctx' Nil tm_tm



print (exp_to_string sgn tm_tm_tm)




let tbug = L.the (Lib.find (get "bug") cs);
let S.Decl sbug = Translate.translate_condec (~1,tbug);
let decl = sbug;











check sgn (#exp decl) (Uni (#uni decl))

let (U1,V1) = (#exp decl,Uni (#uni decl))
let ctx = C.empty
check_exp sgn C.empty U1 V1
let (Pi {var,arg=A1,body=A2,...},uni as Uni _) = (U1,V1)
let ctx = (C.push ctx (var,A1))
let (Root(Const con,S),V) = (A2,uni)

let rec foc exp =
    let
      let U = focus sgn ctx S exp
    in
      if equiv_exp sgn U V then ()
      else raise Fail_exp2 ("check_exp:0",U,V)
    end

in

let Decl decl = Sig.lookup sgn con
foc (#exp decl)

        case Sig.lookup sgn con of
           Decl decl => foc (#exp decl) 
         | Def def => foc (#exp def)
         | Abbrev abbrev => raise Fail "check_exp:1"
      end

let exp = #exp decl




let it =
  ("focus: bad case",Nil,
   Pi {arg=Root (Const 0,Nil),body=Root (Const 0,Nil),depend=No,var=NONE})
  : string * SpineLF.spine * SpineLF.exp


(* -------------------------------------------------------------------------- *)
(*  Timing                                                                    *)
(* -------------------------------------------------------------------------- *)

Twelf.Timers.reset()
Twelf.Print.depth := SOME 0
Twelf.Print.length := SOME 0
Twelf.Print.depth := NONE
Twelf.Print.length := NONE 
Twelf.Timers.show()
(Translate.translate_signature();raise Success)

let center = Timing.newCenter "checker"
Debug.disable_printing()
Timing.time center Translate.translate_signature ()
1;
Timing.toString center

(* ========================================================================== *)
(*  Junk                                                                      *)
(* ========================================================================== *)


Debug.disable_printing()
Debug.enable_printing()
let sgn = 

let it =
  ("focus: bad case",Nil,
   Pi {arg=Root (Const 212,Nil),body=Root (Const 212,Nil),depend=No,var=NONE})
  : string * SpineLF.spine * SpineLF.exp


- let it = (211,"etp") : IntSyn.cid * string
- let it = (212,"eterm") : IntSyn.cid * string
- let it = (541,"eterm-eq/i") : IntSyn.cid * string
- let it = (543,"etp-eq/i") : IntSyn.cid * string
- let it = (591,"eterm-resp-bind") : IntSyn.cid * string
let hsp = (S.check sgn (#exp decl) (S.Uni (#uni decl));raise Success)
  handle S.Fail_spine_exp x => x



name 0;

handle Translate.Trans1 x => x
     | Translate.Fail3 x => x

let s = SpineLF.Sgn.array sgn;

(* -------------------------------------------------------------------------- *)
(*  Debug                                                                     *)
(* -------------------------------------------------------------------------- *)




let tbug = L.the (Lib.find (get "bug") cds')
let S.Decl sbug = Translate.translate_condec (432,tbug)
let decl = sbug

D.enable_printing()

let hsp = (S.check sgn (#exp decl) (S.Uni (#uni decl));raise Success)
  handle S.Fail_hd_spine x => x

let (ctx,E1,E2) = (C.empty,#exp decl,S.Uni (#uni decl))

S.check_exp sgn C.empty E1 E2

let rec check sgn E1 E2 = check_exp sgn C.empty E1 E2

name 211
name 212
name 541
name 543
name 591







S.check 



Control.Print.printDepth := 40



name 85
name 90
name 431


name 2
name 42


module C = ClausePrint
module Ctx = Context
let sgn = Sgn.empty
let dec0 = T.translate_condec (0,(L.ith 0 cs))
let sgn0 = Sgn.insert sgn dec0
let dec1 = T.translate_condec (1,(L.ith 1 cs))
let sgn1 = Sgn.insert sgn0 dec1
let dec2 = T.translate_condec (2,(L.ith 2 cs))
let sgn2 = Sgn.insert sgn1 dec2
let dec3 = T.translate_condec (3,(L.ith 3 cs))
let sgn3 = Sgn.insert sgn2 dec3
let dec4 = T.translate_condec (4,(L.ith 4 cs))
let sgn4 = (Sgn.insert sgn3 dec4;raise Fail "success")
  handle S.Check s => (print s;raise Fail "")
       | S.Fail2(s,v1,v2) => (s,v1,v2)


open S


let tm = (ExpLam
              (ExpApp
                 (HdConst 3,
                  SpCons
                    (ExpApp (HdVar 1,SpNil),
                     SpCons
                       (ExpApp (HdVar 1,SpNil),
                        SpCons (ExpLam (ExpApp (HdVar 1,SpNil)),SpNil))))))

let ty = ExpPi
           (ExpApp (HdConst 0,SpNil),
            ExpApp
              (HdConst 2,
               SpCons
                 (ExpApp
                    (HdConst 1,
                     SpCons
                       (ExpApp (HdVar 1,SpNil),
                        SpCons (ExpApp (HdVar 1,SpNil),SpNil))),SpNil)))

exception Success
(* -------------------------------------------------------------------------- *)

let ctx = C.empty
let sgn = sgn3
let M = tm
let A = ty

(* -------------------------------------------------------------------------- *)

let (ExpLam M,ExpPi(A1,A2)) = (M,A)
let ctx = (C.push ctx A1) 
check' sgn ctx M A2
  handle Check s => (print s;raise Fail "")

(* -------------------------------------------------------------------------- *)

let ExpApp(HdConst con,S) = M
let SOME (Dec decl) = Sig.lookup sgn con 
focus sgn ctx S (#exp decl) 
  handle Check s => (print s;raise Fail "")

(* -------------------------------------------------------------------------- *)

let A = #exp decl
let (SpCons(M,S),ExpPi(A1,A2)) = (S,A)
check' sgn ctx M A1
focus sgn ctx S (apply_exp (SubCons(M,SubId)) A2)
  handle Check s => (print s;raise Fail "")

(* -------------------------------------------------------------------------- *)


let A = (apply_exp (SubCons(M,SubId)) A2)
let (SpCons(M,S),ExpPi(A1,A2)) = (S,A)
check' sgn ctx M A1
(focus sgn ctx S (apply_exp (SubCons(M,SubId)) A2);raise Success)
  handle S.Fail2(s,v1,v2) => (s,v1,v2)

(* -------------------------------------------------------------------------- *)

let A = (apply_exp (SubCons(M,SubId)) A2)
let (SpCons(M,S),ExpPi(A1,A2)) = (S,A)
check' sgn ctx M A1
focus sgn ctx S (apply_exp (SubCons(M,SubId)) A2)
  handle Check s => (print s;raise Fail "")

let tm1 = ExpLam (ExpApp (HdVar 1,SpNil)) 
let ty1 = ExpPi
           (ExpApp (HdConst 3,SpCons (ExpApp (HdVar 1,SpNil),SpNil)),
            ExpApp (HdConst 3,SpCons (ExpApp (HdVar 2,SpNil),SpNil)))

let (ExpLam M,ExpPi(A1,A2)) = (tm1,ty1)
check' sgn (C.push ctx A1) M A2

let (ExpApp(HdVar i,S)) = M
let SOME A = C.lookup ctx (i-1)
focus sgn (C.push ctx A1) S A
 A2

check' sgn ctx tm1 ty1


(* -------------------------------------------------------------------------- *)

let A = A2
let (SpCons(M,S),ExpPi(A1,A2)) = (S,A)
check' sgn ctx M A1
focus sgn ctx S (apply_exp (SubCons(M,SubId)) A2)
  handle Check s => (print s;raise Fail "")



check' sgn4 ctx tm ty


check' sgn4 ctx1 M A2
  handle Check s => (print s;raise Fail "")


let (ExpApp(HdConst con,S)) = M
let SOME (Dec decl) = Sig.lookup sgn con

focus sgn ctx S (#exp decl) 
  handle Check s => (print s;raise Fail "")






S.print_exp sgn4 tm

(* -------------------------------------------------------------------------- *)
(*  Junk                                                                      *)
(* -------------------------------------------------------------------------- *)



Twelf.make "../../sources.cfg"; 
exception Success;
(Translate.translate_signature();raise Success)
  handle Translate.Translate s => (print s; raise Fail "")
       | SpineLF.Check s => (print s; raise Fail "")
       | SpineLF.Fail2(s,u1,u2) => (s,u1,u2)


Twelf.make "../../sources.cfg"; 
Translate.translate_signature();
