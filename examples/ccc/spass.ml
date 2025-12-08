(*
  A simple traverser to generate input for the SPASS prover.
  Author: Frank Pfenning

Sample Session:

% cd /afs/cs/project/twelf/research/twelf/
% sml-cm
- CM.make ();
- use "examples/ccc/spass.sml";

This will print the SPASS representation for a bunch of axioms and theorems
of cartesian closed categories.  The encoding maps any morphism f : A -> B
(even compound ones) to the term mor(f,A,B) to guarantee type safety.

See

  spass.elf

for the definitions and status of various declarations.  Information on
the proofs can be found in pf.dvi (written by Andrzej Filinski) and
the other .elf files.
*)

(Spass : TRAVERSE)R =
struct

  type tp =
    QFProp of string			(* Quantifier-free proposition *)
  | Prop of string * string		(* Proposition ("xs", "A") *)
  | Mor of string			(* Morphism "A,B" *)
  | Obj					(* Object "A" *)
  | What of string			(* What "?error?" *)

  type obj = string

  type head = string
  type spine = string option

  type dec = string

  type condec = string

  fun par (s) = "(" ^ s ^ ")"

  (* types *)
  let rec atom = function (" -> =", SOME(S)) = QFProp ("equal" ^ par (S))
    (* | atom ("mor", SOME(S)) = Mor ("arrow" ^ par (S)) *)
    | ("mor", SOME(S)) -> Mor (S)
    | ("obj", NONE) -> Obj
    | _ -> What "?atom?"

  let rec arrow = function (QFProp(A1), QFProp(A2)) -> 
        QFProp ("implies" ^ par (A1 ^ ", " ^ A2))	(* ?? *)
    | _ -> What "?arrow?"

  let rec pi = function (x, Prop(xs,A)) -> Prop (xs ^ "," ^ x, A)
    | (x, QFProp (A)) -> Prop (x, "and" ^ par (A))
    | _ -> What "?pi?"

  (* terms *)
  fun mor (f, A) = "mor" ^ par (f ^ "," ^ A)

  let rec root = function ("id", NONE, Mor (A)) -> mor ("id", A)	(* constants *)
    | ("@", SOME(S), Mor(A)) -> mor ("comp" ^ par (S), A)
    | ("1", NONE, Obj) -> "one"
    | ("*", SOME(S), Obj) -> "prod" ^ par(S)
    | ("drop", NONE, Mor(A)) -> mor ("drop", A)
    | ("fst", NONE, Mor(A)) -> mor ("fst", A)
    | ("snd", NONE, Mor(A)) -> mor ("snd", A)
    | ("pair", SOME(S), Mor(A)) -> mor ("pair" ^ par (S), A)
    | (" -> >", SOME(S), Obj) = "func" ^ par(S)
    | ("app", NONE, Mor(A)) -> mor ("app", A)
    | ("cur", SOME(S), Mor(A)) -> mor ("cur" ^ par (S), A)
    | (x, NONE, Obj) -> x		(* object variables *)
    | (x, NONE, Mor(A)) -> mor (x, A) (* morphism variables *)
    | _ -> "?root?"

  fun lam _ = "?lam?"

  fun bvar (x) = x
  fun const (c) = c
  fun def (d) = d

  let nils = NONE
  let rec app = function (M, NONE) -> SOME(M)
    | (M, SOME(S)) -> SOME(M ^ "," ^ S)

  (* declarations *)

  fun dec (x, A) = x

  let rec objdec = function (c, Prop(xs,A)) -> 
      "%% " ^ c ^ " :\n"
      ^ "formula" ^ par ("forall" ^ par("[" ^ xs ^ "],\n"
      ^ A)) ^ ".\n"
    | (c, QFProp(A)) -> 
      "%% " ^ c ^ " :\n"
      ^ "formula" ^ par ("and" ^ par(A)) ^ ".\n"
    | (c, _) -> "%% " ^ c ^ " : skipped.\n"

end;; (* module Spass *)

module Spass =
  Traverse (module IntSyn' = IntSyn
	    module Whnf = Whnf
	    module Names = Names
	    module Traverser' = Spass);


Twelf.Config.load (Twelf.Config.read "examples/ccc/spass.cfg");

let rec ccc (c) = (print (Spass.const (c)); print "\n");

(
(* Equality *)
(* refl, then, sym *)

(* identity and composition *)
(* =@= *)
ccc "id_l";
ccc "id_r";
ccc "ass";

(* products *)
(* =pair= *)
ccc "term_u";
ccc "prod_l";
ccc "prod_r";
ccc "prod_u";

(* exponentials *)
(* =cur= *)
ccc "exp_e";
ccc "exp_u";

(* lemmas *)
ccc "distp";
ccc "appl";
ccc "distc";
()
);
