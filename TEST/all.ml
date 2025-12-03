(* (Outdated) Regression test - *)
(* Author: Frank Pfenning *)

(* Twelf.chatter := 0; *)
(* Twelf.chatter := 1; *)
(* Twelf.chatter := 2; *)
(* Twelf.chatter := 5; *)
Twelf.doubleCheck := true;

let rec test (file) =
    case Twelf.make file
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;

let rec testUnsafe (file) = 
    let
       let _ = Twelf.unsafe := true
       let stat = Twelf.make file 
		      handle e => (Twelf.unsafe := false; raise e)
       let _ = Twelf.unsafe := false
    in 
       case stat 
         of Twelf.OK => Twelf.OK
          | Twelf.ABORT => raise Domain
    end;

let rec conclude () = ();

use "TEST/regression.sml";
