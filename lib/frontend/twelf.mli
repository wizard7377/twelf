(* Front End Interface *) 
(* Author: Frank Pfenning *)

module type TWELF =
sig
  module Print :
  sig
    val implicit : bool ref	       (* false, print implicit args *)
    val printInfix : bool ref	       (* false, print fully explicit form infix when possible *)
    val depth : int option ref	       (* NONE, limit print depth *)
    val length : int option ref	       (* NONE, limit argument length *)
    val indent : int ref	       (* 3, indentation of subterms *)
    val width : int ref		       (* 80, line width *)
    val noShadow : bool ref	       (* if true, don't print shadowed constants as "%const%" *)

    val sgn : unit -> unit	       (* print module type *)
    val prog : unit -> unit	       (* print module type as program *)
    val subord : unit -> unit	       (* print subordination relation *)
    val def : unit -> unit	       (* print information about definitions *)
    val domains : unit -> unit         (* print available constraint domains *)

    module TeX :		       (* print in TeX format *)
    sig
      val sgn : unit -> unit	       (* print module type *)
      val prog : unit -> unit	       (* print module type as program *)
    end
  end

  module Trace :
  sig 
    type 'a Spec =		       (* trace and breakpoint spec *)
      None			       (* no tracing, default *)
    | Some of 'a list		       (* list of clauses and families *)
    | All			       (* trace all clauses and families *)

    val trace : string Spec -> unit    (* trace clauses and families *)
    val break : string Spec -> unit    (* break at clauses and families *)
    val detail : int ref	       (* 0 = none, 1 = default, 2 = unify *)

    val show : unit -> unit	       (* show trace, break, and detail *)
    val reset : unit -> unit	       (* reset trace, break, and detail *)
  end

  module Table :
  sig
    type strategy = Variant | Subsumption  (* Variant | Subsumption *)

    val strategy : strategy ref	      (* strategy used for %querytabled *)
    val strengthen : bool ref	      (* strengthenng used %querytabled *)
    val resetGlobalTable : unit -> unit (* reset global table           *)

  val top : unit -> unit    (* top-level for interactive tabled queries *)
  end

  module Timers :
  sig
    val show : unit -> unit	       (* show and reset timers *)
    val reset : unit -> unit	       (* reset timers *)
    val check : unit -> unit	       (* display, but not no reset *)
  end

  module OS :
  sig
    val chDir : string -> unit	       (* change working directory *)
    val getDir : unit -> string	       (* get working directory *)
    val exit : unit -> unit	       (* exit Twelf and ML *)
  end

  module Compile :
  sig
    type opt = No | LinearHeads | Indexing 
    val optimize : opt ref
  end

  module Recon :
  sig
    type tracemode = Progressive | Omniscient
    val trace : bool ref
    val traceMode : tracemode ref
  end

  module Prover :
  sig
    type strategy = RFS | FRS      (* F=Filling, R=Recursion, S=Splitting *)
    val strategy : strategy ref	       (* FRS, strategy used for %prove *)
    val maxSplit : int ref	       (* 2, bound on splitting  *)
    val maxRecurse : int ref	       (* 10, bound on recursion *)
  end

  val chatter : int ref		             (* 3, chatter level *)
  val doubleCheck : bool ref	             (* false, check after reconstruction *)
  val unsafe : bool ref		             (* false, allows %assert *)
  val autoFreeze : bool ref		(* false, freezes families in meta-theorems *)
  val timeLimit : (Time.time option) ref     (* NONEe, allows timeLimit in seconds *)

  type status = OK | ABORT	       (* return status *)

  val reset : unit -> unit	       (* reset global module type *)
  val loadFile : string -> status      (* load file *)
  val loadString : string -> status    (* load string *)
  val readDecl : unit -> status	       (* read declaration interactively *)
  val decl : string -> status	       (* print declaration of constant *)

  val top : unit -> unit	       (* top-level for interactive queries *)

  module Config :
  sig
    type config			       (* configuration *)
    val suffix : string ref            (* suffix of configuration files *)
    val read : string -> config	       (* read config file *)
    val readWithout : string * config -> config 
                                       (* read config file, minus contents of another *)
    val load : config -> status	       (* reset and load configuration *)
    val append : config -> status      (* load configuration (w/o reset) *)
    val define : string list -> config (* explicitly define configuration *)
  end

  val make : string -> status	       (* read and load configuration *)

  val version : string		       (* Twelf version *)

end;; (* module type TWELF *)
