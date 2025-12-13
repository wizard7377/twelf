(* GEN BEGIN SIGNATURE DECLARATION *) signature NETSERVER =
sig

    (* int argument is which port number to run on *)

    val flashServer : int -> unit (* Macromedia Flash XMLSocket interface *)
    val humanServer : int -> unit (* Human-readable interface, suitable for telnet *)
    (* second argument is what directory server.html is kept in *)
    val httpServer : int -> string -> unit (* HTTP interface, suitable for javascript XMLHttpRequest *)
    val setExamplesDir : string -> unit (* filesystem directory where twelf examples are kept *)
end (* GEN END SIGNATURE DECLARATION *)  (* signature SERVER *)

functor (* GEN BEGIN FUNCTOR DECL *) NetServer
	    (structure Timing : TIMING
	     structure Twelf : TWELF
	     structure Msg : MSG)
	    :> NETSERVER =
struct

fun (* GEN BEGIN FUN FIRST *) join delim [] = "" (* GEN END FUN FIRST *)
  | (* GEN BEGIN FUN BRANCH *) join delim [x] = x (* GEN END FUN BRANCH *)
  | (* GEN BEGIN FUN BRANCH *) join delim (h::tl) = h ^ delim ^ (join delim tl) (* GEN END FUN BRANCH *)

type server = { send : string -> unit,
		exec : string -> unit }

type protocol = { init: unit -> unit,
		  reset: unit -> unit,
		  recv: server -> string -> unit, 
		  send: server -> string -> unit,
		  done: unit -> unit }

structure S = Socket

(* GEN BEGIN TAG OUTSIDE LET *) val maxConnections = 128 (* GEN END TAG OUTSIDE LET *) (* queue size for waiting connections in listen *)
                         (* below --- set to some arbitrary high value. *)

(* fun loop f state = loop f (f state) *)
fun loop f  = (f (); loop f)

fun vec2str v = String.implode 
		    (map (Char.chr o Word8.toInt)
				    (Word8Vector.foldr op:: nil v))
fun str2vec l = Word8Vector.fromList
			 (map (Word8.fromInt o Char.ord)
			      (String.explode l))

fun fileText fname = 
    let
	(* GEN BEGIN TAG OUTSIDE LET *) val s = TextIO.openIn fname (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val txt = TextIO.inputAll s (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = TextIO.closeIn s (* GEN END TAG OUTSIDE LET *)
    in
	txt
    end

fun fileData fname = 
    let
	(* GEN BEGIN TAG OUTSIDE LET *) val s = BinIO.openIn fname (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val data = BinIO.inputAll s (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = BinIO.closeIn s (* GEN END TAG OUTSIDE LET *)
    in
	vec2str data
    end

exception EOF
exception Quit

fun send conn str = (Compat.SocketIO.sendVec(conn, str2vec str); ())

local
    structure SS = Substring
in
fun parseCmd s = 
    let
	(* GEN BEGIN TAG OUTSIDE LET *) val (c,a) = SS.position " " (Compat.Substring.full s) (* GEN END TAG OUTSIDE LET *)
    in
	(SS.string c, SS.string (SS.dropl Char.isSpace a))
    end
end

fun quote (string) = "`" ^ string ^ "'"

(* GEN BEGIN TAG OUTSIDE LET *) val examplesDir : string option ref = ref NONE (* GEN END TAG OUTSIDE LET *)
fun setExamplesDir s = examplesDir := SOME s

(* exception Error for server errors *)
exception Error of string
fun error (msg) = raise Error(msg)

fun serveExample e =
	if (case e of
		"ccc" => true
	      | "cut-elim" => true
	      | "handbook" => true
	      | "lp-horn" => true
	      | "prop-calc" => true
	      | "units" => true
	      | "church-rosser" => true
	      | "fj" => true
	      | "incll" => true
	      | "mini-ml" => true
	      | "small-step" => true
	      | "alloc-sem" => true
	      | "compile" => true
	      | "fol" => true
	      | "kolm" => true
	      | "modal" => true
	      | "tabled" => true
	      | "arith" => true
	      | "cpsocc" => true
	      | "guide" => true
	      | "lp" => true
	      | "polylam" => true
	      | "tapl-ch13" => true
	      | _ => false)
	then ((OS.FileSys.chDir (Option.valOf(!examplesDir) ^ "/" ^ e); Twelf.make "sources.cfg") 
	      handle e => raise Error ("Exception " ^ exnName e ^ " raised."))
	else (raise Error ("Unknown example " ^ quote e))
	     
(* Natural numbers *)
fun (* GEN BEGIN FUN FIRST *) getNat (t::nil) =
    (Lexer.stringToNat t
     handle Lexer.NotDigit (char) => error (quote t ^ " is not a natural number")) (* GEN END FUN FIRST *)
  | (* GEN BEGIN FUN BRANCH *) getNat (nil) = error "Missing natural number" (* GEN END FUN BRANCH *)
  | (* GEN BEGIN FUN BRANCH *) getNat (ts) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

(* Example specifiers *)
fun (* GEN BEGIN FUN FIRST *) getExample (t::nil) = t (* GEN END FUN FIRST *)
  | (* GEN BEGIN FUN BRANCH *) getExample (nil) = error "Missing example" (* GEN END FUN BRANCH *)
  | (* GEN BEGIN FUN BRANCH *) getExample (ts) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

(* Setting Twelf parameters *)
fun (* GEN BEGIN FUN FIRST *) setParm ("chatter"::ts) = Twelf.chatter := getNat ts (* GEN END FUN FIRST *)
  | (* GEN BEGIN FUN BRANCH *) setParm (t::ts) = error ("Unknown parameter " ^ quote t) (* GEN END FUN BRANCH *)
  | (* GEN BEGIN FUN BRANCH *) setParm (nil) = error ("Missing parameter") (* GEN END FUN BRANCH *)
		    
fun (* GEN BEGIN FUN FIRST *) exec' conn ("quit", args) = (Msg.message "goodbye.\n"; raise Quit) (* GEN END FUN FIRST *)
  | (* GEN BEGIN FUN BRANCH *) exec' conn ("set", args) = (setParm (String.tokens Char.isSpace args); Twelf.OK) (* GEN END FUN BRANCH *) 
  | (* GEN BEGIN FUN BRANCH *) exec' conn ("readDecl", args) = Twelf.loadString args (* GEN END FUN BRANCH *)
  | (* GEN BEGIN FUN BRANCH *) exec' conn ("decl", args) = Twelf.decl args (* GEN END FUN BRANCH *)
  | (* GEN BEGIN FUN BRANCH *) exec' conn ("example", args) = serveExample (getExample (String.tokens Char.isSpace args)) (* GEN END FUN BRANCH *)
  | (* GEN BEGIN FUN BRANCH *) exec' conn (t, args) = raise Error ("Unrecognized command " ^ quote t) (* GEN END FUN BRANCH *)

fun exec conn str = (case exec' conn (parseCmd str) 
			  handle Error s => (Msg.message ("Server Error: " ^ s ^ "\n"); Twelf.ABORT)
		      of
			 Twelf.OK => Msg.message "%%% OK %%%\n"
		       | Twelf.ABORT => Msg.message "%%% ABORT %%%\n")
		    
		    
fun stripcr s = Substring.string (Substring.dropr ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => x = #"\r" (* GEN END FUNCTION EXPRESSION *)) (Compat.Substring.full s))

fun flashProto() = 
    let 
	(* GEN BEGIN TAG OUTSIDE LET *) val buf : string ref = ref "" (* GEN END TAG OUTSIDE LET *)
	fun (* GEN BEGIN FUN FIRST *) isnull #"\000" = true (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) isnull _ = false (* GEN END FUN BRANCH *)
	fun recv (u : server) s = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = buf := !buf ^ s (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (rem::cmds) = rev(String.fields isnull (!buf)) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = app (#exec u) (rev cmds) (* GEN END TAG OUTSIDE LET *)
	    in
		buf := rem
	    end
	fun send (u : server) s = (#send u) (s ^ "\000")
    in
	{
	 init = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>  Msg.message (Twelf.version ^ "\n%%% OK %%%\n") (* GEN END FUNCTION EXPRESSION *)),
	 reset = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => buf := "" (* GEN END FUNCTION EXPRESSION *)),
	 send = send,
	 recv = recv,
	 done = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *))
	 }
    end

fun humanProto() = 
    let 
	(* GEN BEGIN TAG OUTSIDE LET *) val buf : string ref = ref "" (* GEN END TAG OUTSIDE LET *)
	fun (* GEN BEGIN FUN FIRST *) isnewl #"\n" = true (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) isnewl #"\r" = false (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) isnewl _ = false (* GEN END FUN BRANCH *)
	fun recv (u : server) s = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = buf := !buf ^ s (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (rem::cmds) = rev(String.fields isnewl (!buf)) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = app (#exec u) (map stripcr (rev cmds)) (* GEN END TAG OUTSIDE LET *)
	    in
		buf := rem
	    end
	fun send (u : server) s = (#send u) ("> " ^ s)
    in
	{
	 init = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>  Msg.message (Twelf.version ^ "\n%%% OK %%%\n") (* GEN END FUNCTION EXPRESSION *)),
	 reset = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => buf := "" (* GEN END FUNCTION EXPRESSION *)),
	 send = send,
	 recv = recv,
	 done = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *))
	 }
    end

fun httpProto dir =
    let 
	(* GEN BEGIN TAG OUTSIDE LET *) val ibuf : string ref = ref "" (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val obuf : string ref = ref "" (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val parsingHeaders = ref true (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val contentLength = ref 0 (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val method : string ref = ref "" (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val url : string ref = ref "" (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val headers : string list ref = ref [] (* GEN END TAG OUTSIDE LET *)
	fun (* GEN BEGIN FUN FIRST *) isnewl #"\n" = true (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) isnewl _ = false (* GEN END FUN BRANCH *)

	fun handlePostRequest (u : server) =
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val shouldQuit = ((#exec u) (!ibuf); false) handle Quit => true (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val response = !obuf (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val clmsg = "Content-Length: " ^ Int.toString (size response) ^ "\n" (* GEN END TAG OUTSIDE LET *)
	    in
		#send u ("HTTP/1.1 200 OK\nContent-Type: text/plain\n" ^ clmsg ^ "\n");
		#send u response;
		if shouldQuit then raise Quit else raise EOF
	    end 
	fun handleGetRequest (u : server) =
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val ok = "200 OK" (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val missing = "404 Not Found" (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val (content, ctype, rcode) = (case !url of
                             "/" => (fileText (dir ^ "/server.html"), "application/xhtml+xml", ok)
			   | "/server.js" => (fileText (dir ^ "/server.js"), "text/plain", ok)
			   | "/server.css" => (fileText (dir ^ "/server.css"), "text/css", ok)
			   | "/grad.png" => (fileData (dir ^ "/grad.png"), "image/png", ok)
			   | "/twelfguy.png" => (fileData (dir ^ "/twelfguy.png"), "image/png", ok)
			   | "/input.png" => (fileData (dir ^ "/input.png"), "image/png", ok)
			   | "/output.png" => (fileData (dir ^ "/output.png"), "image/png", ok)
			   | "/floral.png" => (fileData (dir ^ "/floral.png"), "image/png", ok)
			   | _ => ("Error 404", "text/plain", missing)) (* GEN END TAG OUTSIDE LET *)
					      
		(* GEN BEGIN TAG OUTSIDE LET *) val clmsg = "Content-Length: " ^ Int.toString (size content) ^ "\r\n" (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val ctmsg = "Content-Type: " ^ ctype ^ "\r\n" (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val resp = "HTTP/1.1 " ^ rcode ^ "\r\n" (* GEN END TAG OUTSIDE LET *)
	    in
		#send u (resp ^ ctmsg  ^ clmsg ^ "\r\n");
		#send u content;
		raise EOF;
		()
	    end 
	fun handleRequest (u : server) = 
	    if !method = "GET" then handleGetRequest u
	    else if !method = "POST" then handlePostRequest u
	    else #send u "HTTP/1.1 500 Server Error\n\n"
	fun headerExec s = headers := (s :: !headers)
	fun recvContent u = (if (size (!ibuf) >= !contentLength) then handleRequest u else ())
	fun parseHeaders() = 
	    (let
		 (* GEN BEGIN TAG OUTSIDE LET *) val (request::headers) = rev (!headers) (* GEN END TAG OUTSIDE LET *)
		 (* GEN BEGIN TAG OUTSIDE LET *) val [m, u, httpVersion] = String.tokens ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => x = #" " (* GEN END FUNCTION EXPRESSION *)) request (* GEN END TAG OUTSIDE LET *)
		 (* GEN BEGIN TAG OUTSIDE LET *) val _ = method := m (* GEN END TAG OUTSIDE LET *)
		 (* GEN BEGIN TAG OUTSIDE LET *) val _ = url := u (* GEN END TAG OUTSIDE LET *)
		 fun getField s = 
		     let
			 (* GEN BEGIN TAG OUTSIDE LET *) val (k::v) = String.fields ((* GEN BEGIN FUNCTION EXPRESSION *) fn x => x = #":" (* GEN END FUNCTION EXPRESSION *)) s (* GEN END TAG OUTSIDE LET *)
			 (* GEN BEGIN TAG OUTSIDE LET *) val v = join ":" v (* GEN END TAG OUTSIDE LET *)
		     in
			 (k, substring(v, 1, (size v) - 1)) end
		 fun proc_one s = 
		     let
			 (* GEN BEGIN TAG OUTSIDE LET *) val (k, v) = getField s (* GEN END TAG OUTSIDE LET *) 
		     in 
			 if k = "Content-Length" then contentLength := (case Int.fromString v of NONE => 0 | SOME n => n) else ()
		     end
		 (* GEN BEGIN TAG OUTSIDE LET *) val () = app proc_one headers (* GEN END TAG OUTSIDE LET *)
	     in
		 parsingHeaders := false
	     end handle Bind => raise EOF)
		
	fun (* GEN BEGIN FUN FIRST *) interp (u : server) [] = raise Match (* GEN END FUN FIRST *)
	  | (* GEN BEGIN FUN BRANCH *) interp u [x] = ibuf := x (* GEN END FUN BRANCH *)
	  | (* GEN BEGIN FUN BRANCH *) interp u (h::tl) = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val sch = stripcr h (* GEN END TAG OUTSIDE LET *)
	    in
		if sch = "" 
		then (ibuf := join "\n" tl; parseHeaders(); recvContent u)
		else (headerExec (stripcr h); interp u tl)
	    end (* GEN END FUN BRANCH *)
	fun recv (u : server) s = 
	    (ibuf := !ibuf ^ s;
	     if !parsingHeaders 
	     then interp u (String.fields isnewl (!ibuf))
	     else recvContent u)
	fun send (u : server) s = obuf := !obuf ^ s
	fun reset () = (parsingHeaders := true; ibuf := ""; obuf := ""; contentLength := 0; headers := []; url := ""; method := "")
    in
	{
	 init = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *)),
	 reset = reset,
	 send = send,
	 recv = recv,
	 done = ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => () (* GEN END FUNCTION EXPRESSION *))
	 }
    end

fun protoServer (proto : protocol) portNum =
    let
	(* GEN BEGIN TAG OUTSIDE LET *) val sock = INetSock.TCP.socket() (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = S.Ctl.setREUSEADDR (sock, true) (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = S.bind (sock, INetSock.any portNum) (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = S.listen (sock, maxConnections) (* GEN END TAG OUTSIDE LET *)

	fun read_one conn u () =
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val v = S.recvVec(conn, 1024) (* GEN END TAG OUTSIDE LET *) (* arbitrary buffer size *)
	    in
		if Word8Vector.length v = 0 
		then raise EOF
		else (#recv proto) u (vec2str v)
	    end
	fun accept_one () = 
	    let
		(* GEN BEGIN TAG OUTSIDE LET *) val (conn, addr) = S.accept sock (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = (#reset proto) () (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val u = {send = send conn, exec = exec conn} (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = Msg.setMessageFunc ((#send proto) u) (* GEN END TAG OUTSIDE LET *)
		(* GEN BEGIN TAG OUTSIDE LET *) val _ = (#init proto) () (* GEN END TAG OUTSIDE LET *)
	    in
		loop (read_one conn u) handle EOF => ((#done proto)(); S.close conn)
					    | Quit => ((#done proto)(); S.close conn; raise Quit)
	    end
    in
	loop accept_one handle Quit => S.close sock
    end

fun flashServer port = protoServer (flashProto()) port
fun humanServer port = protoServer (humanProto()) port
fun httpServer port dir = protoServer (httpProto dir) port

end (* GEN END FUNCTOR DECL *)

structure NetServer =
NetServer (structure Timing = Timing
	   structure Twelf = Twelf
	   structure Msg = Msg);

