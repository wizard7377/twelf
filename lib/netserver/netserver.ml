module type NETSERVER =
sig

    (* int argument is which port number to run on *)

    let flashServer : int -> unit (* Macromedia Flash XMLSocket interface *)
    let humanServer : int -> unit (* Human-readable interface, suitable for telnet *)
    (* second argument is what directory server.html is kept in *)
    let httpServer : int -> string -> unit (* HTTP interface, suitable for javascript XMLHttpRequest *)
    let setExamplesDir : string -> unit (* filesystem directory where twelf examples are kept *)
end  (* module type SERVER *)

module NetServer
	    (Timing : TIMING)
   (Twelf : TWELF)
   (Msg : MSG)
	    :> NETSERVER =
struct

let rec join delim [] = ""
  | join delim [x] = x
  | join delim (h::tl) = h ^ delim ^ (join delim tl)

type server = { send : string -> unit,
		exec : string -> unit }

type protocol = { init: unit -> unit,
		  reset: unit -> unit,
		  recv: server -> string -> unit, 
		  send: server -> string -> unit,
		  done: unit -> unit }

module S = Socket

let maxConnections = 128 (* queue size for waiting connections in listen *)
                         (* below --- set to some arbitrary high value. *)

(* fun loop f state = loop f (f state) *)
let rec loop f  = (f (); loop f)

let rec vec2str v = String.implode 
		    (map (Char.chr o Word8.toInt)
				    (Word8Vector.foldr op:: nil v))
let rec str2vec l = Word8Vector.fromList
			 (map (Word8.fromInt o Char.ord)
			      (String.explode l))

let rec fileText fname = 
    let
	let s = TextIO.openIn fname
	let txt = TextIO.inputAll s
	let _ = TextIO.closeIn s
    in
	txt
    end

let rec fileData fname = 
    let
	let s = BinIO.openIn fname
	let data = BinIO.inputAll s
	let _ = BinIO.closeIn s
    in
	vec2str data
    end

exception EOF
exception Quit

let rec send conn str = (Compat.SocketIO.sendVec(conn, str2vec str); ())

local
    module SS = Substring
in
let rec parseCmd s = 
    let
	let (c,a) = SS.position " " (Compat.Substring.full s)
    in
	(SS.string c, SS.string (SS.dropl Char.isSpace a))
    end
end

let rec quote (string) = "`" ^ string ^ "'"

let examplesDir : string option ref = ref NONE
let rec setExamplesDir s = examplesDir := SOME s

(* exception Error for server errors *)
exception Error of string
let rec error (msg) = raise Error(msg)

let rec serveExample e =
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
let rec getNat (t::nil) =
    (Lexer.stringToNat t
     handle Lexer.NotDigit (char) => error (quote t ^ " is not a natural number"))
  | getNat (nil) = error "Missing natural number"
  | getNat (ts) = error "Extraneous arguments"

(* Example specifiers *)
let rec getExample (t::nil) = t
  | getExample (nil) = error "Missing example"
  | getExample (ts) = error "Extraneous arguments"

(* Setting Twelf parameters *)
let rec setParm ("chatter"::ts) = Twelf.chatter := getNat ts
  | setParm (t::ts) = error ("Unknown parameter " ^ quote t)
  | setParm (nil) = error ("Missing parameter")
		    
let rec exec' conn ("quit", args) = (Msg.message "goodbye.\n"; raise Quit)
  | exec' conn ("set", args) = (setParm (String.tokens Char.isSpace args); Twelf.OK) 
  | exec' conn ("readDecl", args) = Twelf.loadString args
  | exec' conn ("decl", args) = Twelf.decl args
  | exec' conn ("example", args) = serveExample (getExample (String.tokens Char.isSpace args))
  | exec' conn (t, args) = raise Error ("Unrecognized command " ^ quote t)

let rec exec conn str = (case exec' conn (parseCmd str) 
			  handle Error s => (Msg.message ("Server Error: " ^ s ^ "\n"); Twelf.ABORT)
		      of
			 Twelf.OK => Msg.message "%%% OK %%%\n"
		       | Twelf.ABORT => Msg.message "%%% ABORT %%%\n")
		    
		    
fun stripcr s = Substring.string (Substring.dropr (fun x -> x = #"\r") (Compat.Substring.full s))

let rec flashProto() = 
    let 
	let buf : string ref = ref ""
	let rec isnull = function #"\000" -> true
	  | _ -> false
	let rec recv (u : server) s = 
	    let
		let _ = buf := !buf ^ s
		let (rem::cmds) = rev(String.fields isnull (!buf))
		let _ = app (#exec u) (rev cmds)
	    in
		buf := rem
	    end
	let rec send (u : server) s = (#send u) (s ^ "\000")
    in
	{
	 init = (fn () =>  Msg.message (Twelf.version ^ "\n%%% OK %%%\n")),
	 reset = (fn () => buf := ""),
	 send = send,
	 recv = recv,
	 done = (fn () => ())
	 }
    end

let rec humanProto() = 
    let 
	let buf : string ref = ref ""
	let rec isnewl = function #"\n" -> true
	  | #"\r" -> false
	  | _ -> false
	let rec recv (u : server) s = 
	    let
		let _ = buf := !buf ^ s
		let (rem::cmds) = rev(String.fields isnewl (!buf))
		let _ = app (#exec u) (map stripcr (rev cmds))
	    in
		buf := rem
	    end
	let rec send (u : server) s = (#send u) ("> " ^ s)
    in
	{
	 init = (fn () =>  Msg.message (Twelf.version ^ "\n%%% OK %%%\n")),
	 reset = (fn () => buf := ""),
	 send = send,
	 recv = recv,
	 done = (fn () => ())
	 }
    end

let rec httpProto dir =
    let 
	let ibuf : string ref = ref ""
	let obuf : string ref = ref ""
	let parsingHeaders = ref true
	let contentLength = ref 0
	let method : string ref = ref ""
	let url : string ref = ref ""
	let headers : string list ref = ref []
	let rec isnewl = function #"\n" -> true
	  | _ -> false

	let rec handlePostRequest (u : server) =
	    let
		let shouldQuit = ((#exec u) (!ibuf); false) handle Quit => true
		let response = !obuf
		let clmsg = "Content-Length: " ^ Int.toString (size response) ^ "\n"
	    in
		#send u ("HTTP/1.1 200 OK\nContent-Type: text/plain\n" ^ clmsg ^ "\n");
		#send u response;
		if shouldQuit then raise Quit else raise EOF
	    end 
	let rec handleGetRequest (u : server) =
	    let
		let ok = "200 OK"
		let missing = "404 Not Found"
		let (content, ctype, rcode) = (case !url of
                             "/" => (fileText (dir ^ "/server.html"), "application/xhtml+xml", ok)
			   | "/server.js" => (fileText (dir ^ "/server.js"), "text/plain", ok)
			   | "/server.css" => (fileText (dir ^ "/server.css"), "text/css", ok)
			   | "/grad.png" => (fileData (dir ^ "/grad.png"), "image/png", ok)
			   | "/twelfguy.png" => (fileData (dir ^ "/twelfguy.png"), "image/png", ok)
			   | "/input.png" => (fileData (dir ^ "/input.png"), "image/png", ok)
			   | "/output.png" => (fileData (dir ^ "/output.png"), "image/png", ok)
			   | "/floral.png" => (fileData (dir ^ "/floral.png"), "image/png", ok)
			   | _ => ("Error 404", "text/plain", missing))
					      
		let clmsg = "Content-Length: " ^ Int.toString (size content) ^ "\r\n"
		let ctmsg = "Content-Type: " ^ ctype ^ "\r\n"
		let resp = "HTTP/1.1 " ^ rcode ^ "\r\n"
	    in
		#send u (resp ^ ctmsg  ^ clmsg ^ "\r\n");
		#send u content;
		raise EOF;
		()
	    end 
	let rec handleRequest (u : server) = 
	    if !method = "GET" then handleGetRequest u
	    else if !method = "POST" then handlePostRequest u
	    else #send u "HTTP/1.1 500 Server Error\n\n"
	let rec headerExec s = headers := (s :: !headers)
	let rec recvContent u = (if (size (!ibuf) >= !contentLength) then handleRequest u else ())
	let rec parseHeaders() = 
	    (let
		 let (request::headers) = rev (!headers)
		 let [m, u, httpVersion] = String.tokens (fun x -> x = #" ") request
		 let _ = method := m
		 let _ = url := u
		 let rec getField s = 
		     let
			 let (k::v) = String.fields (fun x -> x = #":") s
			 let v = join ":" v
		     in
			 (k, substring(v, 1, (size v) - 1)) end
		 let rec proc_one s = 
		     let
			 let (k, v) = getField s 
		     in 
			 if k = "Content-Length" then contentLength := (case Int.fromString v of NONE => 0 | SOME n => n) else ()
		     end
		 let () = app proc_one headers
	     in
		 parsingHeaders := false
	     end handle Bind => raise EOF)
		
	let rec interp = function (u : server) [] -> raise Match
	  | u [x] -> ibuf := x
	  | u (h::tl) -> 
	    let
		let sch = stripcr h
	    in
		if sch = "" 
		then (ibuf := join "\n" tl; parseHeaders(); recvContent u)
		else (headerExec (stripcr h); interp u tl)
	    end
	let rec recv (u : server) s = 
	    (ibuf := !ibuf ^ s;
	     if !parsingHeaders 
	     then interp u (String.fields isnewl (!ibuf))
	     else recvContent u)
	let rec send (u : server) s = obuf := !obuf ^ s
	let rec reset () = (parsingHeaders := true; ibuf := ""; obuf := ""; contentLength := 0; headers := []; url := ""; method := "")
    in
	{
	 init = (fn () => ()),
	 reset = reset,
	 send = send,
	 recv = recv,
	 done = (fn () => ())
	 }
    end

let rec protoServer (proto : protocol) portNum =
    let
	let sock = INetSock.TCP.socket()
	let _ = S.Ctl.setREUSEADDR (sock, true)
	let _ = S.bind (sock, INetSock.any portNum)
	let _ = S.listen (sock, maxConnections)

	let rec read_one conn u () =
	    let
		let v = S.recvVec(conn, 1024) (* arbitrary buffer size *)
	    in
		if Word8Vector.length v = 0 
		then raise EOF
		else (#recv proto) u (vec2str v)
	    end
	let rec accept_one () = 
	    let
		let (conn, addr) = S.accept sock
		let _ = (#reset proto) ()
		let u = {send = send conn, exec = exec conn}
		let _ = Msg.setMessageFunc ((#send proto) u)
		let _ = (#init proto) ()
	    in
		loop (read_one conn u) handle EOF => ((#done proto)(); S.close conn)
					    | Quit => ((#done proto)(); S.close conn; raise Quit)
	    end
    in
	loop accept_one handle Quit => S.close sock
    end

let rec flashServer port = protoServer (flashProto()) port
let rec humanServer port = protoServer (humanProto()) port
let rec httpServer port dir = protoServer (httpProto dir) port

end

module NetServer =
NetServer (module Timing = Timing
	   module Twelf = Twelf
	   module Msg = Msg);

