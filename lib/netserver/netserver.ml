module type NETSERVER = sig
(* int argument is which port number to run on *)
  val flashServer : int -> unit
(* Macromedia Flash XMLSocket interface *)
  val humanServer : int -> unit
(* Human-readable interface, suitable for_sml telnet *)
(* second argument is what directory server.html is kept in *)
  val httpServer : int -> string -> unit
(* HTTP interface, suitable for_sml javascript XMLHttpRequest *)
  val setExamplesDir : string -> unit
(* filesystem directory where twelf examples are kept *)

end

(* signature SERVER *)


module NetServer (Timing : TIMING) (Twelf : TWELF) (Msg : MSG) : NETSERVER = struct let rec join = function (delim, []) -> "" | (delim, [x]) -> x | (delim, (h :: tl)) -> h ^ delim ^ (join delim tl)
type server = <send: string -> unit; exec: string -> unit>
type protocol = <init: unit -> unit; reset: unit -> unit; recv: server -> string -> unit; send: server -> string -> unit; done_: unit -> unit>
module S = Socket
let maxConnections = 128
(* queue size for_sml waiting connections in listen *)

(* below --- set to some arbitrary high value. *)

(* fun loop f state = loop f (f state) *)

let rec loop f  = (f (); loop f)
let rec vec2str v  = String.implode (map (Char.chr o Word8.toInt) (Word8Vector.foldr :: [] v))
let rec str2vec l  = Word8Vector.fromList (map (Word8.fromInt o Char.ord) (String.explode l))
let rec fileText fname  = ( let s = TextIO.openIn fname in let txt = TextIO.inputAll s in let _ = TextIO.closeIn s in  txt )
let rec fileData fname  = ( let s = BinIO.openIn fname in let data = BinIO.inputAll s in let _ = BinIO.closeIn s in  vec2str data )
exception EOF
exception Quit
let rec send conn str  = (Compat.SocketIO.sendVec (conn, str2vec str); ())
module SS = Substring
let rec parseCmd s  = ( let (c, a) = SS.position " " (Compat.Substring.full s) in  (SS.string c, SS.string (SS.dropl Char.isSpace a)) )
let rec quote (string)  = "`" ^ string ^ "'"
let examplesDir : string option ref = ref None
let rec setExamplesDir s  = examplesDir := Some s
(* exception Error for_sml server errors *)

exception Error of string
let rec error (msg)  = raise (Error (msg))
let rec serveExample e  = if (match e with "ccc" -> true | "cut-elim" -> true | "handbook" -> true | "lp-horn" -> true | "prop-calc" -> true | "units" -> true | "church-rosser" -> true | "fj" -> true | "incll" -> true | "mini-ml" -> true | "small-step" -> true | "alloc-sem" -> true | "compile" -> true | "fol" -> true | "kolm" -> true | "modal" -> true | "tabled" -> true | "arith" -> true | "cpsocc" -> true | "guide" -> true | "lp" -> true | "polylam" -> true | "tapl-ch13" -> true | _ -> false) then (try (OS.FileSys.chDir (Option.valOf (! examplesDir) ^ "/" ^ e); Twelf.make "sources.cfg") with e -> raise (Error ("Exception " ^ exnName e ^ " raised."))) else (raise (Error ("Unknown example " ^ quote e)))
(* Natural numbers *)

let rec getNat = function (t :: []) -> (try Lexer.stringToNat t with Lexer.NotDigit (char) -> error (quote t ^ " is not a natural number")) | ([]) -> error "Missing natural number" | (ts) -> error "Extraneous arguments"
(* Example specifiers *)

let rec getExample = function (t :: []) -> t | ([]) -> error "Missing example" | (ts) -> error "Extraneous arguments"
(* Setting Twelf parameters *)

let rec setParm = function ("chatter" :: ts) -> Twelf.chatter := getNat ts | (t :: ts) -> error ("Unknown parameter " ^ quote t) | ([]) -> error ("Missing parameter")
let rec exec' = function (conn, ("quit", args)) -> (Msg.message "goodbye.\n"; raise (Quit)) | (conn, ("set", args)) -> (setParm (String.tokens Char.isSpace args); Twelf.OK) | (conn, ("readDecl", args)) -> Twelf.loadString args | (conn, ("decl", args)) -> Twelf.decl args | (conn, ("example", args)) -> serveExample (getExample (String.tokens Char.isSpace args)) | (conn, (t, args)) -> raise (Error ("Unrecognized command " ^ quote t))
let rec exec conn str  = (match try exec' conn (parseCmd str) with Error s -> (Msg.message ("Server Error: " ^ s ^ "\n"); Twelf.ABORT) with Twelf.OK -> Msg.message "%%% OK %%%\n" | Twelf.ABORT -> Msg.message "%%% ABORT %%%\n")
let rec stripcr s  = Substring.string (Substring.dropr (fun x -> x = '\r') (Compat.Substring.full s))
let rec flashProto ()  = ( let buf : string ref = ref "" in let rec isnull = function '\000' -> true | _ -> false in let rec recv (u : server) s  = ( let _ = buf := ! buf ^ s in let (rem :: cmds) = rev (String.fields isnull (! buf)) in let _ = app (exec u) (rev cmds) in  buf := rem ) in let rec send (u : server) s  = (send u) (s ^ "\000") in  {init = (fun () -> Msg.message (Twelf.version ^ "\n%%% OK %%%\n")); reset = (fun () -> buf := ""); send = send; recv = recv; done_ = (fun () -> ())} )
let rec humanProto ()  = ( let buf : string ref = ref "" in let rec isnewl = function '\n' -> true | '\r' -> false | _ -> false in let rec recv (u : server) s  = ( let _ = buf := ! buf ^ s in let (rem :: cmds) = rev (String.fields isnewl (! buf)) in let _ = app (exec u) (map stripcr (rev cmds)) in  buf := rem ) in let rec send (u : server) s  = (send u) ("> " ^ s) in  {init = (fun () -> Msg.message (Twelf.version ^ "\n%%% OK %%%\n")); reset = (fun () -> buf := ""); send = send; recv = recv; done_ = (fun () -> ())} )
let rec httpProto dir  = ( let ibuf : string ref = ref "" in let obuf : string ref = ref "" in let parsingHeaders = ref true in let contentLength = ref 0 in let method_ : string ref = ref "" in let url : string ref = ref "" in let headers : string list ref = ref [] in let rec isnewl = function '\n' -> true | _ -> false in let rec handlePostRequest (u : server)  = ( let shouldQuit = try ((exec u) (! ibuf); false) with Quit -> true in let response = ! obuf in let clmsg = "Content-Length: " ^ Int.toString (size response) ^ "\n" in  send u ("HTTP/1.1 200 OK\nContent-Type: text/plain\n" ^ clmsg ^ "\n"); send u response; if shouldQuit then raise (Quit) else raise (EOF) ) in let rec handleGetRequest (u : server)  = ( let ok = "200 OK" in let missing = "404 Not Found" in let (content, ctype, rcode) = (match ! url with "/" -> (fileText (dir ^ "/server.html"), "application/xhtml+xml", ok) | "/server.js" -> (fileText (dir ^ "/server.js"), "text/plain", ok) | "/server.css" -> (fileText (dir ^ "/server.css"), "text/css", ok) | "/grad.png" -> (fileData (dir ^ "/grad.png"), "image/png", ok) | "/twelfguy.png" -> (fileData (dir ^ "/twelfguy.png"), "image/png", ok) | "/input.png" -> (fileData (dir ^ "/input.png"), "image/png", ok) | "/output.png" -> (fileData (dir ^ "/output.png"), "image/png", ok) | "/floral.png" -> (fileData (dir ^ "/floral.png"), "image/png", ok) | _ -> ("Error 404", "text/plain", missing)) in let clmsg = "Content-Length: " ^ Int.toString (size content) ^ "\r\n" in let ctmsg = "Content-Type: " ^ ctype ^ "\r\n" in let resp = "HTTP/1.1 " ^ rcode ^ "\r\n" in  send u (resp ^ ctmsg ^ clmsg ^ "\r\n"); send u content; raise (EOF); () ) in let rec handleRequest (u : server)  = if ! method_ = "GET" then handleGetRequest u else if ! method_ = "POST" then handlePostRequest u else send u "HTTP/1.1 500 Server Error\n\n" in let rec headerExec s  = headers := (s :: ! headers) in let rec recvContent u  = (if (size (! ibuf) >= ! contentLength) then handleRequest u else ()) in let rec parseHeaders ()  = (try ( let (request :: headers) = rev (! headers) in let [m; u; httpVersion] = String.tokens (fun x -> x = ' ') request in let _ = method_ := m in let _ = url := u in let rec getField s  = ( let (k :: v) = String.fields (fun x -> x = ':') s in let v = join ":" v in  (k, substring (v, 1, (size v) - 1)) ) in let rec proc_one s  = ( let (k, v) = getField s in  if k = "Content-Length" then contentLength := (match Int.fromString v with None -> 0 | Some n -> n) else () ) in let () = app proc_one headers in  parsingHeaders := false ) with Bind -> raise (EOF)) in let rec interp = function ((u : server), []) -> raise (Match) | (u, [x]) -> ibuf := x | (u, (h :: tl)) -> ( let sch = stripcr h in  if sch = "" then (ibuf := join "\n" tl; parseHeaders (); recvContent u) else (headerExec (stripcr h); interp u tl) ) in let rec recv (u : server) s  = (ibuf := ! ibuf ^ s; if ! parsingHeaders then interp u (String.fields isnewl (! ibuf)) else recvContent u) in let rec send (u : server) s  = obuf := ! obuf ^ s in let rec reset ()  = (parsingHeaders := true; ibuf := ""; obuf := ""; contentLength := 0; headers := []; url := ""; method_ := "") in  {init = (fun () -> ()); reset = reset; send = send; recv = recv; done_ = (fun () -> ())} )
let rec protoServer (proto : protocol) portNum  = ( let sock = INetSock.TCP.socket () in let _ = S.Ctl.setREUSEADDR (sock, true) in let _ = S.bind (sock, INetSock.any portNum) in let _ = S.listen (sock, maxConnections) in let rec read_one conn u ()  = ( (* arbitrary buffer size *)
let v = S.recvVec (conn, 1024) in  if Word8Vector.length v = 0 then raise (EOF) else (recv proto) u (vec2str v) ) in let rec accept_one ()  = ( let (conn, addr) = S.accept sock in let _ = (reset proto) () in let u = {send = send conn; exec = exec conn} in let _ = Msg.setMessageFunc ((send proto) u) in let _ = (init proto) () in  try loop (read_one conn u) with EOF -> ((done_ proto) (); S.close conn) | Quit -> ((done_ proto) (); S.close conn; raise (Quit)) ) in  try loop accept_one with Quit -> S.close sock )
let rec flashServer port  = protoServer (flashProto ()) port
let rec humanServer port  = protoServer (humanProto ()) port
let rec httpServer port dir  = protoServer (httpProto dir) port
 end

module NetServer = NetServer (struct module Timing = Timing end) (struct module Twelf = Twelf end) (struct module Msg = Msg end)

