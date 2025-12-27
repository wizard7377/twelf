(* TODO: Figure this out later *)
open StreamIO
open Io

module type TEXTIO = sig
  include STREAMIO with type vector = string and type elem = char

  val openOut : string -> outstream
  val openIn : string -> instream
end

module TextIO : TEXTIO = struct
  type elem = char
  (** {2 StreamIO portion} *)

  type vector = string
  type instream
  type outstream
  type out_pos
  type reader
  type writer
  type pos

  let input : instream -> vector * instream = assert false (* TODO*)
  let input1 : instream -> (elem * instream) option = assert false (* TODO*)
  let inputN : instream * int -> vector * instream = assert false (* TODO*)
  let inputAll : instream -> vector * instream = assert false (* TODO*)
  let canInput : instream * int -> int option = assert false (* TODO*)
  let closeIn : instream -> unit = assert false (* TODO*)
  let endOfStream : instream -> bool = assert false (* TODO*)
  let output : outstream * vector -> unit = assert false (* TODO*)
  let output1 : outstream * elem -> unit = assert false (* TODO*)
  let flushOut : outstream -> unit = assert false (* TODO*)
  let closeOut : outstream -> unit = assert false (* TODO*)
  let mkInstream : reader * vector -> instream = assert false (* TODO*)
  let getReader : instream -> reader * vector = assert false (* TODO*)
  let filePosIn : instream -> pos = assert false (* TODO*)

  let setBufferMode : outstream * IO.buffer_mode -> unit =
    assert false (* TODO*)

  let getBufferMode : outstream -> IO.buffer_mode = assert false (* TODO*)

  let mkOutstream : writer * IO.buffer_mode -> outstream =
    assert false (* TODO*)

  let getWriter : outstream -> writer * IO.buffer_mode = assert false (* TODO*)
  let getPosOut : outstream -> out_pos = assert false (* TODO*)
  let setPosOut : out_pos -> outstream = assert false (* TODO*)
  let filePosOut : out_pos -> pos = assert false (* TODO*)
  let openOut : string -> outstream = assert false (* TODO*)
  let openIn : string -> instream = assert false (* TODO*)
end
