open StreamIO
module type IMPERATIVEIO = sig
    module StreamIO : STREAMIO
    type vector = StreamIO.vector
    type elem = StreamIO.elem

    type instream
    type outstream

    val input : instream -> vector
    val input1 : instream -> elem option
    val inputN : instream * int -> vector
    val inputAll : instream -> vector
    val canInput : instream * int -> int option
    val lookahead : instream -> elem option
    val closeIn : instream -> unit
    val endOfStream : instream -> bool

    val output : outstream * vector -> unit
    val output1 : outstream * elem -> unit
    val flushOut : outstream -> unit
    val closeOut : outstream -> unit

    val mkInstream : StreamIO.instream -> instream
    val getInstream : instream -> StreamIO.instream
    val setInstream : instream * StreamIO.instream -> unit

    val mkOutstream : StreamIO.outstream -> outstream
    val getOutstream : outstream -> StreamIO.outstream
    val setOutstream : outstream * StreamIO.outstream -> unit
    val getPosOut : outstream -> StreamIO.out_pos
    val setPosOut : outstream * StreamIO.out_pos -> unit


end

module Make_ImperativeIO (StreamIO : STREAMIO): IMPERATIVEIO = struct
    module StreamIO = StreamIO
    type vector = StreamIO.vector
    type elem = StreamIO.elem

    type instream
    type outstream

    let input : instream -> vector = assert false (* TODO *)
    let input1 : instream -> elem option = assert false (* TODO*)
    let inputN : instream * int -> vector = assert false (* TODO*)
    let inputAll : instream -> vector = assert false (* TODO*)
    let canInput : instream * int -> int option = assert false (* TODO*)
    let lookahead : instream -> elem option = assert false (* TODO*)
    let closeIn : instream -> unit = assert false (* TODO*)
    let endOfStream : instream -> bool = assert false (* TODO*)

    let output : outstream * vector -> unit = assert false (* TODO*)
    let output1 : outstream * elem -> unit = assert false (* TODO*)
    let flushOut : outstream -> unit = assert false (* TODO*)
    let closeOut : outstream -> unit = assert false (* TODO*)

    let mkInstream : StreamIO.instream -> instream = assert false (* TODO*)
    let getInstream : instream -> StreamIO.instream = assert false (* TODO*)
    let setInstream : instream * StreamIO.instream -> unit = assert false (* TODO*)

    let mkOutstream : StreamIO.outstream -> outstream = assert false (* TODO*)
    let getOutstream : outstream -> StreamIO.outstream = assert false (* TODO*)
    let setOutstream : outstream * StreamIO.outstream -> unit = assert false (* TODO*)
    let getPosOut : outstream -> StreamIO.out_pos = assert false (* TODO*)
    let setPosOut : outstream * StreamIO.out_pos -> unit = assert false (* TODO*)


end
