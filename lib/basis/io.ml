(** IO module - SML Basis Library IO signature *)

module type IO = sig
  exception Io of {name : string; function : string; cause : exn}
  exception BlockingNotSupported
  exception NonblockingNotSupported
  exception RandomAccessNotSupported
  exception TerminatedStream
  exception ClosedStream

  type buffer_mode = NO_BUF | LINE_BUF | BLOCK_BUF
end

module IO : IO = struct
  exception Io of {name : string; function : string; cause : exn}
  exception BlockingNotSupported
  exception NonblockingNotSupported
  exception RandomAccessNotSupported
  exception TerminatedStream
  exception ClosedStream

  type buffer_mode = NO_BUF | LINE_BUF | BLOCK_BUF
end
