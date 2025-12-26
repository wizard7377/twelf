(** IO module - SML Basis Library IO signature *)

module type IO = sig
  type io_error = {name : string; function : string; cause : exn}
  exception Io of io_error
  exception BlockingNotSupported
  exception NonblockingNotSupported
  exception RandomAccessNotSupported
  exception TerminatedStream
  exception ClosedStream

  type buffer_mode = NO_BUF | LINE_BUF | BLOCK_BUF
end

module IO : IO = struct
  type io_error = {name : string; function : string; cause : exn}
  exception Io of io_error
  exception BlockingNotSupported
  exception NonblockingNotSupported
  exception RandomAccessNotSupported
  exception TerminatedStream
  exception ClosedStream

  type buffer_mode = NO_BUF | LINE_BUF | BLOCK_BUF
end
