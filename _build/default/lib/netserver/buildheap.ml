NetServer.setExamplesDir "/usr0/stuff/twelf-cvs/examples";
(* GEN BEGIN TAG INSIDE LET *) fun httpServer _ = (NetServer.httpServer 1066 "/usr0/stuff/twelf-cvs/src/netserver/htdocs"; OS.Process.success) (* GEN END TAG INSIDE LET *);
SMLofNJ.exportFn ("netserver.heap", httpServer);