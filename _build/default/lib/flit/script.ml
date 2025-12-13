fun dumpText(tcb, semant, checker, outputSemant, outputChecker) =
    let 
	(* GEN BEGIN TAG OUTSIDE LET *) val _ =	Twelf.reset() (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Flit.initForText() (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.Print.width := Option.valOf Int.maxInt (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.Print.implicit := true (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.Print.printInfix := true (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.Print.noShadow := true (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.chatter := 1 (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.reset() (* GEN END TAG OUTSIDE LET *);
	(* GEN BEGIN TAG OUTSIDE LET *) val tcbConfig = Twelf.Config.read tcb (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.Config.append(tcbConfig) (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Flit.setEndTcb() (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val semantConfig = Twelf.Config.readWithout (semant, tcbConfig) (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.Config.append(semantConfig) (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Flit.setFlag() (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Twelf.Config.append(Twelf.Config.read checker) (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val _ = Flit.dumpText (outputSemant, outputChecker) (* GEN END TAG OUTSIDE LET *)
    in 
    () 
    end;

dumpText("pcc/flit/ltal.cfg",
	 "pcc/ltal/semant.cfg",
	 "pcc/ltal/checker.cfg",
	 "dumpsemant",
	 "dumpchecker");
