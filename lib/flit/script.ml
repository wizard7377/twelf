let rec dumpText(tcb, semant, checker, outputSemant, outputChecker) =
    let 
	let _ =	Twelf.reset()
	let _ = Flit.initForText()
	let _ = Twelf.Print.width := Option.valOf Int.maxInt
	let _ = Twelf.Print.implicit := true
	let _ = Twelf.Print.printInfix := true
	let _ = Twelf.Print.noShadow := true
	let _ = Twelf.chatter := 1
	let _ = Twelf.reset();
	let tcbConfig = Twelf.Config.read tcb
	let _ = Twelf.Config.append(tcbConfig)
	let _ = Flit.setEndTcb()
	let semantConfig = Twelf.Config.readWithout (semant, tcbConfig)
	let _ = Twelf.Config.append(semantConfig)
	let _ = Flit.setFlag()
	let _ = Twelf.Config.append(Twelf.Config.read checker)
	let _ = Flit.dumpText (outputSemant, outputChecker)
    in 
    () 
    end;

dumpText("pcc/flit/ltal.cfg",
	 "pcc/ltal/semant.cfg",
	 "pcc/ltal/checker.cfg",
	 "dumpsemant",
	 "dumpchecker");
