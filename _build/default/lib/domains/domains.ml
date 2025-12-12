structure Integers = Integers(IntInf);

structure Rationals = Rationals(Integers);

structure IntegersMod7 = IntegersMod((* GEN BEGIN TAG INSIDE LET *) val p = 7 (* GEN END TAG INSIDE LET *));

