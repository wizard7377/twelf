structure Integers = Integers(IntInf);

structure Rationals = Rationals(Integers);

structure IntegersMod7 = IntegersMod((* GEN BEGIN TAG OUTSIDE LET *) val p = 7 (* GEN END TAG OUTSIDE LET *));

