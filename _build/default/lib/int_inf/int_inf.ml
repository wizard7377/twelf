(* int-inf.sml
 *
 * COPYRIGHT (c) 1995 by AT&T Bell Laboratories. See COPYRIGHT file for details.
 *
 * This package is derived from Andrzej Filinski's bignum package.  It is versy
 * close to the definition of the optional IntInf structure in the SML'97 basis.
 * 
 * It is implemented almost totally on the abstraction presented by
 * the BigNat structure. The only concrete type information it assumes 
 * is that BigNat.bignat = 'a list and that BigNat.zero = [].
 * Some trivial additional efficiency could be obtained by assuming that
 * type bignat is really int list, and that if (v : bignat) = [d], then
 * bignat d = [d].
 *
 * At some point, this should be reimplemented to make use of Word32, or
 * have compiler/runtime support.
 *
 * Also, for booting, this module could be broken into one that has
 * all the types and arithmetic functions, but doesn't use NumScan,
 * constructing values from strings using bignum arithmetic. Various
 * integer and word scanning, such as NumScan, could then be constructed 
 * from IntInf. Finally, a user-level IntInf could be built by 
 * importing the basic IntInf, but replacing the scanning functions
 * by more efficient ones based on the functions in NumScan.
 *
 *)

structure IntInf :> INT_INF =
  struct

  (* It is not clear what advantage there is to having NumFormat as
   * a submodule.
   *)

    structure NumScan : sig

        val skipWS : (char, 'a) StringCvt.reader -> 'a -> 'a

        val scanWord : StringCvt.radix
	      ->  (char, 'a) StringCvt.reader
	        -> 'a -> (Word32.word * 'a) option
        val scanInt : StringCvt.radix
	      ->  (char, 'a) StringCvt.reader
	        -> 'a -> (int * 'a) option
	    (** should be to int32 **)

      end = struct

        structure W = Word32
        structure I = Int31
    
        (* GEN BEGIN TAG OUTSIDE LET *) val op <  = W.< (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val op >= = W.>= (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val op +  = W.+ (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val op -  = W.- (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val op *  = W.* (* GEN END TAG OUTSIDE LET *)
    
        (* GEN BEGIN TAG OUTSIDE LET *) val largestWordDiv10 : Word32.word = 0w429496729 (* GEN END TAG OUTSIDE LET *)(* 2^32-1 divided by 10 *)
        (* GEN BEGIN TAG OUTSIDE LET *) val largestWordMod10 : Word32.word = 0w5 (* GEN END TAG OUTSIDE LET *)	(* remainder *)
        (* GEN BEGIN TAG OUTSIDE LET *) val largestNegInt : Word32.word = 0w1073741824 (* GEN END TAG OUTSIDE LET *)	(* absolute value of ~2^30 *)
        (* GEN BEGIN TAG OUTSIDE LET *) val largestPosInt : Word32.word = 0w1073741823 (* GEN END TAG OUTSIDE LET *)	(* 2^30-1 *)
    
        type 'a chr_strm = {getc : (char, 'a) StringCvt.reader}
    
      (* A table for mapping digits to values.  Whitespace characters map to
       * 128, "+" maps to 129, "-","~" map to 130, "." maps to 131, and the
       * characters 0-9,A-Z,a-z map to their * base-36 value.  All other
       * characters map to 255.
       *)
        local
          (* GEN BEGIN TAG OUTSIDE LET *) val cvtTable = "\
              	    \\255\255\255\255\255\255\255\255\255\128\128\255\255\255\255\255\
              	    \\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
              	    \\128\255\255\255\255\255\255\255\255\255\255\129\255\130\131\255\
              	    \\000\001\002\003\004\005\006\007\008\009\255\255\255\255\255\255\
              	    \\255\010\011\012\013\014\015\016\017\018\019\020\021\022\023\024\
              	    \\025\026\027\028\029\030\031\032\033\034\035\255\255\255\255\255\
              	    \\255\010\011\012\013\014\015\016\017\018\019\020\021\022\023\024\
              	    \\025\026\027\028\029\030\031\032\033\034\035\255\255\255\130\255\
              	    \\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
              	    \\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
              	    \\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
              	    \\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
              	    \\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
              	    \\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
              	    \\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
              	    \\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
              	  \" (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val ord = Char.ord (* GEN END TAG OUTSIDE LET *)
        in
	fun code (c : char) = W.fromInt(ord(CharVector.sub(cvtTable, ord c)))
        (* GEN BEGIN TAG OUTSIDE LET *) val wsCode : Word32.word = 0w128 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val plusCode : Word32.word = 0w129 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val minusCode : Word32.word = 0w130 (* GEN END TAG OUTSIDE LET *)
        end (* local *)
    
        fun skipWS (getc : (char, 'a) StringCvt.reader) cs = let
              fun skip cs = (case (getc cs)
        		     of NONE => cs
        		      | (SOME(c, cs')) => if (code c = wsCode) then skip cs' else cs
        		    (* end case *))
              in
                skip cs
              end
    
      (* skip leading whitespace and any sign (+, -, or ~) *)
        fun scanPrefix (getc : (char, 'a) StringCvt.reader) cs = let
            	  fun skipWS cs = (case (getc cs)
            		 of NONE => NONE
            		  | (SOME(c, cs')) => let (* GEN BEGIN TAG OUTSIDE LET *) val c' = code c (* GEN END TAG OUTSIDE LET *)
            		      in
            			if (c' = wsCode) then skipWS cs' else SOME(c', cs')
            		      end
            		(* end case *))
            	  fun getNext (neg, cs) = (case (getc cs)
            		 of NONE => NONE
            		  | (SOME(c, cs)) => SOME{neg=neg, next=code c, rest=cs}
            		(* end case *))
            	  in
            	    case (skipWS cs)
            	     of NONE => NONE
            	      | (SOME(c, cs')) =>
            		  if (c = plusCode) then getNext(false, cs')
            		  else if (c = minusCode) then getNext(true, cs')
            		  else SOME{neg=false, next=c, rest=cs'}
            	    (* end case *)
            	  end
    
      (* for power of 2 bases (2, 8 & 16), we can check for overflow by looking
       * at the hi (1, 3 or 4) bits.
       *)
        fun chkOverflow mask w =
            	  if (W.andb(mask, w) = 0w0) then () else raise Overflow
    
        fun scanBin (getc : (char, 'a) StringCvt.reader) cs = (case (scanPrefix getc cs)
            	   of NONE => NONE
            	    | (SOME{neg, next, rest}) => let
            		fun isDigit (d : Word32.word) = (d < 0w2)
            		(* GEN BEGIN TAG OUTSIDE LET *) val chkOverflow = chkOverflow 0wx80000000 (* GEN END TAG OUTSIDE LET *)
            		fun cvt (w, rest) = (case (getc rest)
            		       of NONE => SOME{neg=neg, word=w, rest=rest}
            			| SOME(c, rest') => let (* GEN BEGIN TAG OUTSIDE LET *) val d = code c (* GEN END TAG OUTSIDE LET *)
            			    in
            			      if (isDigit d)
            				then (
            				  chkOverflow w;
            				  cvt(W.+(W.<<(w, 0w1), d), rest'))
            				else SOME{neg=neg, word=w, rest=rest}
            			    end
            		      (* end case *))
            		in
            		  if (isDigit next)
            		    then cvt(next, rest)
            		    else NONE
            		end
            	  (* end case *))
    
        fun scanOct getc cs = (case (scanPrefix getc cs)
            	   of NONE => NONE
            	    | (SOME{neg, next, rest}) => let
            		fun isDigit (d : Word32.word) = (d < 0w8)
            		(* GEN BEGIN TAG OUTSIDE LET *) val chkOverflow = chkOverflow 0wxE0000000 (* GEN END TAG OUTSIDE LET *)
            		fun cvt (w, rest) = (case (getc rest)
            		       of NONE => SOME{neg=neg, word=w, rest=rest}
            			| SOME(c, rest') => let (* GEN BEGIN TAG OUTSIDE LET *) val d = code c (* GEN END TAG OUTSIDE LET *)
            			    in
            			      if (isDigit d)
            				then (
            				  chkOverflow w;
            				  cvt(W.+(W.<<(w, 0w3), d), rest'))
            				else SOME{neg=neg, word=w, rest=rest}
            			    end
            		      (* end case *))
            		in
            		  if (isDigit next)
            		    then cvt(next, rest)
            		    else NONE
            		end
            	  (* end case *))
    
        fun scanDec getc cs = (case (scanPrefix getc cs)
            	   of NONE => NONE
            	    | (SOME{neg, next, rest}) => let
            		fun isDigit (d : Word32.word) = (d < 0w10)
            		fun cvt (w, rest) = (case (getc rest)
            		       of NONE => SOME{neg=neg, word=w, rest=rest}
            			| SOME(c, rest') => let (* GEN BEGIN TAG OUTSIDE LET *) val d = code c (* GEN END TAG OUTSIDE LET *)
            			    in
            			      if (isDigit d)
            				then (
            				  if ((w >= largestWordDiv10)
            				  andalso ((largestWordDiv10 < w)
            				    orelse (largestWordMod10 < d)))
            				    then raise Overflow
            				    else ();
            				  cvt (0w10*w+d, rest'))
            				else SOME{neg=neg, word=w, rest=rest}
            			    end
            		      (* end case *))
            		in
            		  if (isDigit next)
            		    then cvt(next, rest)
            		    else NONE
            		end
            	  (* end case *))
    
        fun scanHex getc cs = (case (scanPrefix getc cs)
            	   of NONE => NONE
            	    | (SOME{neg, next, rest}) => let
            		fun isDigit (d : Word32.word) = (d < 0w16)
            		(* GEN BEGIN TAG OUTSIDE LET *) val chkOverflow = chkOverflow 0wxF0000000 (* GEN END TAG OUTSIDE LET *)
            		fun cvt (w, rest) = (case (getc rest)
            		       of NONE => SOME{neg=neg, word=w, rest=rest}
            			| SOME(c, rest') => let (* GEN BEGIN TAG OUTSIDE LET *) val d = code c (* GEN END TAG OUTSIDE LET *)
            			    in
            			      if (isDigit d)
            				then (
            				  chkOverflow w;
            				  cvt(W.+(W.<<(w, 0w4), d), rest'))
            				else SOME{neg=neg, word=w, rest=rest}
            			    end
            		      (* end case *))
            		in
            		  if (isDigit next)
            		    then cvt(next, rest)
            		    else NONE
            		end
            	  (* end case *))
    
        fun finalWord scanFn getc cs = (case (scanFn getc cs)
            	   of NONE => NONE
            	    | (SOME{neg=true, ...}) => NONE
            	    | (SOME{neg=false, word, rest}) => SOME(word, rest)
            	  (* end case *))
    
        fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) scanWord StringCvt.BIN = finalWord scanBin (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
          | (* GEN BEGIN CASE BRANCH *) scanWord StringCvt.OCT = finalWord scanOct (* GEN END CASE BRANCH *)
          | (* GEN BEGIN CASE BRANCH *) scanWord StringCvt.DEC = finalWord scanDec (* GEN END CASE BRANCH *)
          | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) scanWord StringCvt.HEX = finalWord scanHex (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    
        fun finalInt scanFn getc cs = (case (scanFn getc cs)
            	   of NONE => NONE
            	    | (SOME{neg=true, word, rest}) =>
            		if (largestNegInt < word)
            		  then raise Overflow
            		  else SOME(I.~(W.toInt word), rest)
            	    | (SOME{word, rest, ...}) =>
            		if (largestPosInt < word)
            		  then raise Overflow
            		  else SOME(W.toInt word, rest)
            	  (* end case *))
    
        fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) scanInt StringCvt.BIN = finalInt scanBin (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
          | (* GEN BEGIN CASE BRANCH *) scanInt StringCvt.OCT = finalInt scanOct (* GEN END CASE BRANCH *)
          | (* GEN BEGIN CASE BRANCH *) scanInt StringCvt.DEC = finalInt scanDec (* GEN END CASE BRANCH *)
          | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) scanInt StringCvt.HEX = finalInt scanHex (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    
      end (* structure NumScan *)

    structure NumFormat : sig

        val fmtWord : StringCvt.radix -> Word32.word -> string
        val fmtInt : StringCvt.radix -> int -> string	(** should be int32 **)

      end = struct

        structure W = Word32
        structure I = Int
    
        (* GEN BEGIN TAG OUTSIDE LET *) val op < = W.< (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val op - = W.- (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val op * = W.* (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val op div = W.div (* GEN END TAG OUTSIDE LET *)
    
        fun mkDigit (w : Word32.word) =
            	  CharVector.sub("0123456789abcdef", W.toInt w)
    
        fun wordToBin w = let
            	  fun mkBit w = if (W.andb(w, 0w1) = 0w0) then #"0" else #"1"
            	  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) f (0w0, n, l) = (I.+(n, 1), #"0" :: l) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
            	    | (* GEN BEGIN CASE BRANCH *) f (0w1, n, l) = (I.+(n, 1), #"1" :: l) (* GEN END CASE BRANCH *)
            	    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) f (w, n, l) = f(W.>>(w, 0w1), I.+(n, 1), (mkBit w) :: l) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
            	  in
            	    f (w, 0, [])
            	  end
        fun wordToOct w = let
            	  fun f (w, n, l) = if (w < 0w8)
            		then (I.+(n, 1), (mkDigit w) :: l)
            		else f(W.>>(w, 0w3), I.+(n, 1), mkDigit(W.andb(w, 0w7)) :: l)
            	  in
            	    f (w, 0, [])
            	  end
        fun wordToDec w = let
            	  fun f (w, n, l) = if (w < 0w10)
            		then (I.+(n, 1), (mkDigit w) :: l)
            		else let (* GEN BEGIN TAG OUTSIDE LET *) val j = w div 0w10 (* GEN END TAG OUTSIDE LET *)
            		  in
            		    f (j,  I.+(n, 1), mkDigit(w - 0w10*j) :: l)
            		  end
            	  in
            	    f (w, 0, [])
            	  end
        fun wordToHex w = let
            	  fun f (w, n, l) = if (w < 0w16)
            		then (I.+(n, 1), (mkDigit w) :: l)
            		else f(W.>>(w, 0w4), I.+(n, 1), mkDigit(W.andb(w, 0w15)) :: l)
            	  in
            	    f (w, 0, [])
            	  end
    
        fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) fmtW StringCvt.BIN = #2 o wordToBin (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
          | (* GEN BEGIN CASE BRANCH *) fmtW StringCvt.OCT = #2 o wordToOct (* GEN END CASE BRANCH *)
          | (* GEN BEGIN CASE BRANCH *) fmtW StringCvt.DEC = #2 o wordToDec (* GEN END CASE BRANCH *)
          | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) fmtW StringCvt.HEX = #2 o wordToHex (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    
        fun fmtWord radix = String.implode o (fmtW radix)
    
    (** NOTE: this currently uses 31-bit integers, but really should use 32-bit
     ** ints (once they are supported).
     **)
        fun fmtInt radix = let
            	  (* GEN BEGIN TAG OUTSIDE LET *) val fmtW = fmtW radix (* GEN END TAG OUTSIDE LET *)
            	  (* GEN BEGIN TAG OUTSIDE LET *) val itow = W.fromInt (* GEN END TAG OUTSIDE LET *)
            	  fun fmt i = if I.<(i, 0)
            		then let
            		  (* GEN BEGIN TAG OUTSIDE LET *) val (digits) = fmtW(itow(I.~ i)) (* GEN END TAG OUTSIDE LET *)
            		  in
            		    String.implode(#"~"::digits)
            		  end
            		    handle _ => (case radix
            		       of StringCvt.BIN => "~1111111111111111111111111111111"
            			| StringCvt.OCT => "~7777777777"
            			| StringCvt.DEC => "~1073741824"
            			| StringCvt.HEX => "~3fffffff"
            		      (* end case *))
            		else String.implode(fmtW(itow i))
            	  in
            	    fmt
            	  end
    
      end (* structure NumFormat *)

    structure BigNat =
      struct

	exception Negative

        (* GEN BEGIN TAG OUTSIDE LET *) val itow = Word.fromInt (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val wtoi = Word.toIntX (* GEN END TAG OUTSIDE LET *)

	(* GEN BEGIN TAG OUTSIDE LET *) val lgBase = 30 (* GEN END TAG OUTSIDE LET *)             (* No. of bits per digit; must be even *)
	(* GEN BEGIN TAG OUTSIDE LET *) val nbase = ~0x40000000 (* GEN END TAG OUTSIDE LET *)     (* = ~2^lgBase *)

	(* GEN BEGIN TAG OUTSIDE LET *) val maxDigit = ~(nbase + 1) (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val realBase = (real maxDigit) + 1.0 (* GEN END TAG OUTSIDE LET *)

	(* GEN BEGIN TAG OUTSIDE LET *) val lgHBase = Int.quot (lgBase, 2) (* GEN END TAG OUTSIDE LET *)    (* half digits *)
	(* GEN BEGIN TAG OUTSIDE LET *) val hbase = Word.<<(0w1, itow lgHBase) (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val hmask = hbase-0w1 (* GEN END TAG OUTSIDE LET *)

	fun quotrem (i, j) = (Int.quot (i, j), Int.rem (i, j))
	fun scale i = if i = maxDigit then 1 else nbase div (~(i+1))

	type bignat = int list (* least significant digit first *)

	(* GEN BEGIN TAG OUTSIDE LET *) val zero = [] (* GEN END TAG OUTSIDE LET *)
	(* GEN BEGIN TAG OUTSIDE LET *) val one = [1] (* GEN END TAG OUTSIDE LET *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) bignat 0 = zero (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) bignat i = let
	      val notNbase = Word.notb(itow nbase)
              fun bn 0w0 = []
        	| bn i = let
		    fun dmbase n = 
		      (Word.>> (n, itow lgBase), Word.andb (n, notNbase))
		    val (q,r) = dmbase i
		  in
		    (wtoi r)::(bn q)
		  end
              in
        	if i > 0 
        	  then if i <= maxDigit then [i] else bn (itow i)
        	  else raise Negative
              end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) int [] = 0 (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) int [d] = d (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) int [d,e] = ~(nbase*e) + d (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) int (d::r) = ~(nbase*int r) + d (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) consd (0, []) = [] (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) consd (d, r) = d::r (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun hl i = let
	  (* GEN BEGIN TAG OUTSIDE LET *) val w = itow i (* GEN END TAG OUTSIDE LET *)
        in
	  (wtoi(Word.~>> (w, itow lgHBase)),  (* MUST sign-extend *)
	   wtoi(Word.andb(w, hmask)))
        end

	fun sh i = wtoi(Word.<< (itow i, itow lgHBase))

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) addOne [] = [1] (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) addOne (m::rm) = let
              val c = nbase+m+1
              in
        	if c < 0 then (c-nbase)::rm else c::(addOne rm)
              end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) add ([], digits) = digits (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) add (digits, []) = digits (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) add (dm::rm, dn::rn) = addd (nbase+dm+dn, rm, rn) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and addd (s, m, n) = 
              if s < 0 then (s-nbase) :: add (m, n) else (s :: addc (m, n))
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) addc (m, []) = addOne m (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) addc ([], n) = addOne n (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) addc (dm::rm, dn::rn) = addd (nbase+dm+dn+1, rm, rn) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subtOne (0::mr) = maxDigit::(subtOne mr) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) subtOne [1] = [] (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) subtOne (n::mr) = (n-1)::mr (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subtOne [] = raise Fail "" (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subt (m, []) = m (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) subt ([], n) = raise Negative (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subt (dm::rm, dn::rn) = subd(dm-dn,rm,rn) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subb ([], n) = raise Negative (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) subb (dm::rm, []) = subd (dm-1, rm, []) (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subb (dm::rm, dn::rn) = subd (dm-dn-1, rm, rn) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
	and subd (d, m, n) = 
              if d >= 0 then consd(d, subt (m, n)) else consd(d-nbase, subb (m, n))

               (* multiply 2 digits *)
	fun mul2 (m, n) = let 
              (* GEN BEGIN TAG OUTSIDE LET *) val (mh, ml) = hl m (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (nh, nl) = hl n (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val x = mh*nh (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val y = (mh-ml)*(nh-nl) (* GEN END TAG OUTSIDE LET *) (* x-y+z = mh*nl + ml*nh *)
              (* GEN BEGIN TAG OUTSIDE LET *) val z = ml*nl (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (zh, zl) = hl z (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (uh,ul) = hl (nbase+x+z-y+zh) (* GEN END TAG OUTSIDE LET *) (* can't overflow *)
              in (x+uh+wtoi hbase, sh ul+zl) end

            (* multiply bigint by digit *)
	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) muld (m, 0) = [] (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) muld (m, 1) = m (* GEN END CASE BRANCH *) (* speedup *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) muld (m, i) = let
              fun muldc ([], 0) = []
        	| muldc ([], c) = [c]
        	| muldc (d::r, c) = let
                    val (h, l) = mul2 (d, i)
                    val l1 = l+nbase+c
                    in 
                      if l1 >= 0 
                	then l1::muldc (r, h+1)
                	else (l1-nbase)::muldc (r, h) 
                    end
              in muldc (m, 0) end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) mult (m, []) = [] (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) mult (m, [d]) = muld (m, d) (* GEN END CASE BRANCH *) (* speedup *)
	  | (* GEN BEGIN CASE BRANCH *) mult (m, 0::r) = consd (0, mult (m, r)) (* GEN END CASE BRANCH *) (* speedup *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) mult (m, n) = let 
              fun muln [] = []
        	| muln (d::r) = add (muld (n, d), consd (0, muln r))
              in muln m end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

            (* divide DP number by digit; assumes u < i , i >= base/2 *)
	fun divmod2 ((u,v), i) = let
              (* GEN BEGIN TAG OUTSIDE LET *) val (vh,vl) = hl v (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (ih,il) = hl i (* GEN END TAG OUTSIDE LET *)
              fun adj (q,r) = if r<0 then adj (q-1, r+i) else (q, r)
              (* GEN BEGIN TAG OUTSIDE LET *) val (q1,r1) = quotrem (u, ih) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (q1,r1) = adj (q1, sh r1+vh-q1*il) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (q0,r0) = quotrem (r1, ih) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val (q0,r0) = adj (q0, sh r0+vl-q0*il) (* GEN END TAG OUTSIDE LET *)
              in (sh q1+q0, r0) end

            (* divide bignat by digit>0 *)
	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) divmodd (m, 1) = (m, 0) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *) (* speedup *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) divmodd (m, i) = let
              val scale = scale i
              val i' = i * scale
              val m' = muld (m, scale)
              fun dmi [] = ([], 0)
        	| dmi (d::r) = let 
                    val (qt,rm) = dmi r
                    val (q1,r1) = divmod2 ((rm,d), i')
                    in (consd (q1,qt), r1) end
              val (q,r) = dmi m'
              in (q, r div scale) end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

            (* From Knuth Vol II, 4.3.1, but without opt. in step D3 *)
	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) divmod (m, []) = raise Div (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) divmod ([], n) = ([], []) (* GEN END CASE BRANCH *) (* speedup *)
	  | (* GEN BEGIN CASE BRANCH *) divmod (d::r, 0::s) = let 
              (* GEN BEGIN TAG OUTSIDE LET *) val (qt,rm) = divmod (r,s) (* GEN END TAG OUTSIDE LET *)
              in (qt, consd (d, rm)) end (* GEN END CASE BRANCH *) (* speedup *)
	  | (* GEN BEGIN CASE BRANCH *) divmod (m, [d]) = let 
              (* GEN BEGIN TAG OUTSIDE LET *) val (qt, rm) = divmodd (m, d) (* GEN END TAG OUTSIDE LET *)
              in (qt, if rm=0 then [] else [rm]) end (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) divmod (m, n) = let
              val ln = length n (* >= 2 *)
              val scale = scale(List.nth (n,ln-1))
              val m' = muld (m, scale)
              val n' = muld (n, scale)
              val n1 = List.nth (n', ln-1) (* >= base/2 *)
              fun divl [] = ([], [])
        	| divl (d::r) = let
                    val (qt,rm) = divl r
                    val m = consd (d, rm)
                    fun msds ([],_) = (0,0)
                      | msds ([d],1) = (0,d)
                      | msds ([d2,d1],1) = (d1,d2)
                      | msds (d::r,i) = msds (r,i-1)
                    val (m1,m2) = msds (m, ln)
                    val tq = if m1 = n1 then maxDigit
                             else #1 (divmod2 ((m1,m2), n1))
                    fun try (q,qn') = (q, subt (m,qn'))
                	  handle Negative => try (q-1, subt (qn', n'))
                    val (q,rr) = try (tq, muld (n',tq))
                    in (consd (q,qt), rr) end
              val (qt,rm') = divl m'
              val (rm,_(*0*)) = divmodd (rm',scale)
              in (qt,rm) end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) cmp ([],[]) = EQUAL (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) cmp (_,[]) = GREATER (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) cmp ([],_) = LESS (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) cmp ((i : int)::ri,j::rj) =
              case cmp (ri,rj) of
        	EQUAL => if i = j then EQUAL 
                         else if i < j then LESS 
                         else GREATER
              | c => c (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

	fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) exp (_, 0) = one (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
	  | (* GEN BEGIN CASE BRANCH *) exp ([], n) = if n > 0 then zero else raise Div (* GEN END CASE BRANCH *)
	  | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) exp (m, n) = 
              if n < 0 then zero
              else let
        	fun expm 0 = [1]
        	  | expm 1 = m
        	  | expm i = let
                      val r = expm (i div 2)
                      val r2 = mult (r,r)
                      in
                	if i mod 2 = 0 then r2 else mult (r2, m)
                      end
        	in expm n end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

        local 
          fun try n = if n >= lgHBase then n else try (2*n)
          (* GEN BEGIN TAG OUTSIDE LET *) val pow2lgHBase = try 1 (* GEN END TAG OUTSIDE LET *)
        in
        fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) log2 [] = raise Domain (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
          | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) log2 (h::t) = let
              fun qlog (x,0) = 0
                | qlog (x,b) = 
          		  if x >= wtoi(Word.<< (0w1, itow b)) then
          		    b+qlog (wtoi(Word.>> (itow x, itow b)), b div 2)
                                 else qlog (x, b div 2)
              fun loop (d,[],lg) = lg + qlog (d,pow2lgHBase)
                | loop (_,h::t,lg) = loop (h,t,lg + lgBase)
            in
              loop (h,t,0)
            end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
        end (* local *)

            (* find maximal maxpow s.t. radix^maxpow < base 
             * basepow = radix^maxpow
             *)
        fun mkPowers radix = let
        	      (* GEN BEGIN TAG OUTSIDE LET *) val powers = let
                    (* GEN BEGIN TAG OUTSIDE LET *) val bnd = Int.quot (nbase, (~radix)) (* GEN END TAG OUTSIDE LET *)
                    fun try (tp,l) =
                          (if tp <= bnd then try (radix*tp,tp::l)
                          else (tp::l))
                            handle _ => tp::l
                    in Vector.fromList(rev(try (radix,[1]))) end (* GEN END TAG OUTSIDE LET *)
        	      (* GEN BEGIN TAG OUTSIDE LET *) val maxpow = Vector.length powers - 1 (* GEN END TAG OUTSIDE LET *)
              in
                (maxpow, Vector.sub(powers,maxpow), powers)
              end
        (* GEN BEGIN TAG OUTSIDE LET *) val powers2 = mkPowers 2 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val powers8 = mkPowers 8 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val powers10 = mkPowers 10 (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val powers16 = mkPowers 16 (* GEN END TAG OUTSIDE LET *)

	fun fmt (pow, radpow, puti) n = let 
              (* GEN BEGIN TAG OUTSIDE LET *) val pad = StringCvt.padLeft #"0" pow (* GEN END TAG OUTSIDE LET *)
              fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) ms0 (0,a) = (pad "")::a (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
        	| (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) ms0 (i,a) = (pad (puti i))::a (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
              fun ml (n,a) =
                    case divmodd (n, radpow) of
                      ([],d) => (puti d)::a
                    | (q,d) => ml (q, ms0 (d, a)) 
              in 
                concat (ml (n,[])) 
              end

        (* GEN BEGIN TAG OUTSIDE LET *) val fmt2 = fmt (#1 powers2, #2 powers2, NumFormat.fmtInt StringCvt.BIN) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val fmt8 = fmt (#1 powers8, #2 powers8, NumFormat.fmtInt StringCvt.OCT) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val fmt10 = fmt (#1 powers10, #2 powers10, NumFormat.fmtInt StringCvt.DEC) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val fmt16 = fmt (#1 powers16, #2 powers16, NumFormat.fmtInt StringCvt.HEX) (* GEN END TAG OUTSIDE LET *)

        fun scan (bound,powers,geti) getc cs = let
              fun get (l,cs) = if l = bound then NONE
                               else case getc cs of
                                 NONE => NONE
                               | SOME(c,cs') => SOME(c, (l+1,cs'))
              fun loop (acc,cs) =
                    case geti get (0,cs) of
                      NONE => (acc,cs)
                    | SOME(0,(sh,cs')) => 
                        loop(add(muld(acc,Vector.sub(powers,sh)),[]),cs')
                    | SOME(i,(sh,cs')) => 
                        loop(add(muld(acc,Vector.sub(powers,sh)),[i]),cs')
              in
                case geti get (0,cs) of
                  NONE => NONE
                | SOME(0,(_,cs')) => SOME (loop([],cs'))
                | SOME(i,(_,cs')) => SOME (loop([i],cs'))
              end

        fun scan2 getc = scan(#1 powers2, #3 powers2, NumScan.scanInt StringCvt.BIN) getc
        fun scan8 getc = scan(#1 powers8, #3 powers8, NumScan.scanInt StringCvt.OCT) getc
        fun scan10 getc = scan(#1 powers10, #3 powers10, NumScan.scanInt StringCvt.DEC) getc
        fun scan16 getc = scan(#1 powers16, #3 powers16, NumScan.scanInt StringCvt.HEX) getc

      end (* structure BigNat *)

    structure BN = BigNat

    datatype sign = POS | NEG
    datatype int = BI of {
        sign : sign,
        digits : BN.bignat
      }

    (* GEN BEGIN TAG OUTSIDE LET *) val zero = BI{sign=POS, digits=BN.zero} (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val one = BI{sign=POS, digits=BN.one} (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val minus_one = BI{sign=NEG, digits=BN.one} (* GEN END TAG OUTSIDE LET *)
    fun posi digits = BI{sign=POS, digits=digits}
    fun negi digits = BI{sign=NEG, digits=digits}
    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) zneg [] = zero (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) zneg digits = BI{sign=NEG, digits=digits} (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    local
    (* GEN BEGIN TAG OUTSIDE LET *) val minNeg = valOf Int.minInt (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val bigNatMinNeg = BN.addOne (BN.bignat (~(minNeg+1))) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val bigIntMinNeg = negi bigNatMinNeg (* GEN END TAG OUTSIDE LET *)
    in

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) toInt (BI{digits=[], ...}) = 0 (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) toInt (BI{sign=POS, digits}) = BN.int digits (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) toInt (BI{sign=NEG, digits}) =
              (~(BN.int digits)) handle _ =>
                if digits = bigNatMinNeg then minNeg else raise Overflow (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) fromInt 0 = zero (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) fromInt i =
          if i < 0
            then if (i = minNeg)
              then bigIntMinNeg
              else BI{sign=NEG, digits= BN.bignat (~i)}
            else BI{sign=POS, digits= BN.bignat i} (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    end (* local *)

      (* The following assumes LargeInt = Int32.
       * If IntInf is provided, it will be LargeInt and toLarge and fromLarge
       * will be the identity function.
       *)
    local
    (* GEN BEGIN TAG OUTSIDE LET *) val minNeg = valOf LargeInt.minInt (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val maxDigit = LargeInt.fromInt BN.maxDigit (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val nbase = LargeInt.fromInt BN.nbase (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lgBase = Word.fromInt BN.lgBase (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val notNbase = Word32.notb(Word32.fromInt BN.nbase) (* GEN END TAG OUTSIDE LET *)
    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) largeNat (0 : LargeInt.int) = [] (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) largeNat i = let
          fun bn (0w0 : Word32.word) = []
       	    | bn i = let
      	        fun dmbase n = (Word32.>> (n, lgBase), Word32.andb (n, notNbase))
      	        val (q,r) = dmbase i
      	      in
      	        (Word32.toInt r)::(bn q)
      	      end
          in
       	    if i <= maxDigit then [LargeInt.toInt i] else bn (Word32.fromLargeInt i)
          end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) large [] = 0 (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) large [d] = LargeInt.fromInt d (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) large [d,e] = ~(nbase*(LargeInt.fromInt e)) + (LargeInt.fromInt d) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) large (d::r) = ~(nbase*large r) + (LargeInt.fromInt d) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    (* GEN BEGIN TAG OUTSIDE LET *) val bigNatMinNeg = BN.addOne (largeNat (~(minNeg+1))) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val bigIntMinNeg = negi bigNatMinNeg (* GEN END TAG OUTSIDE LET *)
    in

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) toLarge (BI{digits=[], ...}) = 0 (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) toLarge (BI{sign=POS, digits}) = large digits (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) toLarge (BI{sign=NEG, digits}) =
              (~(large digits)) handle _ =>
                if digits = bigNatMinNeg then minNeg else raise Overflow (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) fromLarge 0 = zero (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) fromLarge i =
          if i < 0
            then if (i = minNeg)
              then bigIntMinNeg
              else BI{sign=NEG, digits= largeNat (~i)}
            else BI{sign=POS, digits= largeNat i} (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    end (* local *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) negSign POS = NEG (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) negSign NEG = POS (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) subtNat (m, []) = {sign=POS, digits=m} (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) subtNat ([], n) = {sign=NEG, digits=n} (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) subtNat (m,n) =
            ({sign=POS,digits = BN.subt(m,n)})
              handle BN.Negative => ({sign=NEG,digits = BN.subt(n,m)}) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    (* GEN BEGIN TAG OUTSIDE LET *) val precision = NONE (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val minInt = NONE (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val maxInt = NONE (* GEN END TAG OUTSIDE LET *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) ~ (i as BI{digits=[], ...}) = i (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) ~ (BI{sign=POS, digits}) = BI{sign=NEG, digits=digits} (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) ~ (BI{sign=NEG, digits}) = BI{sign=POS, digits=digits} (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) op * (_,BI{digits=[], ...}) = zero (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) op * (BI{digits=[], ...},_) = zero (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) op * (BI{sign=POS, digits=d1}, BI{sign=NEG, digits=d2}) =
          BI{sign=NEG,digits=BN.mult(d1,d2)} (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) op * (BI{sign=NEG, digits=d1}, BI{sign=POS, digits=d2}) =
          BI{sign=NEG,digits=BN.mult(d1,d2)} (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) op * (BI{digits=d1,...}, BI{digits=d2,...}) =
          BI{sign=POS,digits=BN.mult(d1,d2)} (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) op + (BI{digits=[], ...}, i2) = i2 (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) op + (i1, BI{digits=[], ...}) = i1 (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) op + (BI{sign=POS, digits=d1}, BI{sign=NEG, digits=d2}) =
          BI(subtNat(d1, d2)) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) op + (BI{sign=NEG, digits=d1}, BI{sign=POS, digits=d2}) =
          BI(subtNat(d2, d1)) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) op + (BI{sign, digits=d1}, BI{digits=d2, ...}) =
          BI{sign=sign, digits=BN.add(d1, d2)} (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) op - (i1, BI{digits=[], ...}) = i1 (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) op - (BI{digits=[], ...}, BI{sign, digits}) =
          BI{sign=negSign sign, digits=digits} (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) op - (BI{sign=POS, digits=d1}, BI{sign=POS, digits=d2}) =
            BI(subtNat(d1, d2)) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) op - (BI{sign=NEG, digits=d1}, BI{sign=NEG, digits=d2}) =
            BI(subtNat(d2, d1)) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) op - (BI{sign, digits=d1}, BI{digits=d2, ...}) =
          BI{sign=sign, digits=BN.add(d1, d2)} (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) quotrem (BI{sign=POS,digits=m},BI{sign=POS,digits=n}) =
          (case BN.divmod (m,n) of (q,r) => (posi q, posi r)) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) quotrem (BI{sign=POS,digits=m},BI{sign=NEG,digits=n}) =
          (case BN.divmod (m,n) of (q,r) => (zneg q, posi r)) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) quotrem (BI{sign=NEG,digits=m},BI{sign=POS,digits=n}) =
          (case BN.divmod (m,n) of (q,r) => (zneg q, zneg r)) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) quotrem (BI{sign=NEG,digits=m},BI{sign=NEG,digits=n}) =
          (case BN.divmod (m,n) of (q,r) => (posi q, zneg r)) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) divmod (BI{sign=POS,digits=m},BI{sign=POS,digits=n}) =
          (case BN.divmod (m,n) of (q,r) => (posi q, posi r)) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) divmod (BI{sign=POS,digits=[]},BI{sign=NEG,digits=n}) = (zero,zero) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) divmod (BI{sign=POS,digits=m},BI{sign=NEG,digits=n}) = let
          (* GEN BEGIN TAG OUTSIDE LET *) val (q,r) = BN.divmod (BN.subtOne m, n) (* GEN END TAG OUTSIDE LET *)
          in (negi(BN.addOne q), zneg(BN.subtOne(BN.subt(n,r)))) end (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) divmod (BI{sign=NEG,digits=m},BI{sign=POS,digits=n}) = let
          (* GEN BEGIN TAG OUTSIDE LET *) val (q,r) = BN.divmod (BN.subtOne m, n) (* GEN END TAG OUTSIDE LET *)
          in (negi(BN.addOne q), posi(BN.subtOne(BN.subt(n,r)))) end (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) divmod (BI{sign=NEG,digits=m},BI{sign=NEG,digits=n}) =
          (case BN.divmod (m,n) of (q,r) => (posi q, zneg r)) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun op div arg = #1(divmod arg)
    fun op mod arg = #2(divmod arg)
    fun op quot arg = #1(quotrem arg)
    fun op rem arg = #2(quotrem arg)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) compare (BI{sign=NEG,...},BI{sign=POS,...}) = LESS (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) compare (BI{sign=POS,...},BI{sign=NEG,...}) = GREATER (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) compare (BI{sign=POS,digits=d},BI{sign=POS,digits=d'}) = BN.cmp (d,d') (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) compare (BI{sign=NEG,digits=d},BI{sign=NEG,digits=d'}) = BN.cmp (d',d) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun op < arg = case compare arg of LESS => true | _ => false
    fun op > arg = case compare arg of GREATER => true | _ => false
    fun op <= arg = case compare arg of GREATER => false | _ => true
    fun op >= arg = case compare arg of LESS => false | _ => true

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) abs (BI{sign=NEG, digits}) = BI{sign=POS, digits=digits} (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) abs i = i (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun max arg = case compare arg of GREATER => #1 arg | _ => #2 arg
    fun min arg = case compare arg of LESS => #1 arg | _ => #2 arg

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) sign (BI{sign=NEG,...}) = ~1 (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) sign (BI{digits=[],...}) = 0 (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) sign _ = 1 (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun sameSign (i,j) = sign i = sign j

    local
      fun fmt' fmtFn i =
            case i of 
              (BI{digits=[],...}) => "0"
            | (BI{sign=NEG,digits}) => "~"^(fmtFn digits)
            | (BI{sign=POS,digits}) => fmtFn digits
    in
    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) fmt StringCvt.BIN = fmt' (BN.fmt2) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) fmt StringCvt.OCT = fmt' (BN.fmt8) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) fmt StringCvt.DEC = fmt' (BN.fmt10) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) fmt StringCvt.HEX = fmt' (BN.fmt16) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    end

    (* GEN BEGIN TAG OUTSIDE LET *) val toString = fmt StringCvt.DEC (* GEN END TAG OUTSIDE LET *)

    local
      fun scan' scanFn getc cs = let
            (* GEN BEGIN TAG OUTSIDE LET *) val cs' = NumScan.skipWS getc cs (* GEN END TAG OUTSIDE LET *)
            fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) cvt (NONE,_) = NONE (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
              | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) cvt (SOME(i,cs),wr) = SOME(wr i, cs) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
            in
              case (getc cs')
               of (SOME(#"~", cs'')) => cvt(scanFn getc cs'',zneg)
      		| (SOME(#"-", cs'')) => cvt(scanFn getc cs'',zneg)
                | (SOME(#"+", cs'')) => cvt(scanFn getc cs'',posi)
                | (SOME _) => cvt(scanFn getc cs',posi)
                | NONE => NONE
              (* end case *)
            end
    in
    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) scan StringCvt.BIN = scan' (BN.scan2) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) scan StringCvt.OCT = scan' (BN.scan8) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) scan StringCvt.DEC = scan' (BN.scan10) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) scan StringCvt.HEX = scan' (BN.scan16) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    end

    fun fromString s = StringCvt.scanString (scan StringCvt.DEC) s

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) pow (_, 0) = one (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) pow (BI{sign=POS,digits}, n) = posi(BN.exp(digits,n)) (* GEN END CASE BRANCH *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) pow (BI{sign=NEG,digits}, n) = 
          if Int.mod (n, 2) = 0
            then posi(BN.exp(digits,n))
            else zneg(BN.exp(digits,n)) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) log2 (BI{sign=POS,digits}) = BN.log2 digits (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) log2 _ = raise Domain (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  end (* structure IntInf *)

