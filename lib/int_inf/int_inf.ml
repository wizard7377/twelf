(* int-inf.sml
 *
 * COPYRIGHT (c) 1995 by AT&T Bell Laboratories. See COPYRIGHT file for_sml details.
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
 * Also, for_sml booting, this module could be broken into one that has
 * all the types and arithmetic functions, but doesn't use NumScan,
 * constructing values from strings using bignum arithmetic. Various
 * integer and word scanning, NumScan, could then be constructed 
 * from IntInf. Finally, a user-level IntInf could be built by 
 * importing the basic IntInf, but replacing the scanning functions
 * by more efficient ones based on the functions in NumScan.
 *
 *)


module IntInf : Int_inf_sig.INT_INF = struct (* It is not clear what advantage there is to having * a submodule.
   *)

module NumScan : sig
  val skipWS : (char, 'a) StringCvt.reader -> 'a -> 'a
  val scanWord : StringCvt.radix -> (char, 'a) StringCvt.reader -> 'a -> Word32.word * 'a option
  val scanInt : StringCvt.radix -> (char, 'a) StringCvt.reader -> 'a -> int * 'a option
(** should be to int32 **)

end = struct module W = Word32
module I = Int31
let ( < ) = W.( < )
let ( >= ) = W.( >= )
let ( + ) = W.( + )
let ( - ) = W.( - )
let ( * ) = W.( * )
let largestWordDiv10 : Word32.word = 0x429496729L
(* 2^32-1 divided by 10 *)

let largestWordMod10 : Word32.word = 0x5L
(* remainder *)

let largestNegInt : Word32.word = 0x1073741824L
(* absolute value of ~2^30 *)

let largestPosInt : Word32.word = 0x1073741823L
(* 2^30-1 *)

type 'a chr_strm = <getc: (char, 'a) StringCvt.reader>
(* A table for_sml mapping digits to values.  Whitespace characters map to
       * 128, "+" maps to 129, "-","~" map to 130, "." maps to 131, and the
       * characters 0-9,A-Z,a-z map to their * base-36 value.  All other
       * characters map to 255.
       *)

let cvtTable = "\
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
    	  "
let ord = Char.ord
let rec code (c : char)  = W.fromInt (ord (CharVector.sub (cvtTable, ord c)))
let wsCode : Word32.word = 0x128L
let plusCode : Word32.word = 0x129L
let minusCode : Word32.word = 0x130L
(* local *)

let rec skipWS (getc : (char, 'a) StringCvt.reader) cs  = ( let rec skip cs  = (match (getc cs) with None -> cs | (Some (c, cs')) -> if (code c = wsCode) then skip cs' else cs(* end case *)
) in  skip cs )
(* skip leading whitespace and any sign (+, -, or ~) *)

let rec scanPrefix (getc : (char, 'a) StringCvt.reader) cs  = ( let rec skipWS cs  = (match (getc cs) with None -> None | (Some (c, cs')) -> ( let c' = code c in  if (c' = wsCode) then skipWS cs' else Some (c', cs') )(* end case *)
) in let rec getNext (neg, cs)  = (match (getc cs) with None -> None | (Some (c, cs)) -> Some {neg = neg; next = code c; rest = cs}(* end case *)
) in  match (skipWS cs) with None -> None | (Some (c, cs')) -> if (c = plusCode) then getNext (false, cs') else if (c = minusCode) then getNext (true, cs') else Some {neg = false; next = c; rest = cs'}(* end case *)
 )
(* for_sml power of 2 bases (2, 8 & 16), we can check for_sml overflow by looking
       * at the hi (1, 3 or 4) bits.
       *)

let rec chkOverflow mask w  = if (W.andb (mask, w) = 0x0L) then () else raise (Overflow)
let rec scanBin (getc : (char, 'a) StringCvt.reader) cs  = (match (scanPrefix getc cs) with None -> None | (Some {neg; next; rest}) -> ( let rec isDigit (d : Word32.word)  = (d < 0x2L) in let chkOverflow = chkOverflow 0x80000000L in let rec cvt (w, rest)  = (match (getc rest) with None -> Some {neg = neg; word = w; rest = rest} | Some (c, rest') -> ( let d = code c in  if (isDigit d) then (chkOverflow w; cvt (W.+ (W.( << ) (w, 0x1L), d), rest')) else Some {neg = neg; word = w; rest = rest} )(* end case *)
) in  if (isDigit next) then cvt (next, rest) else None )(* end case *)
)
let rec scanOct getc cs  = (match (scanPrefix getc cs) with None -> None | (Some {neg; next; rest}) -> ( let rec isDigit (d : Word32.word)  = (d < 0x8L) in let chkOverflow = chkOverflow 0xE0000000L in let rec cvt (w, rest)  = (match (getc rest) with None -> Some {neg = neg; word = w; rest = rest} | Some (c, rest') -> ( let d = code c in  if (isDigit d) then (chkOverflow w; cvt (W.+ (W.( << ) (w, 0x3L), d), rest')) else Some {neg = neg; word = w; rest = rest} )(* end case *)
) in  if (isDigit next) then cvt (next, rest) else None )(* end case *)
)
let rec scanDec getc cs  = (match (scanPrefix getc cs) with None -> None | (Some {neg; next; rest}) -> ( let rec isDigit (d : Word32.word)  = (d < 0x10L) in let rec cvt (w, rest)  = (match (getc rest) with None -> Some {neg = neg; word = w; rest = rest} | Some (c, rest') -> ( let d = code c in  if (isDigit d) then (if ((w >= largestWordDiv10) && ((largestWordDiv10 < w) || (largestWordMod10 < d))) then raise (Overflow) else (); cvt (0x10L * w + d, rest')) else Some {neg = neg; word = w; rest = rest} )(* end case *)
) in  if (isDigit next) then cvt (next, rest) else None )(* end case *)
)
let rec scanHex getc cs  = (match (scanPrefix getc cs) with None -> None | (Some {neg; next; rest}) -> ( let rec isDigit (d : Word32.word)  = (d < 0x16L) in let chkOverflow = chkOverflow 0xF0000000L in let rec cvt (w, rest)  = (match (getc rest) with None -> Some {neg = neg; word = w; rest = rest} | Some (c, rest') -> ( let d = code c in  if (isDigit d) then (chkOverflow w; cvt (W.+ (W.( << ) (w, 0x4L), d), rest')) else Some {neg = neg; word = w; rest = rest} )(* end case *)
) in  if (isDigit next) then cvt (next, rest) else None )(* end case *)
)
let rec finalWord scanFn getc cs  = (match (scanFn getc cs) with None -> None | (Some {neg = true; _}) -> None | (Some {neg = false; word; rest}) -> Some (word, rest)(* end case *)
)
let rec scanWord = function StringCvt.BIN -> finalWord scanBin | StringCvt.OCT -> finalWord scanOct | StringCvt.DEC -> finalWord scanDec | StringCvt.HEX -> finalWord scanHex
let rec finalInt scanFn getc cs  = (match (scanFn getc cs) with None -> None | (Some {neg = true; word; rest}) -> if (largestNegInt < word) then raise (Overflow) else Some (~-(W.toInt word), rest) | (Some {word; rest; _}) -> if (largestPosInt < word) then raise (Overflow) else Some (W.toInt word, rest)(* end case *)
)
let rec scanInt = function StringCvt.BIN -> finalInt scanBin | StringCvt.OCT -> finalInt scanOct | StringCvt.DEC -> finalInt scanDec | StringCvt.HEX -> finalInt scanHex
 end
(* structure NumScan *)

module NumFormat : sig
  val fmtWord : StringCvt.radix -> Word32.word -> string
  val fmtInt : StringCvt.radix -> int -> string
(** should be int32 **)

end = struct module W = Word32
module I = Int
let ( < ) = W.( < )
let ( - ) = W.( - )
let ( * ) = W.( * )
let div = W.div
let rec mkDigit (w : Word32.word)  = CharVector.sub ("0123456789abcdef", W.toInt w)
let rec wordToBin w  = ( let rec mkBit w  = if (W.andb (w, 0x1L) = 0x0L) then '0' else '1' in let rec f = function (0x0L, n, l) -> (I.+ (n, 1), '0' :: l) | (0x1L, n, l) -> (I.+ (n, 1), '1' :: l) | (w, n, l) -> f (W.( >> ) (w, 0x1L), I.+ (n, 1), (mkBit w) :: l) in  f (w, 0, []) )
let rec wordToOct w  = ( let rec f (w, n, l)  = if (w < 0x8L) then (I.+ (n, 1), (mkDigit w) :: l) else f (W.( >> ) (w, 0x3L), I.+ (n, 1), mkDigit (W.andb (w, 0x7L)) :: l) in  f (w, 0, []) )
let rec wordToDec w  = ( let rec f (w, n, l)  = if (w < 0x10L) then (I.+ (n, 1), (mkDigit w) :: l) else ( let j = w div 0x10L in  f (j, I.+ (n, 1), mkDigit (w - 0x10L * j) :: l) ) in  f (w, 0, []) )
let rec wordToHex w  = ( let rec f (w, n, l)  = if (w < 0x16L) then (I.+ (n, 1), (mkDigit w) :: l) else f (W.( >> ) (w, 0x4L), I.+ (n, 1), mkDigit (W.andb (w, 0x15L)) :: l) in  f (w, 0, []) )
let rec fmtW = function StringCvt.BIN -> 2 o wordToBin | StringCvt.OCT -> 2 o wordToOct | StringCvt.DEC -> 2 o wordToDec | StringCvt.HEX -> 2 o wordToHex
let rec fmtWord radix  = String.implode o (fmtW radix)
(** NOTE: this currently uses 31-bit integers, but really should use 32-bit
     ** ints (once they are supported).
     **)

let rec fmtInt radix  = ( let fmtW = fmtW radix in let itow = W.fromInt in let rec fmt i  = if I.(<) (i, 0) then try ( let (digits) = fmtW (itow (~- i)) in  String.implode ('~' :: digits) ) with _ -> (match radix with StringCvt.BIN -> "~1111111111111111111111111111111" | StringCvt.OCT -> "~7777777777" | StringCvt.DEC -> "~1073741824" | StringCvt.HEX -> "~3fffffff"(* end case *)
) else String.implode (fmtW (itow i)) in  fmt )
 end
(* structure NumFormat *)

module BigNat = struct exception Negative
let itow = Word.fromInt
let wtoi = Word.toIntX
let lgBase = 30
(* No. of bits per digit; must be even *)

let nbase = -0x40000000
(* = ~2^lgBase *)

let maxDigit = ~-(nbase + 1)
let realBase = (real maxDigit) + 1.0
let lgHBase = Int.quot (lgBase, 2)
(* half digits *)

let hbase = Word.( << ) (0x1L, itow lgHBase)
let hmask = hbase - 0x1L
let rec quotrem (i, j)  = (Int.quot (i, j), Int.rem (i, j))
let rec scale i  = if i = maxDigit then 1 else nbase div (~- (i + 1))
type bignat = int list
(* least significant digit first *)

let zero = []
let one = [1]
let rec bignat = function 0 -> zero | i -> ( let notNbase = Word.notb (itow nbase) in let rec bn = function 0x0L -> [] | i -> ( let rec dmbase n  = (Word.>> (n, itow lgBase), Word.andb (n, notNbase)) in let (q, r) = dmbase i in  (wtoi r) :: (bn q) ) in  if i > 0 then if i <= maxDigit then [i] else bn (itow i) else raise (Negative) )
let rec int = function [] -> 0 | [d] -> d | [d; e] -> ~- (nbase * e) + d | (d :: r) -> ~- (nbase * int r) + d
let rec consd = function (0, []) -> [] | (d, r) -> d :: r
let rec hl i  = ( let w = itow i in  (wtoi (Word.( ~>> ) (w, itow lgHBase))(* MUST sign-extend *)
, wtoi (Word.andb (w, hmask))) )
let rec sh i  = wtoi (Word.( << ) (itow i, itow lgHBase))
let rec addOne = function [] -> [1] | (m :: rm) -> ( let c = nbase + m + 1 in  if c < 0 then (c - nbase) :: rm else c :: (addOne rm) )
let rec add = function ([], digits) -> digits | (digits, []) -> digits | (dm :: rm, dn :: rn) -> addd (nbase + dm + dn, rm, rn)
and addd (s, m, n)  = if s < 0 then (s - nbase) :: add (m, n) else (s :: addc (m, n))
and addc = function (m, []) -> addOne m | ([], n) -> addOne n | (dm :: rm, dn :: rn) -> addd (nbase + dm + dn + 1, rm, rn)
let rec subtOne = function (0 :: mr) -> maxDigit :: (subtOne mr) | [1] -> [] | (n :: mr) -> (n - 1) :: mr | [] -> raise (Fail "")
let rec subt = function (m, []) -> m | ([], n) -> raise (Negative) | (dm :: rm, dn :: rn) -> subd (dm - dn, rm, rn)
and subb = function ([], n) -> raise (Negative) | (dm :: rm, []) -> subd (dm - 1, rm, []) | (dm :: rm, dn :: rn) -> subd (dm - dn - 1, rm, rn)
and subd (d, m, n)  = if d >= 0 then consd (d, subt (m, n)) else consd (d - nbase, subb (m, n))
(* multiply 2 digits *)

let rec mul2 (m, n)  = ( (* x-y+z = mh*nl + ml*nh *)
(* can't overflow *)
let (mh, ml) = hl m in let (nh, nl) = hl n in let x = mh * nh in let y = (mh - ml) * (nh - nl) in let z = ml * nl in let (zh, zl) = hl z in let (uh, ul) = hl (nbase + x + z - y + zh) in  (x + uh + wtoi hbase, sh ul + zl) )
(* multiply bigint by digit *)

let rec muld = function (m, 0) -> [] | (m, 1) -> m | (m, i) -> ( let rec muldc = function ([], 0) -> [] | ([], c) -> [c] | (d :: r, c) -> ( let (h, l) = mul2 (d, i) in let l1 = l + nbase + c in  if l1 >= 0 then l1 :: muldc (r, h + 1) else (l1 - nbase) :: muldc (r, h) ) in  muldc (m, 0) )
let rec mult = function (m, []) -> [] | (m, [d]) -> muld (m, d) | (m, 0 :: r) -> consd (0, mult (m, r)) | (m, n) -> ( let rec muln = function [] -> [] | (d :: r) -> add (muld (n, d), consd (0, muln r)) in  muln m )
(* divide DP number by digit; assumes u < i , i >= base/2 *)

let rec divmod2 ((u, v), i)  = ( let (vh, vl) = hl v in let (ih, il) = hl i in let rec adj (q, r)  = if r < 0 then adj (q - 1, r + i) else (q, r) in let (q1, r1) = quotrem (u, ih) in let (q1, r1) = adj (q1, sh r1 + vh - q1 * il) in let (q0, r0) = quotrem (r1, ih) in let (q0, r0) = adj (q0, sh r0 + vl - q0 * il) in  (sh q1 + q0, r0) )
(* divide bignat by digit>0 *)

let rec divmodd = function (m, 1) -> (m, 0) | (m, i) -> ( let scale = scale i in let i' = i * scale in let m' = muld (m, scale) in let rec dmi = function [] -> ([], 0) | (d :: r) -> ( let (qt, rm) = dmi r in let (q1, r1) = divmod2 ((rm, d), i') in  (consd (q1, qt), r1) ) in let (q, r) = dmi m' in  (q, r div scale) )
(* From Knuth Vol II, 4.3.1, but without opt. in step D3 *)

let rec divmod = function (m, []) -> raise (Div) | ([], n) -> ([], []) | (d :: r, 0 :: s) -> ( let (qt, rm) = divmod (r, s) in  (qt, consd (d, rm)) ) | (m, [d]) -> ( let (qt, rm) = divmodd (m, d) in  (qt, if rm = 0 then [] else [rm]) ) | (m, n) -> ( (* >= 2 *)
(* >= base/2 *)
let ln = length n in let scale = scale (List.nth (n, ln - 1)) in let m' = muld (m, scale) in let n' = muld (n, scale) in let n1 = List.nth (n', ln - 1) in let rec divl = function [] -> ([], []) | (d :: r) -> ( let (qt, rm) = divl r in let m = consd (d, rm) in let rec msds = function ([], _) -> (0, 0) | ([d], 1) -> (0, d) | ([d2; d1], 1) -> (d1, d2) | (d :: r, i) -> msds (r, i - 1) in let (m1, m2) = msds (m, ln) in let tq = if m1 = n1 then maxDigit else 1 (divmod2 ((m1, m2), n1)) in let rec try_ (q, qn')  = try (q, subt (m, qn')) with Negative -> try_ (q - 1, subt (qn', n')) in let (q, rr) = try_ (tq, muld (n', tq)) in  (consd (q, qt), rr) ) in let (qt, rm') = divl m' in let (rm, _(*0*)
) = divmodd (rm', scale) in  (qt, rm) )
let rec cmp = function ([], []) -> Eq | (_, []) -> Gt | ([], _) -> Lt | ((i : int) :: ri, j :: rj) -> match cmp (ri, rj) with Eq -> if i = j then Eq else if i < j then Lt else Gt | c -> c
let rec exp = function (_, 0) -> one | ([], n) -> if n > 0 then zero else raise (Div) | (m, n) -> if n < 0 then zero else ( let rec expm = function 0 -> [1] | 1 -> m | i -> ( let r = expm (i div 2) in let r2 = mult (r, r) in  if i mod_ 2 = 0 then r2 else mult (r2, m) ) in  expm n )
let rec try_ n  = if n >= lgHBase then n else try_ (2 * n)
let pow2lgHBase = try_ 1
let rec log2 = function [] -> raise (Domain) | (h :: t) -> ( let rec qlog = function (x, 0) -> 0 | (x, b) -> if x >= wtoi (Word.( << ) (0x1L, itow b)) then b + qlog (wtoi (Word.( >> ) (itow x, itow b)), b div 2) else qlog (x, b div 2) in let rec loop = function (d, [], lg) -> lg + qlog (d, pow2lgHBase) | (_, h :: t, lg) -> loop (h, t, lg + lgBase) in  loop (h, t, 0) )
(* local *)

(* find maximal maxpow s.t. radix^maxpow < base 
             * basepow = radix^maxpow
             *)

let rec mkPowers radix  = ( let powers = ( let bnd = Int.quot (nbase, (~- radix)) in let rec try_ (tp, l)  = try (if tp <= bnd then try_ (radix * tp, tp :: l) else (tp :: l)) with _ -> tp :: l in  Vector.fromList (rev (try_ (radix, [1]))) ) in let maxpow = Vector.length powers - 1 in  (maxpow, Vector.sub (powers, maxpow), powers) )
let powers2 = mkPowers 2
let powers8 = mkPowers 8
let powers10 = mkPowers 10
let powers16 = mkPowers 16
let rec fmt (pow, radpow, puti) n  = ( let pad = StringCvt.padLeft '0' pow in let rec ms0 = function (0, a) -> (pad "") :: a | (i, a) -> (pad (puti i)) :: a in let rec ml (n, a)  = match divmodd (n, radpow) with ([], d) -> (puti d) :: a | (q, d) -> ml (q, ms0 (d, a)) in  concat (ml (n, [])) )
let fmt2 = fmt (1 powers2, 2 powers2, NumFormat.fmtInt StringCvt.BIN)
let fmt8 = fmt (1 powers8, 2 powers8, NumFormat.fmtInt StringCvt.OCT)
let fmt10 = fmt (1 powers10, 2 powers10, NumFormat.fmtInt StringCvt.DEC)
let fmt16 = fmt (1 powers16, 2 powers16, NumFormat.fmtInt StringCvt.HEX)
let rec scan (bound, powers, geti) getc cs  = ( let rec get (l, cs)  = if l = bound then None else match getc cs with None -> None | Some (c, cs') -> Some (c, (l + 1, cs')) in let rec loop (acc, cs)  = match geti get (0, cs) with None -> (acc, cs) | Some (0, (sh, cs')) -> loop (add (muld (acc, Vector.sub (powers, sh)), []), cs') | Some (i, (sh, cs')) -> loop (add (muld (acc, Vector.sub (powers, sh)), [i]), cs') in  match geti get (0, cs) with None -> None | Some (0, (_, cs')) -> Some (loop ([], cs')) | Some (i, (_, cs')) -> Some (loop ([i], cs')) )
let rec scan2 getc  = scan (1 powers2, 3 powers2, NumScan.scanInt StringCvt.BIN) getc
let rec scan8 getc  = scan (1 powers8, 3 powers8, NumScan.scanInt StringCvt.OCT) getc
let rec scan10 getc  = scan (1 powers10, 3 powers10, NumScan.scanInt StringCvt.DEC) getc
let rec scan16 getc  = scan (1 powers16, 3 powers16, NumScan.scanInt StringCvt.HEX) getc
 end
(* structure BigNat *)

module BN = BigNat
type sign = POS | NEG
type int = BI of <sign: sign; digits: BN.bignat>
let zero = BI {sign = POS; digits = BN.zero}
let one = BI {sign = POS; digits = BN.one}
let minus_one = BI {sign = NEG; digits = BN.one}
let rec posi digits  = BI {sign = POS; digits = digits}
let rec negi digits  = BI {sign = NEG; digits = digits}
let rec zneg = function [] -> zero | digits -> BI {sign = NEG; digits = digits}
let minNeg = valOf Int.minInt
let bigNatMinNeg = BN.addOne (BN.bignat (~- (minNeg + 1)))
let bigIntMinNeg = negi bigNatMinNeg
let rec toInt = function (BI {digits = []; _}) -> 0 | (BI {sign = POS; digits}) -> BN.int digits | (BI {sign = NEG; digits}) -> try (~- (BN.int digits)) with _ -> if digits = bigNatMinNeg then minNeg else raise (Overflow)
let rec fromInt = function 0 -> zero | i -> if i < 0 then if (i = minNeg) then bigIntMinNeg else BI {sign = NEG; digits = BN.bignat (~- i)} else BI {sign = POS; digits = BN.bignat i}
(* local *)

(* The following assumes LargeInt = Int32.
       * If IntInf is provided, it will be LargeInt and toLarge and fromLarge
       * will be the identity function.
       *)

let minNeg = valOf LargeInt.minInt
let maxDigit = LargeInt.fromInt BN.maxDigit
let nbase = LargeInt.fromInt BN.nbase
let lgBase = Word.fromInt BN.lgBase
let notNbase = Word32.notb (Word32.fromInt BN.nbase)
let rec largeNat = function (0 : LargeInt.int) -> [] | i -> ( let rec bn = function (0x0L : Word32.word) -> [] | i -> ( let rec dmbase n  = (Word32.>> (n, lgBase), Word32.andb (n, notNbase)) in let (q, r) = dmbase i in  (Word32.toInt r) :: (bn q) ) in  if i <= maxDigit then [LargeInt.toInt i] else bn (Word32.fromLargeInt i) )
let rec large = function [] -> 0 | [d] -> LargeInt.fromInt d | [d; e] -> ~- (nbase * (LargeInt.fromInt e)) + (LargeInt.fromInt d) | (d :: r) -> ~- (nbase * large r) + (LargeInt.fromInt d)
let bigNatMinNeg = BN.addOne (largeNat (~- (minNeg + 1)))
let bigIntMinNeg = negi bigNatMinNeg
let rec toLarge = function (BI {digits = []; _}) -> 0 | (BI {sign = POS; digits}) -> large digits | (BI {sign = NEG; digits}) -> try (~- (large digits)) with _ -> if digits = bigNatMinNeg then minNeg else raise (Overflow)
let rec fromLarge = function 0 -> zero | i -> if i < 0 then if (i = minNeg) then bigIntMinNeg else BI {sign = NEG; digits = largeNat (~- i)} else BI {sign = POS; digits = largeNat i}
(* local *)

let rec negSign = function POS -> NEG | NEG -> POS
let rec subtNat = function (m, []) -> {sign = POS; digits = m} | ([], n) -> {sign = NEG; digits = n} | (m, n) -> try ({sign = POS; digits = BN.subt (m, n)}) with BN.Negative -> ({sign = NEG; digits = BN.subt (n, m)})
let precision = None
let minInt = None
let maxInt = None
let rec ( ~- ) = function (i) -> i | (BI {sign = POS; digits}) -> BI {sign = NEG; digits = digits} | (BI {sign = NEG; digits}) -> BI {sign = POS; digits = digits}
let rec ( + ) = assert false
let rec ( - ) = assert false (* TODO CHECK DEFS *)
let rec ( / ) = assert false 
let rec quotrem = function (BI {sign = POS; digits = m}, BI {sign = POS; digits = n}) -> (match BN.divmod (m, n) with (q, r) -> (posi q, posi r)) | (BI {sign = POS; digits = m}, BI {sign = NEG; digits = n}) -> (match BN.divmod (m, n) with (q, r) -> (zneg q, posi r)) | (BI {sign = NEG; digits = m}, BI {sign = POS; digits = n}) -> (match BN.divmod (m, n) with (q, r) -> (zneg q, zneg r)) | (BI {sign = NEG; digits = m}, BI {sign = NEG; digits = n}) -> (match BN.divmod (m, n) with (q, r) -> (posi q, zneg r))
let rec divmod = function (BI {sign = POS; digits = m}, BI {sign = POS; digits = n}) -> (match BN.divmod (m, n) with (q, r) -> (posi q, posi r)) | (BI {sign = POS; digits = []}, BI {sign = NEG; digits = n}) -> (zero, zero) | (BI {sign = POS; digits = m}, BI {sign = NEG; digits = n}) -> ( let (q, r) = BN.divmod (BN.subtOne m, n) in  (negi (BN.addOne q), zneg (BN.subtOne (BN.subt (n, r)))) ) | (BI {sign = NEG; digits = m}, BI {sign = POS; digits = n}) -> ( let (q, r) = BN.divmod (BN.subtOne m, n) in  (negi (BN.addOne q), posi (BN.subtOne (BN.subt (n, r)))) ) | (BI {sign = NEG; digits = m}, BI {sign = NEG; digits = n}) -> (match BN.divmod (m, n) with (q, r) -> (posi q, zneg r))
let rec  div arg  = 1 (divmod arg)
let rec  mod_ arg  = 2 (divmod arg)
let rec  quot arg  = 1 (quotrem arg)
let rec  rem arg  = 2 (quotrem arg)
let rec compare = function (BI {sign = NEG; _}, BI {sign = POS; _}) -> Lt | (BI {sign = POS; _}, BI {sign = NEG; _}) -> Gt | (BI {sign = POS; digits = d}, BI {sign = POS; digits = d'}) -> BN.cmp (d, d') | (BI {sign = NEG; digits = d}, BI {sign = NEG; digits = d'}) -> BN.cmp (d', d)
let rec  < arg  = match compare arg with Lt -> true | _ -> false
let rec  > arg  = match compare arg with Gt -> true | _ -> false
let rec  <= arg  = match compare arg with Gt -> false | _ -> true
let rec  >= arg  = match compare arg with Lt -> false | _ -> true
let rec abs = function (BI {sign = NEG; digits}) -> BI {sign = POS; digits = digits} | i -> i
let rec max arg  = match compare arg with Gt -> 1 arg | _ -> 2 arg
let rec min arg  = match compare arg with Lt -> 1 arg | _ -> 2 arg
let rec sign = function (BI {sign = NEG; _}) -> -1 | (BI {digits = []; _}) -> 0 | _ -> 1
let rec sameSign (i, j)  = sign i = sign j
let rec fmt' fmtFn i  = match i with (BI {digits = []; _}) -> "0" | (BI {sign = NEG; digits}) -> "~" ^ (fmtFn digits) | (BI {sign = POS; digits}) -> fmtFn digits
let rec fmt = function StringCvt.BIN -> fmt' (BN.fmt2) | StringCvt.OCT -> fmt' (BN.fmt8) | StringCvt.DEC -> fmt' (BN.fmt10) | StringCvt.HEX -> fmt' (BN.fmt16)
let toString = fmt StringCvt.DEC
let rec scan' scanFn getc cs  = ( let cs' = NumScan.skipWS getc cs in let rec cvt = function (None, _) -> None | (Some (i, cs), wr) -> Some (wr i, cs) in  match (getc cs') with (Some ('~', cs'')) -> cvt (scanFn getc cs'', zneg) | (Some ('-', cs'')) -> cvt (scanFn getc cs'', zneg) | (Some ('+', cs'')) -> cvt (scanFn getc cs'', posi) | (Some _) -> cvt (scanFn getc cs', posi) | None -> None(* end case *)
 )
let rec scan = function StringCvt.BIN -> scan' (BN.scan2) | StringCvt.OCT -> scan' (BN.scan8) | StringCvt.DEC -> scan' (BN.scan10) | StringCvt.HEX -> scan' (BN.scan16)
let rec fromString s  = StringCvt.scanString (scan StringCvt.DEC) s
let rec pow = function (_, 0) -> one | (BI {sign = POS; digits}, n) -> posi (BN.exp (digits, n)) | (BI {sign = NEG; digits}, n) -> if Int.mod_ (n, 2) = 0 then posi (BN.exp (digits, n)) else zneg (BN.exp (digits, n))
let rec log2 = function (BI {sign = POS; digits}) -> BN.log2 digits | _ -> raise (Domain)
 end

(* structure IntInf *)

