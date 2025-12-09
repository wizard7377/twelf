
(Lib : LIB) =
struct

  nonfix upto mem ins union subset mod div
  infix ~~ -- += -= ::= @= oo ooo oooo
 
  exception Not_implemented

  (* ------------------------------------------------------------------------- *)
  (*  Booleans                                                                 *)
  (* ------------------------------------------------------------------------- *)

  let rec andalso' x y = x andalso y
  let rec orelse' x y = x orelse y

  (* ---------------------------------------------------------------------- *)
  (*  Pairs                                                                 *)
  (* ---------------------------------------------------------------------- *)

  let rec fst (x,y) = x
  let rec snd (x,y) = y

  (* -------------------------------------------------------------------------- *)
  (*  Options                                                                   *)
  (* -------------------------------------------------------------------------- *)

  let rec is_none = function NONE -> true
    | (SOME _) -> false
  let rec is_some = function NONE -> false
    | (SOME _) -> true
  let rec the = function NONE -> raise Fail "the"
    | (SOME x) -> x

  (* ------------------------------------------------------------------------- *)
  (*  Refs                                                                     *)
  (* ------------------------------------------------------------------------- *)

  let rec x += n = x := (!x) + n
  let rec x -= n = x := (!x) - n
  let rec incr x = x += 1
  let rec decr x = x -= 1
  let rec l ::= v = l := v::(!l)
  let rec l @= l' = l := (!l) @ l'

  (* -------------------------------------------------------------------------- *)
  (*  Streams                                                                   *)
  (* -------------------------------------------------------------------------- *)

  type 'a stream = SNil 
                     | SCons of unit -> 'a * 'a stream

  let rec constant_s x = SCons (fn () => (x,(constant_s x)))

  let rec ones_f n = SCons (fn () => (n,(ones_f (n + 1))))

  let nat_s = ones_f 0

  let rec nth_s = function n SNil -> raise Fail "s_nth"
    | 0 (SCons f) -> fst(f())
    | n (SCons f) -> let let (_,s') = f() in nth_s (n - 1) s' end

  let rec listof_s = function 0 _ -> []
    | n SNil -> raise Fail "listof_s"
    | n (SCons f) -> let let (v,s) = f() in v::listof_s (n - 1) s end

  (* ---------------------------------------------------------------------- *)
  (*  Functions                                                             *)
  (* ---------------------------------------------------------------------- *)

  let rec curry f x y = f(x,y)
  let rec uncurry f (x,y) = f x y
  let rec curry3 f x y z = f(x,y,z)
  let rec id x = x  
  let rec can f x = (f x;true) handle _ => false
  let rec cant f x = (f x;false) handle _ => true
  let rec can2 f x y = (f x y;true) handle _ => false
  let rec ceq x y = x = y
  let rec (f oo g) x y = f (g x y)
  let rec (f ooo g) x y z = f (g x y z)
  let rec (f oooo g) x y z w = f (g x y z w)
  let rec swap f x y = f y x
  let rec apply(f,x) = f x
  let rec repeat f n x = if n = 0 then x else repeat f (n - 1) (f x)
 
  (* -------------------------------------------------------------------------- *)
  (*  Ints                                                                      *)
  (* -------------------------------------------------------------------------- *)

  let rec max xs = foldr Int.max 0 xs
  let rec sum ns = foldr op+ 0 ns
  let rec uptoby k m n = if m > n then [] else m::(uptoby k (m + k) n)
  let upto = uncurry(uptoby 1)
  let op-- = upto
  infix --<
  let rec x --< y = x -- (y - 1)
  
  let rec pow x n = 
      case n of 
        0 => 1
      | n => if Int.mod(n,2) = 0 then 
               let let n' = pow x (Int.div(n,2)) in n' * n' end
             else x * pow x (n - 1)

  let rec log n = 
      let
        let rec log n even = 
            case n of 
              1 => (0,even)
            | n => 
              let
                let (ln,even') = log (Int.div(n,2)) even
                let even'' = even' andalso (Int.mod(n,2) = 0)
              in
                (1 + ln,even'')
              end
      in
        log n true
      end

  (* -------------------------------------------------------------------------- *)
  (*  Reals                                                                     *)
  (* -------------------------------------------------------------------------- *)

  let rec real_max xs = foldr Real.max 0.0 xs
  let rec real_sum rs = foldr op+ 0.0 rs

  (* ------------------------------------------------------------------------- *)
  (*  Order                                                                    *)
  (* ------------------------------------------------------------------------- *)

  let rec string_ord (s1:string,s2) = 
      if s1 < s2 then LESS else if s1 = s2 then EQUAL else GREATER

  let rec int_ord (s1:int,s2) = 
      if s1 < s2 then LESS else if s1 = s2 then EQUAL else GREATER

  let rec lex_ord o1 o2 ((x1,y1),(x2,y2)) =
      case o1(x1,x2) of 
        EQUAL => o2(y1,y2)
      | x => x

  let rec eq_ord(x,y) = if x = y then EQUAL else LESS

  (* ---------------------------------------------------------------------- *)
  (*  Debug                                                                 *)
  (* ---------------------------------------------------------------------- *)
 
  let rec assert b s = if b then () else raise Fail ("Assertion Failure: " ^ s)
  
  let warn = ref true
  let rec warning s = if !warn then TextIO.print ("Warning: " ^ s ^ "\n") else ()

  (* ---------------------------------------------------------------------- *)
  (*  Lists                                                                 *)
  (* ---------------------------------------------------------------------- *)

  let rec list x = [x]

  let rec cons x xs = x::xs

  (* same as foldr *)
  let rec itlist = function f [] b -> b
    | f (h::t) b -> f h (itlist f t b)

  let rec citlist f l b = itlist (curry f) l b

  let rec ith = function i [] -> raise Fail "ith: empty"
    | 0 (h::t) -> h
    | n (h::t) -> ith (n-1) t

  let rec map2 = function f [] [] -> []
    | f (h1::t1) (h2::t2) -> 
      f(h1,h2)::map2 f t1 t2
    | f _ _ -> raise Fail "map2: length mismatch"

  let rec map3 = function f [] [] [] -> []
    | f (h1::t1) (h2::t2) (h3::t3) -> f(h1,h2,h3)::map3 f t1 t2 t3
    | f _ _ _ -> raise Fail "map3: unequal lengths"

  let rec map4 = function f [] [] [] [] -> []
    | f (h1::t1) (h2::t2) (h3::t3) (h4::t4) -> f(h1,h2,h3,h4)::map4 f t1 t2 t3 t4
    | f _ _ _ _ -> raise Fail "map4: unequal lengths"

  let rec map5 = function f [] [] [] [] [] -> []
    | f (h1::t1) (h2::t2) (h3::t3) (h4::t4) (h5::t5) -> f(h1,h2,h3,h4,h5)::map5 f t1 t2 t3 t4 t5
    | f _ _ _ _ _ -> raise Fail "map5: unequal lengths"

  let rec zip l1 l2 = map2 id l1 l2
  let rec zip3 l1 l2 l3 = map3 id l1 l2 l3
  let rec zip4 l1 l2 l3 l4 = map4 id l1 l2 l3 l4
  let rec zip5 l1 l2 l3 l4 l5 = map5 id l1 l2 l3 l4 l5

  let rec unzip l = itlist (fn (h1,h2) => fn (t1,t2) => (h1::t1,h2::t2)) l ([],[])  
  let rec unzip3 l = itlist (fn (h1,h2,h3) => fn (t1,t2,t3) => (h1::t1,h2::t2,h3::t3)) l ([],[],[])  
  let rec unzip4 l = itlist (fn (h1,h2,h3,h4) => fn (t1,t2,t3,t4) => (h1::t1,h2::t2,h3::t3,h4::t4)) l ([],[],[],[])  

  let rec x ~~ y = zip x y

  let rec end_itlist = function f [] -> raise Fail "end_itlist"
    | f [x] -> x
    | f (h::t) -> f h (end_itlist f t)

  let rec end_citlist f l = end_itlist (curry f) l

  let rec itlist2 = function f [] [] b -> b
    | f (h1::t1) (h2::t2) b -> f h1 h2 (itlist2 f t1 t2 b)
    | _ _ _ _ -> raise Fail "itlist2"

  (* same as foldl *)
  let rec rev_itlist = function f [] b -> b
    | f (h::t) b -> rev_itlist f t (f h b)

  let rec rev_end_itlist = function f [] -> raise Fail "rev_end_itlist"
    | f [x] -> x
    | f (h::t) -> f (rev_end_itlist f t) h 

  let rec replicate = function x 0 -> []
    | x n -> if n > 0 then x::replicate x (n-1) else []

  let rec exists = function f [] -> false
    | f (h::t) -> f h orelse exists f t

  let rec forall = function f [] -> true
    | f (h::t) -> f h andalso forall f t

  let rec last = function [] -> raise Fail "Last"
    | (h::[]) -> h
    | (h::t) -> last t

  let rec butlast = function [] -> raise Fail "Butlast"
    | (h::[]) -> []
    | (h::t) -> h::butlast t

  let rec gen_list_eq ord l1 l2 = 
      itlist2 (fun x -> fun y -> fun z -> ord(x,y) = EQUAL andalso z) l1 l2 true 

  let rec list_eq l1 l2 = gen_list_eq eq_ord l1 l2

  let rec partition = function p [] -> ([],[])
    | p (h::t) -> 
      let 
        let (l,r) = partition p t 
      in
        if p h then (h::l,r) else (l,h::r)
      end

  let rec filter p l = fst (partition p l)

  let rec sort = function ord [] -> []
    | ord (piv::rest) -> 
      let 
        let (l,r) = partition (fun x -> ord(x,piv) = LESS) rest 
      in
        (sort ord l) @ (piv::(sort ord r))
      end

  let rec uniq = function ord (x::(t as y::_)) -> 
      let 
        let t' = uniq ord t
      in
        if ord(x,y) = EQUAL then t' else x::t'
      end
    | _ l -> l

  let rec uniq_list comp l = length (uniq comp l) = length l

  let rec split_at = function _ [] -> raise Fail "split_at: splitting empty"
    | 0 l -> ([],l)
    | n (xs as x::ys) -> 
      if n < 0 then raise Fail "split_at: arg out of range" else
      let let (ps,qs) = split_at (n-1) ys in (x::ps,qs) end

  let rec list_prefix n l = fst (split_at n l)
                        handle Fail _ => raise Fail "list_prefix"

  let rec list_slice n m l = 
      let
        let (_,r) = split_at n l
        let (l',_) = split_at m r
      in
        l'
      end

  let rec shuffle = function [] l2 -> l2
    | l1 [] -> l1
    | (h1::t1) (h2::t2) -> h1::h2::shuffle t1 t2

  let rec find_index p =
      let 
        let rec ind = function n [] -> NONE
          | n (h::t) -> if p h then SOME n else ind (n + 1) t 
      in
        ind 0
      end

  let rec index x l = find_index (ceq x) l 

  let rec find_last_index p l = 
      let
        let n = length l
        let l' = rev l
      in
        case find_index p l' of 
          SOME n' => SOME(n - n' - 1)
        | NONE => NONE
      end

  let rec last_index x l = find_last_index (ceq x) l

  let rec flatten l = itlist (curry op@) l []

  let rec chop_list = function 0 l -> ([],l)
    | n l -> 
      let let (l1,l2) = chop_list (n-1) (tl l) in (hd l::l1,l2) end
        handle _ => raise Fail "chop_list"

  let rec list_to_string f l = 
      let
        let l' = map f l
      in
        itlist (fun x -> fun y -> x ^ "," ^ y) ("["::l'@["]"]) ""
      end

  let rec remove = function p [] -> raise Fail "remove"
    | p (h::t) -> 
      if p h then (h,t) else
      let let (y,n) = remove p t in (y,h::n) end

  let rec do_list = function f [] -> ()
    | f (h::t) -> (f h; do_list f t)

  let rec exn_index = function f l -> 
      let
        let rec exn_index f [] n = NONE
          | f (h::t) n -> if can f h then exn_index f t (n + 1) else SOME n
      in
        exn_index f l 0
      end

  (* ------------------------------------------------------------------------- *)
  (*  Lists as Sets                                                            *)
  (* ------------------------------------------------------------------------- *)

  let rec gen_setify ord s = uniq ord (sort ord s)
  let rec setify s = gen_setify eq_ord s

  let rec gen_mem = function ord x [] -> false
    | ord x (h::t) -> if ord(x,h) = EQUAL then true else gen_mem ord x t

  let rec mem x l = gen_mem eq_ord x l

  let rec insert x l = if mem x l then l else x::l

  let rec gen_disjoint ord l1 l2 = forall (fun x -> not (gen_mem ord x l2)) l1

  let rec disjoint l = gen_disjoint eq_ord l

  let rec gen_pairwise_disjoint = function p [] -> true
    | p (h::t) -> 
      forall (gen_disjoint p h) t andalso gen_pairwise_disjoint p t

  let rec pairwise_disjoint t = gen_pairwise_disjoint eq_ord t
 
  let rec gen_set_eq ord l1 l2 = gen_list_eq ord (gen_setify ord l1) (gen_setify ord l2)

  let rec diff = function [] l -> []
    | (h::t) l -> if mem h l then diff t l else h::diff t l  

  let rec union l1 l2 = itlist insert l1 l2

  let rec unions l = itlist union l []

  let rec intersect l1 l2 = filter (fun x -> mem x l2) l1

  let rec subtract l1 l2 = filter (fun x -> not (mem x l2)) l1

  let rec subset l1 l2 = forall (fun t -> mem t l2) l1

  let rec set_eq l1 l2 = subset l1 l2 andalso subset l2 l1

  (* ------------------------------------------------------------------------- *)
  (*  Assoc lists                                                              *)
  (* ------------------------------------------------------------------------- *)

  let rec find = function p [] -> NONE
    | p (h::t) -> if p h then SOME h else find p t;;

  let rec assoc x l = 
      case find (fun p -> fst p = x) l of
        SOME (x,y) => SOME y 
      | NONE => NONE

  let rec rev_assoc x l = 
      case find (fun p -> snd p = x) l of
        SOME (x,y) => SOME x
      | NONE => NONE

  (* ------------------------------------------------------------------------- *)
  (*  Strings                                                                  *)
  (* ------------------------------------------------------------------------- *)

  let rec char_max c1 c2 = if Char.ord c1 < Char.ord c2 then c1 else c2

  let rec string_lt (x:string) y = x < y

  let rec collect l = itlist (curry op^)  l ""

  let rec commas n = replicate "," n

  let rec shuffle_commas l = shuffle l (commas (length l - 1))

  let rec semis n = replicate ";" n

  let rec parenify x = collect ["(",x,")"]

  let rec postfix n s = substring(s,size s - n, n)

  let numeric_chars = "0123456789"
  let lowercase_chars = "abcdefghijklmnopqrstuvwxyz"
  let uppercase_chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  let alpha_chars = lowercase_chars ^ uppercase_chars
  let alphanum_chars = alpha_chars ^ numeric_chars
  let word_sym_chars = "_'"
  let word_chars = alphanum_chars ^ word_sym_chars

  let explode = String.explode

  local 
    let rec is_legal u s = forall (fun x -> mem x (explode u)) (explode s)
  in
    let is_numeric = is_legal numeric_chars
    let is_lower = is_legal lowercase_chars
    let is_upper = is_legal uppercase_chars
    let is_alpha = is_legal alpha_chars
    let is_alnum = is_legal alphanum_chars 
    let is_word_sym = is_legal word_sym_chars
    let is_word = is_legal word_chars
  end

  let to_lower = String.translate (Char.toString o Char.toLower)
  let to_upper = String.translate (Char.toString o Char.toUpper)
  
  let rec capitalize s = 
      case map Char.toString (explode s) of
        [] => ""
      | h::t => concat ([to_upper h] @ (map to_lower t))

  let newline = Char.toString #"\n"

  let rec ends_with s e = 
      substring(s,size s - size e,size e) = e
      handle _ => false

  let rec starts_with s e = 
      substring(s,0,size e) = e
      handle _ => false

  (* abc.def.ghi -> (abc,def.ghi) *)
  let rec strip_path c s =
      let
        let n = case index c (String.explode s) of
                  SOME x => x
                | NONE => raise Fail "strip_path"
        let m = substring(s,0,n)
        let m' = substring(s,n+1,size s - n - 1)
      in
        (m,m')
      end

  (* abc.def.ghi -> (abc.def,ghi) *)
  let rec rev_strip_path c s =
      let
        let no = last_index c (String.explode s)
        let n = case no of SOME x => x | NONE => raise Fail "rev_strip_path"
        let m = substring(s,0,n)
        let m' = substring(s,n+1,size s - n - 1)
      in
        (m,m')
      end

  (* ------------------------------------------------------------------------- *)
  (*  Options                                                                  *)
  (* ------------------------------------------------------------------------- *)

  let rec the = function (SOME x) -> x
    | _ -> raise Fail "the"

  let rec is_some = function (SOME _) -> true
    | _ -> false

  let rec is_none = function NONE -> true
    | _ -> false

  let rec list_of_opt_list = function [] -> []
    | (NONE::t) -> list_of_opt_list t
    | (SOME x::t) -> x::list_of_opt_list t

  let rec get_opt = function (SOME x) _ -> x
    | NONE err -> raise Fail err

  let rec get_list = function (SOME l) -> l
    | NONE -> []

  let rec conv_opt = function f (SOME l) -> SOME (f l)
    | f NONE -> NONE

  (* ------------------------------------------------------------------------- *)
  (*  Timing                                                                   *)
  (* ------------------------------------------------------------------------- *)

  let rec time f x = 
      let
        let timer = Timer.startCPUTimer()
      in
        let
          let res = f x 
          let time = Timer.checkCPUTimer timer
          let _ = print ("CPU time (user): " ^ Time.toString (#usr time))
        in
          res
        end
          handle e => 
                 let
                   let time = Timer.checkCPUTimer timer
                 in
                   print ("Failed after (user) CUP time of " ^ Time.toString (#usr time));
                   raise e
                 end

      end

  (* ------------------------------------------------------------------------- *)
  (*  IO                                                                       *)
  (* ------------------------------------------------------------------------- *)

  let rec printl s = print (s ^ "\n")

  let rec read_file file = 
      let
        let f = TextIO.openIn file
        let s = TextIO.inputAll f
        let _ = TextIO.closeIn f
      in
        s
      end

  let rec write_file file s = 
      let
        let f = TextIO.openOut file
        let _ = TextIO.output(f,s)
        let _ = TextIO.closeOut f
      in
        ()
      end

  let rec write_file_append file s = 
      let
        let f = TextIO.openAppend file
        let _ = TextIO.output(f,s)
        let _ = TextIO.closeOut f
      in
        ()
      end

  let rec all_dir_files dir = 
      let
        let str = OS.FileSys.openDir dir
        let fs = ref []
        let f = ref (OS.FileSys.readDir str)
      in
        (while !f <> NONE do
          (fs ::= the (!f);
           f := OS.FileSys.readDir str));
        !fs
      end


end
