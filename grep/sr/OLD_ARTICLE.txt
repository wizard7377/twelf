The languages compared are Moscow ML (Mosml) and Objective ML (Ocaml)
but the comparison may be applicable to other dialects as well.

The Object Oriented features of Ocaml is intentionally not covered.

The first section is an interaction with the respective toplevel system, in
order to show the built in datatypes. The rest is just example expressions and
definitions.

Anything within <> is the author's note.


Built in datatypes
--SML---------------------------------+--ML------------------------------------
 - 3;                                 | # 3;;
 > val it = 3 : int                   | - : int = 3
--------------------------------------+----------------------------------------
 - 3.141;                             | # 3.141;;  
 > val it = 3.141 : real              | - : float = 3.141
--------------------------------------+----------------------------------------
 - "hello world";                     | # "hello world";;
 > val it = "hello world" : string    | - : string = "hello world"
--------------------------------------+----------------------------------------
 - #"J";                              | # 'J';;
 > val it = #"J" : char               | - : char = 'J'
--------------------------------------+----------------------------------------
 - true;                              | # true;;
 > val it = true : bool               | - : bool = true
--------------------------------------+----------------------------------------
 - ();                                | # ();;
 > val it = () : unit                 | - : unit = ()
--------------------------------------+----------------------------------------
 - [1,2,3];                           | # [1;2;3];;
 > val it = [1, 2, 3] : int list      | - : int list = [1; 2; 3]
--------------------------------------+----------------------------------------
 <Cannot create arrays 'on the fly',  | # [|4;5;6|];;
 use library functions instead>       | - : int array = [|4; 5; 6|]
--------------------------------------+----------------------------------------
 - #[4,5,6];                          | <Does not have vectors, use arrays
 > val it = #[4, 5, 6] : int vector   | instead>
===============================================================================

Datatypes
--SML---------------------------------+--ML------------------------------------
 - datatype color = BLUE | GREEN;     | # type color = BLUE | GREEN;;
 > datatype color                     | type color = | BLUE | GREEN
   con BLUE = BLUE : color            |
   con GREEN = GREEN : color          |
--------------------------------------+----------------------------------------
 - datatype 'a option =               | # type 'a option = NONE | SOME of 'a;;
     NONE | SOME of 'a;               | type 'a option = | NONE | SOME of 'a
 > datatype 'a option                 |
   con NONE = NONE : 'a option        |
   con SOME = fn : 'a -> 'a option    |
--------------------------------------+----------------------------------------
 - abstype exp = EXP of int * int     | <Does not exist. Use 'type' and hide 
   with <defs of primitives> end;     | with an interface file not exposing
 > abstype exp                        | representation.>
   <def names & types>                |
===============================================================================

Name bindings
--SML---------------------------------+--ML------------------------------------
 val <name> = <expr>                  | let <name> = <expr>
===============================================================================

Exceptions
--SML---------------------------------+--ML------------------------------------
 exception Hell;                      + exception Hell;;
--------------------------------------+----------------------------------------
 exception Failure of string;         | exception Failure of string;;
--------------------------------------+----------------------------------------
 raise Failure "Unkown code";         | raise(Failure "Unkown code");;
===============================================================================

References
--SML---------------------------------+--ML------------------------------------
 val c = ref 0;                       | let c = ref 0;;
--------------------------------------+----------------------------------------
 c := 1;                              | c := 1;;
--------------------------------------+----------------------------------------
 !c;                                  | !c;;
===============================================================================

Expressions
--SML---------------------------------+--ML------------------------------------
 3*(1+7);                             | 3*(1+7);;  
--------------------------------------+----------------------------------------
 1.0 + 2.0;                           | 1.0 +. 2.0;;
--------------------------------------+----------------------------------------
 true orelse false andalso false;     | true || false && false;;
--------------------------------------+----------------------------------------
 val curry =                          | let curry = 
   fn f => fn x => fn y => f(x, y);   |    function f ->
                                      |      function x ->
 fun curry f x y = f(x, y);           |        function y -> f(x, y);;
                                      | 
                                      | let curry = fun f x y -> f(x, y);;
                                      |
                                      | let curry f x y = f(x, y);;
===============================================================================

Control flow
--SML---------------------------------+--ML------------------------------------
 if 3 > 2 then "X" else "Y"           | if 3 > 2 then "X" else "Y"
--------------------------------------+----------------------------------------
 <SML requires an else-clause>        | if false then print_string "hello";;
                                      | <Note: expr has to have type unit>
--------------------------------------+----------------------------------------
 while true do print "X";             | while true do print_string "X" done;;
--------------------------------------+----------------------------------------
 <SML does not have for-loops>        | for i = 1 to 10 do
                                      |   print_string "Hello\n";;
--------------------------------------+----------------------------------------
 (print "hello";                      | (print_string "hello";
  print " world");                    |  print_string " world");;
                                      |
                                      | print_string "hello";
                                      | print_string " world";;
                                      |
                                      | begin
                                      |   print_string "hello";
                                      |   print_string " world"
                                      | end;;
                                      | <Note: it is said to be good style to
                                      |  use begin/end with loops only?> 
===============================================================================

Local bindings
--SML---------------------------------+--ML------------------------------------
 local                                | let pyt(x, y) =  
   fun sqr(x) = x * x;                |   let sqr(x) = x *. x in
 in                                   |   sqrt(sqr(x) +. sqr(y));;
   fun pyt(x, y) =                    | 
     Math.sqrt(sqr(x) + sqr(y));      | 
 end;                                 | 
--------------------------------------+----------------------------------------
 fun pyt(x, y) =                      | let pyt(x, y) = 
   let                                |   let xx = x *. x in
     val xx = x * x;                  |   let yy = y *. y in
     val yy = y * y;                  |   sqrt(xx +. yy);;
   in                                 | 
     Math.sqrt(xx + yy)               | 
   end;                               | 
===============================================================================

Recursion
--SML---------------------------------+--ML------------------------------------
 fun fib n =                          | let rec fib n =
   if n < 2 then n                    |   if n < 2 then n
   else fib(n - 1) + fib (n - 2);     |   else fib(n - 1) + fib(n - 2);;
                                      |
 val rec fib n =                      |
   if n < 2 then n                    |
   else fib(n - 1) + fib (n - 2);     |
===============================================================================

Matching
--SML---------------------------------+--ML------------------------------------
 fun getOpt(NONE, d) = d              | let getOpt = function
   | getOpt (SOME x, _) = x;          |     (NONE, d) -> d
                                      |   | (SOME x, _) -> x;;
--------------------------------------+----------------------------------------
 fun getOpt(opt, d) =                 | let getOpt(opt, d) = 
   case opt                           |   match opt 
     of NONE => d                     |     with NONE -> d
      | SOME x => x;                  |        | SOME x -> x;;
--------------------------------------+----------------------------------------
 <Guards does not exist>              | let rec fac = function
                                      |     n when n > 0 -> n * fac(n - 1)
                                      |   | _ -> raise Hell;;
===============================================================================

Records
--SML---------------------------------+--ML------------------------------------
                                      | type foo =
                                      |   {x:int; y:float; mutable s:string};;
                                      | <mutable y : xxx in records has not 
                                      | the same type as a field z : xxx ref>
--------------------------------------+----------------------------------------
                                      | let bar = {x=0; y=3.14; s=""};;
                                      | <bar has now type foo>
--------------------------------------+----------------------------------------
                                      | bar.x;;
                                      | bar.y;;
                                      | bar.s;;
--------------------------------------+----------------------------------------
                                      | bar.s <- "something";;
                                      | <bar.s updated as a side effect, since
                                      | s is declared mutable in foo>
--------------------------------------+----------------------------------------


List functions
--SML---------------------------------+--ML------------------------------------
 List.foldl op+ 0 [1,2,3];            | List.fold_left (+) [1;2;3];;
--------------------------------------+----------------------------------------
 map Math.sqrt [9.0,4.0];             | List.map sqrt [9.;4.];;
--------------------------------------+----------------------------------------
 length [3,2,1];                      | List.length [3;2;1];;
===============================================================================

String functions
--SML---------------------------------+--ML------------------------------------
 String.substring("abCD", 1, 2);      | String.sub "abCD" 1 2;;
--------------------------------------+----------------------------------------
 String.sub("abCD", 0);               | String.get "abCD" 0;;
                                      |
                                      | "abCD".[0];;
                                      | <ie: if string bound to name s: s.[0]>
--------------------------------------+----------------------------------------
 <Strings are immutable in SML>       | String.set 0 'F';;
                                      | 
                                      | "abCD".[0] <- 'F';;
                                      | <ie: if string bound to name s: 
                                      | s.[0] <- 0>
--------------------------------------+----------------------------------------
 "123" ^ "abc";                       | "123" ^ "abc";;
--------------------------------------+----------------------------------------
 size "123";                          | String.length "123";;
===============================================================================

Array functions
--SML---------------------------------+--ML------------------------------------
 Array.sub(Array.tabulate(3,          | Array.get [|0;1;2|] 2;;
    fn x => x), 2);                   |
                                      | [|0;1;2|].(2);;
                                      | <ie: if array bound to name a: a.(0)>
--------------------------------------+----------------------------------------
 Array.update(Array.tabulate(3,       | Array.set [|0;1;2|] 2 0;;
    fn x => x), 2, 0);                |
                                      | "abCD".(2) <- 0;;
                                      | <ie: if array bound to name a: 
                                      | a.(2) <- 0> 
===============================================================================

/Jens Olsson, jenso@csd.uu.se, 2000-05-02
 (Latest update: minor errors and bad spelling)
