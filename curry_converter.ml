(* Automated Currying Converter Script

   This script converts uncurried functions to curried form.
   It handles the most common patterns:
   1. fun (x, y) -> body  =>  fun x y -> body
   2. fun (x, y, z) -> body  =>  fun x y z -> body
   3. function (x, y) -> body  =>  fun x y -> body  (when simple)
   4. let f (x, y) = body  =>  let f x y = body

   Complex patterns requiring manual review:
   - Nested tuples: fun (x, (y, z)) -> ...
   - Pattern matches with tuples: function (0, 0) -> ... | (x, y) -> ...
   - Partial applications that rely on tuple structure
*)

open Str

let tuple_param_regex = regexp "\\((\\([a-zA-Z_][a-zA-Z0-9_']*\\),[ ]*\\([a-zA-Z_][a-zA-Z0-9_']*\\))\\)"
let triple_param_regex = regexp "\\((\\([a-zA-Z_][a-zA-Z0-9_']*\\),[ ]*\\([a-zA-Z_][a-zA-Z0-9_']*\\),[ ]*\\([a-zA-Z_][a-zA-Z0-9_']*\\))\\)"

(* Convert: fun (x, y) -> body  to  fun x y -> body *)
let convert_fun_tuple line =
  (* First try triple *)
  let line = global_replace
    (regexp "fun *(\\([a-zA-Z_][a-zA-Z0-9_']*\\), *\\([a-zA-Z_][a-zA-Z0-9_']*\\), *\\([a-zA-Z_][a-zA-Z0-9_']*\\)) *->")
    "fun \\1 \\2 \\3 ->"
    line
  in
  (* Then try double *)
  global_replace
    (regexp "fun *(\\([a-zA-Z_][a-zA-Z0-9_']*\\), *\\([a-zA-Z_][a-zA-Z0-9_']*\\)) *->")
    "fun \\1 \\2 ->"
    line

(* Convert: let rec f (x, y) = body  to  let rec f x y = body *)
let convert_let_tuple line =
  (* First try triple *)
  let line = global_replace
    (regexp "let +rec +\\([a-zA-Z_][a-zA-Z0-9_']*\\) *(\\([a-zA-Z_][a-zA-Z0-9_']*\\), *\\([a-zA-Z_][a-zA-Z0-9_']*\\), *\\([a-zA-Z_][a-zA-Z0-9_']*\\)) *=")
    "let rec \\1 \\2 \\3 \\4 ="
    line
  in
  (* Then try double *)
  let line = global_replace
    (regexp "let +rec +\\([a-zA-Z_][a-zA-Z0-9_']*\\) *(\\([a-zA-Z_][a-zA-Z0-9_']*\\), *\\([a-zA-Z_][a-zA-Z0-9_']*\\)) *=")
    "let rec \\1 \\2 \\3 ="
    line
  in
  (* Try let without rec *)
  let line = global_replace
    (regexp "let +\\([a-zA-Z_][a-zA-Z0-9_']*\\) *(\\([a-zA-Z_][a-zA-Z0-9_']*\\), *\\([a-zA-Z_][a-zA-Z0-9_']*\\), *\\([a-zA-Z_][a-zA-Z0-9_']*\\)) *=")
    "let \\1 \\2 \\3 \\4 ="
    line
  in
  global_replace
    (regexp "let +\\([a-zA-Z_][a-zA-Z0-9_']*\\) *(\\([a-zA-Z_][a-zA-Z0-9_']*\\), *\\([a-zA-Z_][a-zA-Z0-9_']*\\)) *=")
    "let \\1 \\2 \\3 ="
    line

let convert_line line =
  let line = convert_fun_tuple line in
  let line = convert_let_tuple line in
  line

let process_file filename =
  let ic = open_in filename in
  let oc = open_out (filename ^ ".curried") in
  try
    while true do
      let line = input_line ic in
      let converted = convert_line line in
      output_string oc converted;
      output_char oc '\n'
    done
  with End_of_file ->
    close_in ic;
    close_out oc;
    Unix.rename (filename ^ ".curried") filename

let () =
  let files = Sys.argv in
  Array.iteri (fun i f ->
    if i > 0 then (
      Printf.printf "Converting %s...\n%!" f;
      process_file f
    )
  ) files
