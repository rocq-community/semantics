module Big_int = Z
open Parse_little
open Interp
open Str_little
open Str

(* Recuperating the certified code from the file Interp. *)
(* Str_little.Str is a module providing the string operations, based on
   ocaml native strings. *)
module D = Interp.Rocq_denot(Str_little.Str)
module A = Interp.Rocq_ax(Str_little.Str)
module B = Interp.Rocq_ab(Str_little.Str)
open B
open A
open D
open L

(* Displaying the results: first displaying integers. *)

let two_big_int = Big_int.of_int 2

let rec big_int_of_positive = function
  Interp.XH -> Big_int.one
| Interp.XI p -> Big_int.succ (Big_int.mul two_big_int (big_int_of_positive p))
| Interp.XO p -> Big_int.mul two_big_int (big_int_of_positive p)

let bigint_of_z = function
  Interp.Z0 -> Big_int.zero
| Interp.Zpos x -> big_int_of_positive x
| Interp.Zneg x -> Big_int.neg (big_int_of_positive x)
  
let rec display_result = function
  Interp.Nil -> ()
| Interp.Cons(Interp.Pair(s, v), tl) ->
  print_string (s ^ " " ^ Big_int.to_string (bigint_of_z v) ^ "\n");
  display_result tl

(* Displaying assertions *)

let rec string_of_expr = function
  Interp.Avar s -> s
| Interp.Anum n -> Big_int.to_string (bigint_of_z n)
| Interp.Aplus(e1, e2) -> string_of_expr e1 ^ "+" ^ string_of_expr e2

let string_of_bexpr (Interp.Blt(e1, e2)) =
  string_of_expr e1 ^ "<" ^ string_of_expr e2

let rec interp_fold_left f v = function
  Interp.Nil -> v
| Interp.Cons(e,l) -> interp_fold_left f (f v e) l

let rec string_of_assert = function
  Interp.A_b b -> string_of_bexpr b
| Interp.A_not a -> "!" ^ string_of_assert a
| Interp.Pred(s, l) -> s ^ "(" ^
  (match l with
    Interp.Nil -> ""
  | Interp.Cons(e, l) -> 
    (interp_fold_left
      (fun s e -> s ^ ", " ^ string_of_expr e)
      (string_of_expr e)) l) ^ ")"
| Interp.A_conj(e1, e2) -> string_of_assert e1 ^ "/\\" ^ string_of_assert e2

let string_of_condition = function
  Interp.C_imp(a1,a2) -> string_of_assert a1 ^ " -> " ^ string_of_assert a2

let rec string_of_a_instr = function
  Interp.A_assign(x, e) -> (x ^ ":=" ^ string_of_expr e)
| Interp.A_while(b, a, i) ->
   "while " ^ string_of_bexpr b ^ " do\n[" ^
   string_of_assert a ^ "]\n" ^
   string_of_a_instr i ^
   "\ndone"
| Interp.A_skip -> "skip"
| Interp.A_sequence(i1, i2) ->
  string_of_a_instr i1 ^ ";\n" ^ string_of_a_instr i2
| Interp.Prec(a,i) ->
  "[" ^ string_of_assert a ^ "]\n" ^ string_of_a_instr i

(* The interpreter *)
let process_program = function
    (l, i) ->
    (match ds (un_annot i) l with
       Interp.Some(l) -> display_result l
     | _ -> failwith "execution failed")

(* display of conditions, for Coq. *)

module SS = Set.Make(struct type t = string let compare = String.compare end)
open SS

let rec collect_expr set = function
  Interp.Avar s -> add s set
| Interp.Anum n -> set
| Interp.Aplus(e1, e2) -> collect_expr (collect_expr set e1) e2

let rec collect_expr_list set = function
  Interp.Nil -> set
| Interp.Cons(e,l) -> collect_expr (collect_expr_list set l) e

let collect_bexpr set (Interp.Blt(e1,e2)) =
  collect_expr (collect_expr set e1) e2

let rec collect_assert set = function
  Interp.A_b b -> collect_bexpr set b
| Interp.A_not a -> collect_assert set a
| Interp.Pred(s, l) -> collect_expr_list set l
| Interp.A_conj(a1,a2) -> collect_assert (collect_assert set a1) a2

let rec coq_expr = function
  Interp.Avar s -> s
| Interp.Anum n -> Big_int.to_string (bigint_of_z n)
| Interp.Aplus(e1,e2) -> coq_expr e1 ^ "+" ^ coq_expr e2

let coq_bexpr (Interp.Blt(e1,e2)) = coq_expr e1 ^ " < " ^ coq_expr e2

let rec coq_plain_assert = function
  Interp.A_b b -> coq_bexpr b
| Interp.A_not a -> "~(" ^ coq_plain_assert a ^ ")"
| Interp.A_conj(a1,a2) -> "(" ^ coq_plain_assert a1 ^ ") /\\ (" ^
                       coq_plain_assert a2 ^ ")"
| Interp.Pred(s, l) -> 
  (interp_fold_left
   (fun (s:string) (e:Str.aexpr) -> 
    s ^ " " ^ 
    (match e with Interp.Aplus(_,_) -> "(" ^ coq_expr e ^ ")"
        | _ -> coq_expr e))
   s l)

let coq_string_of_condition (Interp.C_imp(a1,a2)) =
  let names = collect_assert (collect_assert empty a1) a2 in
  "forall " ^
  fold (fun name s -> name ^ " " ^ s) names 
     (", (" ^ coq_plain_assert a1 ^ ") -> (" ^ coq_plain_assert a2 ^ ")");;

(* This function manages the callode to the certified abstract interpreter
  and displays the result. the argument vars is an abstract environment
  binding variables with intervals, the result is displayed as an annotated
  program with a post-condition. *)

let process_abstract (vars, inst) =
  match B.abstract_i (un_annot inst) vars with
     Interp.Pair(i, opt_e) ->
     print_string(string_of_a_instr i ^ "\n[" ^
                  string_of_assert (B.to_a' opt_e) ^ "]\n");;

(* The verification generator. *)
(* The first argument is a boolean, which indicates whether we want the
  output in Coq compatible syntax. *)

let process_vcg for_coq (inst, post) = 
  let count = ref 0 in
  let conds = vcg inst post in 
     print_string 
      (interp_fold_left
          (fun s c -> count := !count+1;
               s^"\n\n" ^ 
               (if for_coq
                then "Lemma cond" ^ (string_of_int !count) ^ " : " ^
                     coq_string_of_condition c ^ "."
                else string_of_condition c)) "" conds);
     print_string "\n";;

(* syntax error reporting.  Whatever the entry point, we always want to
  catch Parse_error exceptions and use the line counter managed in the
  lexical analyser to indicate where the syntax error was detected. *)

let parse_tool f = 
   try f Llex.token (Lexing.from_channel stdin)
   with Parsing.Parse_error ->
     (output_string stderr
        ("Parse error detected around line " ^
                                  (string_of_int (!Llex.count+1)) ^ "\n");
        exit 1);;
   
(* the main toplevel *)
try
if Array.length(Sys.argv) = 2 then
 if Sys.argv.(1) = "-interpreter" then
   let (vars, inst) = parse_tool main in
   process_program (vars, inst)
 else if Sys.argv.(1) = "-vcg" then
   let (inst,post) = parse_tool inst_with_post in
   process_vcg false (inst,post)
 else if Sys.argv.(1) = "-vcg-coq" then
   let (inst,post) = parse_tool inst_with_post in
   process_vcg true (inst,post)
 else if Sys.argv.(1) = "-static-analysis" then
   let (vars, inst) = parse_tool main_intervals in
   process_abstract(vars, inst)
 else
   failwith "command line argument parsing" 
else
  failwith "command line argument parsing"
with Failure _ ->
 failwith ("usage: " ^ 
               Sys.argv.(0) ^ 
               " [-interpreter | -vcg | -vcg-coq | -static-analysis] < file")
