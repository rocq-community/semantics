%{
(* This code is actually taken into account after the token declarations.
   so no module renaming is taken into account when declaring the tokens. *)
  open String
  open Str_little
  open Str
(* Beware that module Patched_interp should not be opened, to avoid that
   Patched_interp.Z hides the Z module from zarith. *)


(* Making Coq data. *)

let big_int2 = Z.of_int 2

let z_of_big_int n =
    let rec f n = if Z.equal n Z.one then Patched_interp.XH
                else let q,r = Z.div_rem n big_int2 in
                  if Z.equal r Z.one then Patched_interp.XI(f q)
                  else Patched_interp.XO(f q) in
  if Z.equal n Z.zero then Patched_interp.Z0 else Patched_interp.Zpos(f n)

let p a b = Patched_interp.Pair(a, b)
let c a b = Patched_interp.Cons(a, b)
let nil = Patched_interp.Nil

let rec mk_precs l i =
 match l with [] -> i | a :: tl -> Patched_interp.Prec(a, mk_precs tl i)

%}
%token VARIABLES IN END WHILE DO DONE ASSIGN PLUS MINUS COMMA CONJ BANG
%token SEMICOLON OPEN CLOSE BOPEN BCLOSE SKIP LT SOPEN SCLOSE MINFTY PINFTY
%token <Z.t> NUM
%token <string> ID
%left PLUS
%right CONJ
%type <(string,Patched_interp.z)Patched_interp.prod Patched_interp.list*string Patched_interp.a_instr0> main
%type <string Patched_interp.a_instr0> inst
%start main main_intervals inst_with_post
%type <Patched_interp.z> num
%type <string> identifier
%type <(string,(Patched_interp.ext_Z,Patched_interp.ext_Z)Patched_interp.prod)Patched_interp.prod Patched_interp.list*string Patched_interp.a_instr0>main_intervals
%type <string Patched_interp.a_instr0*string Patched_interp.assert0> inst_with_post
%%
main : VARIABLES environment IN inst END { ($2, $4) }
;
main_intervals : VARIABLES interval_environment IN inst END  { ($2,$4) }
num : NUM { z_of_big_int $1 } | MINUS NUM {Patched_interp.Z.opp (z_of_big_int $2)}
;
identifier : ID { $1 }
;
variable_value : identifier num { p $1 $2 }
;
bound : num {Patched_interp.CZ $1} | MINFTY {Patched_interp.Minfty} | PINFTY {Patched_interp.Pinfty}
;
variable_interval : identifier bound bound {p $1 (p $2 $3)}
;
interval_environment : { nil}
| variable_interval interval_environment {c $1 $2}
;
environment : { nil }
| variable_value environment { c $1 $2 }
;
inst: elem_inst {$1}
|  elem_inst SEMICOLON inst { Patched_interp.A_sequence($1,$3) }
;
elem_inst : elem_inst0 {$1}
| SOPEN l_assert SCLOSE elem_inst {Patched_interp.Prec($2,$4)}
;

elem_inst0 : BOPEN inst BCLOSE { $2 }
|  SKIP { Patched_interp.A_skip }
|  WHILE b_exp DO inst DONE
     {match $4 with Patched_interp.Prec(a,i) -> Patched_interp.A_while($2,a, i)
         | Patched_interp.A_sequence(Patched_interp.Prec(a,i),j) ->
           Patched_interp.A_while($2, a, Patched_interp.A_sequence(i, j))
         | it -> Patched_interp.A_while($2, false_assert, it)}
|  identifier ASSIGN exp { Patched_interp.A_assign($1,$3) }
;
inst_with_post :
  elem_inst SOPEN l_assert SCLOSE {($1,$3)}
| elem_inst SEMICOLON inst_with_post
   {let a,b = $3 in Patched_interp.A_sequence($1,a), b }
;
exp: num { Patched_interp.Anum($1) }
|    identifier { Patched_interp.Avar($1) }
|    exp PLUS exp { Patched_interp.Aplus($1, $3); }
|    OPEN exp CLOSE { $2 }
;
b_exp: exp LT exp { Patched_interp.Blt($1, $3) }
;
elem_assert : b_exp {Patched_interp.A_b($1)}
|   identifier OPEN l_exp CLOSE {Patched_interp.Pred($1, $3)}
|   BANG elem_assert {Patched_interp.A_not($2)}
;
l_assert : elem_assert {$1}
| elem_assert CONJ l_assert {Patched_interp.A_conj($1,$3)}
;
l_exp : l_exp1 {$1}
| {Patched_interp.Nil}
;
l_exp1 : exp { Patched_interp.Cons($1, Patched_interp.Nil)}
| exp COMMA l_exp1 {Patched_interp.Cons($1, $3)}
;
%%
