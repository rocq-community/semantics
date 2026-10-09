From Stdlib Require Import ZArith List String Lia.
Require Import little_w_string parser.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope a_scope.
Import str AB A D L syntax denot.

(* Executing sample programs with the small step functional description. *)

(* The parser only produces annotated programs, and while loops in *)
(* annotated programs have to carry an invariant.  Here we put an
   invariant, but is discarded by the un_annot function. *)
Definition sum_1_10 := Eval vm_compute in un_annot (parse_instr'
  "x := 0;
   y := 0;
   while x < 10 do [le(x, 10)]
    x := x + 1; y := x + y
   done").

(* One should always check that the parser returned something meaningful.
  This parse has no error message, and produces an empty program if parsing
  failed. *)
Print sum_1_10.

(* This is an example of computation of a program, with 100 steps of
  maximal execution.  The result is of type option (env * instr).
  If the result is None, computation failed.  This is usually caused by
  the fact that the environment does not contain pairs for all variables
  used in the program.
  If the result is Some (e, i), then i is the instruction that describes
  the work that remains to be done, and e is the current environment
  describe the values of all the variables in the program.  If the number
  of steps given as argument is high enough, then execution is complete and
  i is the empty intruction called skip.  In this case,  the number of steps
  is high enough. *)
Compute f_star 100 (("x", 0) :: ("y", 0) :: nil)
  sum_1_10.

(* This is an example of execution that is not complete. *)
Compute f_star 50 (("x", 0) :: ("y", 0) :: nil)
  sum_1_10.

(* f_star is nice, but it has the drawback that the number of steps is
  described using a natural number,  not convenient when large numbers
  of steps are required, which comes fast because steps are very small. *)

(* The presentation also provides another approach to execution, where
  fuel is consumed only when unrolling a loop.  On the other hand, this
  approach relies on a function called Tarski_fix, which cannot be
  executed in Rocq, because it is a potentially non-terminating function.
  
  The following function is an alternative to Tarski_fix, which is
  "partially" executable because it simulates Tarski_fix for a certain
  number of steps, before falling back on Tarski_fix. *)
Definition tarski_fix_z (z : Z) {A B : Type}
  (F : (A -> option B) -> A -> option B) : A -> option B  :=
  Z.iter  z F (Tarski_fix F).

(* When using Tarski_fix_z with a numeric parameter that is too small
  the results is too big and may break development environments like
  visual studio (with vsrocq).   I advise not to perform the following
  computation with a parameter 10 to tarski_fix_z. *)
Compute  ds_abstract (@tarski_fix_z 100)
        sum_1_10 (("x", 0) :: ("y", 0) :: nil).

(* With the same infrastructure, it is also possible to compute safely,
  where the value None is returned to express that not enough fuel was
  given for the execution. *)
Definition limited_unroll (z : Z) {A B : Type}
  (F : (A -> option B) -> A -> option B) : A -> option B :=
  Z.iter z F (fun _ => None).

(* With unlimited unroll, the result is Some only if one
  gave enough fuel for the execution of all loops*)
Compute ds_abstract (@limited_unroll 100)
        sum_1_10 (("x", 0) :: ("y", 0) :: nil).

(* We see that 10 is not enough *)
Compute ds_abstract (@limited_unroll 10)
        sum_1_10 (("x", 0) :: ("y", 0) :: nil).

(* We see that 10 is not enough, but 11 is enough *)
Compute ds_abstract (@limited_unroll 11)
        sum_1_10 (("x", 0) :: ("y", 0) :: nil).

(* The function Tarski_fix cannot be described in Rocq, but it can be 
  described in Ocaml.  The extracted code uses ds_abstract and Tarski_fix
  to compute programs to their end, without the need to produce fuel, but
  with the drawback that non-terminating programs do compute forever, or
  terminate in execution errors (mostly stack-overflow). *)

Definition le_list :=
  fun l =>
    match l with n1::n2::nil => n1 <= n2 | _ => False end.

Definition pp :=
  fun l =>
    match l with n1::n2::nil => 2*n1=n2*(n2+1) | _ => False end.

Definition ex_m := (("le", le_list)::("pp",pp)::nil).

Lemma hyp_both_side :
  forall a b c d e, a = b -> b*c+d = a*c+e -> d=e.
Proof.
intros a b c d e H H0; subst a; apply Zplus_reg_l  with (b*c); auto.
Qed.

(* slow version that relies on parsing

Example ex1 : forall r2 n g,
  exec (("x",0)::("y",0)::("n",n)::nil)
         (un_annot (parse_instr'
           "while x < n do [le(x,n)/\pp(y,x)]
              x:=x+1; y:=x+y
            done")) r2 ->
  0 <= n ->
  2*"y"@[r2,g]="n"@[r2,g]*("n"@[r2,g]+1).
Proof.
parse_it; intros r2 n g Hex Hn.
let a := eval vm_compute in (parse_assert' "pp(y,n)") in
change (i_a ex_m (e_to_f g r2) a).

apply vcg_sound with (2:=Hex).
clear; unfold ex_m; compute_vcg.
unfold ex_m; compute_vcg; unfold le_list, pp.
clear; intros g;
  generalize (g "x")(g "y")(g "n"); intros x y n.
list_conj.
intros; assert (x = n) by lia; subst x; intuition.
intros [H1 [H2 H3]]; split;[lia|idtac].
apply hyp_both_side with (c:=1) (1:= H3); ring.
split; [exact Hn| vm_compute; trivial].
Qed.

*)

Example ex2 : forall r2 n g,
  exec (("x",0)::("y",0)::("n",n)::nil)
         (un_annot (a_while (blt (avar "x")(avar "n"))
                       (a_conj (pred "le" (avar "x"::avar "n"::nil))
                         (pred "pp" (avar "y"::avar "x"::nil)))
                       (a_sequence (a_assign "x" (aplus (avar "x")(anum 1)))
                         (a_assign "y" (aplus (avar "x")(avar "y")))))) r2 ->
  0 <= n ->
  2*(r2@g)"y"=(r2@g)"n"*((r2@g)"n"+1).
Proof.
parse_it; intros r2 n g Hex Hn.
change (i_a ex_m (r2@g) (pred "pp" (avar "y"::avar "n"::nil))).

apply vcg_sound with (2:=Hex).
clear; unfold ex_m; compute_vcg.

lazy beta iota zeta delta [
  vcg valid_l i_lc i_c i_a f_p
  str.string_dec string_dec string_rec string_rect sumbool_rec
  sumbool_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect 
  Bool.bool_dec  bool_rec bool_rect eq_rec_r eq_rec eq_rect sym_eq lf'
  af' bf' pc mark List.app a_subst subst l_subst].
Open Scope string_scope.


unfold ex_m; simpl string_dec; simpl af'; compute_vcg; unfold le_list, pp.
clear; intros g;
  generalize (g "x")(g "y")(g "n"); intros x y n.
list_conj.

simpl string_dec; compute_vcg.
unfold eq_rec_r.
unfold eq_rec.
unfold eq_rect.
unfold sym_eq.

intros; assert (x = n) by lia; subst x; intuition.
intros [H1 [H2 H3]]; split;[lia|idtac].
apply hyp_both_side with (c:=1) (1:= H3); ring.
split; [exact Hn| vm_compute; trivial].
Qed.

