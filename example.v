From Stdlib Require Import ZArith List String Lia.
Require Import little_w_string parser.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope a_scope.
Import str AB A D L syntax.

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

