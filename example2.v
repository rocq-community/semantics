From Stdlib Require Import ZArith List String Lia.
Require Import little_w_string parser.
Open Scope Z_scope.
Import AB A D L.
Open Scope a_scope.

Definition le_list :=
  fun l => match l with n1::n2::nil => n1 <= n2 | _ => False end.

Definition pp :=
   fun l => match l with n1::n2::nil => 2*n1=n2*(n2+1) | _ => False end.

Definition ex_m := (("le", le_list)::("pp",pp)::nil).

Example ex1 : forall r2 n g, 0<= n ->
  exec (("x", 0)::("y", 0)::("n", n)::nil)
   (parse_instr''
       "while x < n do [le(x,n) /\ pp(y,x)] x:=x+1;y:=x+y done") r2 ->  
   2*(r2@g)"y" = (r2@g)"n"*((r2@g)"n"+1).
Proof.
intros r2 n g Hn Hex.
 change (i_a ex_m (r2@g) (parse_assert' "pp(y,n)")).
 unfold parse_instr'' in Hex.
 apply vcg_sound with (2:= Hex);[clear Hn Hex g n r2| idtac].

parse_it.
Import syntax.
  unfold ex_m, pp, le_list;  compute_vcg; expand_semantics.
intros g; generalize (g "x")(g "y")(g "n"); intros x y n; clear.
list_conj.
intros [Hnlt [Hxlen Heq']];  assert (x=n) by lia; subst x; auto.
intros [Hxltn [_ Heq']]; 
 split;[lia | rewrite Zmult_plus_distr_r; rewrite Heq'; ring].
Show.
parse_it; unfold ex_m, le_list, pp; compute_vcg; expand_semantics; simpl.
Show.
auto with zarith.
Qed.
