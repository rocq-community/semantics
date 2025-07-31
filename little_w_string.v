From Stdlib Require Import ZArith List String Bool.
Require Import syntax little axiom abstract_i.
Open Scope string_scope.

Module str <: little_syntax.

Definition string := string.
Definition string_dec := string_dec.
Definition false_cst := "False".
Definition true_cst := "True".
Definition between_cst := "between".
Definition le_cst := "le".
Definition ge_cst := "ge".

Inductive lt_i : string -> string -> Prop :=
  lt0 : lt_i between_cst false_cst
| lt1 : lt_i false_cst ge_cst
| lt2 : lt_i ge_cst le_cst
| lt3 : lt_i le_cst true_cst
| lti_trans : forall x y z, lt_i x y -> lt_i y z -> lt_i x z.

Definition lt := lt_i.
Global Hint Resolve lt0 lt1 lt2 lt3 : core.

Theorem all_distinct : lt between_cst false_cst /\ lt false_cst ge_cst /\
  lt ge_cst le_cst /\ lt le_cst true_cst.
Proof.
 unfold lt; auto.
Qed.

Scheme lt_ind2 := Induction for lt_i Sort Prop.

Theorem lt_irrefl : forall x, ~lt x x.
assert (Hin : forall x y, lt x y -> x = between_cst \/ x = false_cst \/
                           x = ge_cst \/ x = le_cst)
 by (intros x y H; elim H; auto).
assert (Hin' : forall x y, lt x y -> y = false_cst \/ y = ge_cst \/
             y = le_cst \/ y = true_cst)
 by (intros x y H; elim H; auto).
assert (Hle : forall x y, lt x y -> x = le_cst -> y = true_cst).
intros x y H; elim H; try (intros; discriminate); auto.
intros x' y' z Hxy Hi1 Hyz Hi2 Hx; rewrite Hi1 in Hyz; auto.
destruct (Hin _ _ Hyz) as [H' | [H' | [H' | H']]]; discriminate H'.
assert (Hin2 :
        forall x y, lt x y -> forall z,
             lt y z -> x = between_cst \/ x = false_cst \/
             x = ge_cst).
intros x y H; elim H; eauto.
intros z Hz; destruct (Hin _ _ Hz) as [H' | [ H' | [H'|H']]];discriminate H'.
assert (Hin3 :
  forall x y, lt x y -> forall z, lt y z -> forall u, lt z u ->
              x = between_cst \/ x = false_cst).
intros x y H; elim H; clear H; eauto.
intros z Hz; assert (Hle' := Hle _ _ Hz); rewrite Hle'; auto.
intros u Hu; assert (Hin'' := Hin _ _ Hu).
destruct Hin'' as [H' | [H' | [H' | H']]]; discriminate H'.
intros z Hz; assert (Hin'' := Hin _ _ Hz).
destruct Hin'' as [H' | [H' | [H' | H']]]; discriminate H'.
assert (Hin4 :
  forall x y, lt x y -> forall z, lt y z -> forall u, lt z u ->
  forall v, lt u v -> x = between_cst).
intros x y H; elim H; clear H; eauto.
intros z Hz; inversion Hz.
intros u Hu; assert (u = true_cst) by eauto; subst u.
intros v Hv; destruct (Hin _ _ Hv) as [H'|[H'|[H'|H']]]; discriminate H'.
intros u Hu v Hv; destruct (Hin3 _ _ Hz _ Hu _ Hv); discriminate.
intros z Hz u Hu v Hv; destruct (Hin3 _ _ Hz _ Hu _ Hv); discriminate.
intros z Hz; destruct (Hin _ _ Hz) as [H'|[H'|[H'|H']]]; discriminate H'.
intros x Hx; assert (H' := Hin4 _ _ Hx _ Hx _ Hx _ Hx); subst x.
destruct (Hin' _ _ Hx) as [H'|[H'|[H'|H']]]; discriminate.
Qed.

Definition lt_trans : forall x y z, lt x y -> lt y z -> lt x z :=
 lti_trans.

Definition aexpr := aexpr0 string.
Definition bexpr := bexpr0 string.
Definition instr := instr0 string.
Definition assert := assert0 string.
Definition condition := condition0 string.
Definition a_instr := a_instr0 string.

Set Implicit Arguments.

Fixpoint un_annot (i:a_instr):instr :=
  match i with
    prec _ i => un_annot i
  | a_skip => skip
  | a_assign x e => assign x e
  | a_sequence i1 i2 => sequence (un_annot i1)(un_annot i2)
  | a_while b a i => while b (un_annot i)
  end.

Definition false_assert : assert := pred false_cst nil.

Fixpoint mark (i:instr):a_instr :=
  match i with
    skip => a_skip
  | assign x e => a_assign x e
  | sequence i1 i2 => a_sequence (mark i1)(mark i2)
  | while b i => a_while b false_assert (mark i)
  end.

End str.

Module AB := abstract_i.ab(str).
Import str AB A D L B.

Ltac compute_vcg :=
  lazy beta iota zeta delta [
  vcg valid_l i_lc i_c i_a f_p
  str.string_dec String.string_dec string_rec string_rect sumbool_rec
  sumbool_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
  bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect sym_eq lf'
  af' bf' pc mark List.app a_subst subst l_subst].

Ltac list_conj :=
  match goal with |- True => trivial
    | _ => split;[idtac | list_conj]
  end.


(* Specialized tactics to use the vcg. *)

Ltac abstract_vars g :=
match goal with |- context[g ?s] =>
   generalize (g s); intro; abstract_vars g
 | _ => clear g
end.


Definition bind (A B:Type) (x:option A)(f:A->option B) : (option B) :=
 match x with Some x' => f x' | None => None end.

Arguments bind : default implicits.

Notation "a /\ b" := (a_conj a b) : a_scope.
Notation "a ==> b" := (c_imp a b) (at level 55, right associativity) : a_scope.
Notation "! a" := (a_not a) (at level 30) : a_scope.
