From Stdlib Require Export Relations Classical ClassicalEpsilon Zwf.
Require Export function_cpo.

(* SECTION : continuity of constant functions. *)

Theorem lub_cst :
  forall (A:Type)(R:A->A->Prop)(a:A),(forall x, R x x)->lub R a (fun n=>a).
intros A R a Hrefl.
split.
intros n; apply Hrefl.
intros v Hup.
apply (Hup 0).
Qed.

Theorem continuous_cst :
  forall (A B:Type)(R:A->A->Prop)(R':B->B->Prop)(b:B),
  reflexive R' -> continuous R R' (fun x:A => b).
intros A B R R' b Hrefl c Hch l Hlub.
apply lub_cst; auto.
Qed.

(* SECTION: the operation of composing on the left with an arbitrary
   function. *)

Definition comp_right (A:Type)(f g:A->option A)(x:A) :=
  match f x with None => None | Some r => g r end.

Arguments comp_right : default implicits.

Theorem comp_right_continuous :
  forall (A:Type)(f:A->option A),
     continuous (f_order' A)(f_order' A)(comp_right f).
intros A f c Hc l [Hu Hl].
split.
intros n x; unfold comp_right; case (f x);
   [exact (Hu n) | apply option_cpo_none_bot].
intros g' Hu' x.
assert (Hc' : forall n, option_cpo (comp_right f (c n) x)
                                   (comp_right f (c (S n)) x)).
intros n; unfold comp_right; case (f x);
   [intros a; exact (Hc n a) | apply option_cpo_none_bot].
case_eq (f x).
intros a Hfxeqa.
unfold comp_right; rewrite Hfxeqa.
generalize (lub_lift_reverse A (option A) (option_cpo (A:=A)) c l
            (conj Hu Hl) a).
intros [_ Hlla].
apply Hlla.
intros n; generalize (Hu' n x); unfold comp_right; rewrite Hfxeqa; trivial.
intros Hfxeqnone; unfold comp_right; rewrite Hfxeqnone.
apply option_cpo_none_bot.
Qed.

(* SECTION: a simple form of conditional statement. *)

Definition ifthenelse (A:Type)(t:option bool)(v w: option A) :=
  match t with Some true => v | Some false => w | None => None end.

Notation "'IF x 'THEN a 'ELSE b" :=
   (ifthenelse _ x a b) (at level 200).

Theorem ifthenelse_continuous :
  forall (A:Type) t F G,
     continuous (f_order' A) (f_order' A) F ->
     continuous (f_order' A) (f_order' A) G ->
     continuous (f_order' A) (f_order' A)
       (fun f x => 'IF (t x) 'THEN (F f x) 'ELSE (G f x)).
Proof.
intros A t F G HF HG c Hc l Hl.
apply (lift_lub A (option A) (@option_cpo A)).
intros x; destruct (t x) as [[ | ] | ]; simpl.
apply lub_lift_reverse with (l := F l)(c:= fun n => F (c n));
 apply HF; auto.
apply lub_lift_reverse with (l := G l)(c:= fun n => G (c n));
 apply HG; auto.
split;  intro; auto.
Qed.
