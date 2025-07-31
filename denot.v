From Stdlib Require Import Relations ClassicalEpsilon.
Require Export function_cpo constructs.
Require Export syntax little.

(* The function that is used for the semantics of the while construct. *)

Module denot (S : little_syntax).

Module L := little.little(S).
Import L S.

Definition F_phi (A:Type)(t:A->option bool)(f g :A->option A) :=
   fun r => 'IF (t r) 'THEN (bind (f r) g) 'ELSE (Some r).

Theorem F_phi_continuous :
   forall (A : Type) t f,
       continuous (f_order A A)(f_order A A) (F_phi A t f).
intros A t f; unfold F_phi;
apply ifthenelse_continuous with (F:= comp_right f)
        (G:= fun (g:A->option A)(x:A) => Some x).
apply comp_right_continuous.
apply continuous_cst; auto.
Qed.

Definition phi := fun A t f => Tarski_fix (F_phi A t f).

Arguments phi : default implicits.

(* reasoning tools. *)

Lemma phi_terminates_n :
  forall (A:Type) (t:A->option bool)  f r r',
  phi t f r = Some r' ->
  exists n, iter _ (F_phi A t f) n (fun g => None) r = Some r'.
intros A t f r r' Heq.
assert (Hlub : lub (f_order' A) (phi t f)
                (fun n => iter _ (F_phi A t f) n (fun x : A => None))).
apply least_fixpoint_lub_iterates; auto.
intros g x; apply option_cpo_none_bot.
unfold f_order'; apply F_phi_continuous.
unfold phi, F_phi, f_order'; apply Tarski_fix_prop.
exact (F_phi_continuous A t f).
apply (lub_some_witness _ _ _ r r' (phi t f) Heq Hlub).
Qed.

Lemma fix_phi :
  forall (A:Type)(t:A->option bool) f,
  F_phi A t f (phi t f) = phi t f.
intros A t f.
assert (Hint : least_fixpoint (f_order' A) (F_phi A t f) (phi t f)).
unfold phi, f_order'; apply Tarski_fix_prop; apply F_phi_continuous.
unfold least_fixpoint in Hint; fold (phi t f) in Hint.
intuition.
Qed.

(* SECTION : Specializing the whole thing for the while language. *)

Open Scope Z_scope.

Fixpoint ds(i:instr) : env -> option env :=
  match i with
    assign x e => fun l => bind (af l e) (fun v => uf l x v)
  | sequence i1 i2 => fun r => bind (ds i1 r) (ds i2)
  | while e i => fun l => phi (fun l' => bf l' e)(ds i) l
  | skip => fun r => Some r
  end.

Ltac case' f := case f;[idtac|intros; discriminate].

Theorem ds_sn :  forall i l l', ds i l = Some l' -> exec l i l'.
induction i.

intros l l'; simpl; unfold bind.
generalize (af_eval l a).
 case' (af l a).
intros v He.
generalize (uf_s l s v).
intros Hu Heq.
rewrite Heq in Hu.
eauto.

simpl; unfold comp_right; intros l l'.
generalize (IHi1 l); case' (ds i1 l).
intros l1 Hi1; generalize (IHi2 l1).
simpl; intros IHi2' Heq; rewrite Heq in IHi2'.
eauto.

simpl; intros l l' Heq.
pose (f:= F_phi (list(string*Z))
   (fun l => bf l b)(ds i)).

assert (Hn: exists n:nat,
          iter _ f n (fun _ : list(string*Z) => None) l =
          Some l').
apply (phi_terminates_n _ (fun l => bf l b)(ds i)).
assumption.

case Hn; intros n; generalize l; clear Heq Hn l.
induction n; intros l.
simpl; intros; discriminate.
simpl. unfold f at 1, F_phi, ifthenelse at 1.
generalize (bf_eval l b); case' (bf l b).
intros [|] Hevalb.
unfold bind at 1.
generalize (IHi l); case' (ds i l).
intros l1 Hds_i Hds_w.
 apply SN4 with l1.
auto. auto. apply IHn. auto.

intros Hres; injection Hres; intros; subst l'.
apply SN5; auto.

simpl; intros l l' Heq; injection Heq; intros; subst; apply SN1.
Qed.

Theorem sn_ds : forall l i l', exec l i l' -> ds i l = Some l'.
induction 1.

auto.

simpl; unfold bind;
 match goal with
   id : _ |- _ => rewrite aeval_f with (1:=id); apply s_update_f; auto
end.

simpl; unfold comp_right;
 match goal with id : _ |- _ => rewrite id; assumption end.

pose (f:= F_phi _ (fun l' => bf l' b)(ds i)).
simpl in IHexec2 |- *.

rewrite <- fix_phi.
unfold F_phi at 1.
assert (Ht : bf r b = Some true) by (apply beval_f; auto).
rewrite Ht; simpl.
rewrite IHexec1; simpl.
assumption.

pose (f:= F_phi _ (fun l' => bf l' b)(ds i)).
simpl.
rewrite <- fix_phi.
assert (Ht : bf r b = Some false) by (apply beval_f; auto).
simpl; unfold f, F_phi; rewrite Ht; auto.
Qed.

Theorem ds_eq_sn : forall i l l', ds i l = Some l' <-> exec l i l'.
intros; split; [apply ds_sn | apply sn_ds]; auto.
Qed.

End denot.
