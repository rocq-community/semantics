From Stdlib Require Import Bool List String ZArith.
Require Import syntax little denot.

Module ax(S:little_syntax).
Module D := denot.denot(S).
Import D L S.

Fixpoint subst (e:aexpr)(s:string)(v:aexpr) {struct e} : aexpr :=
  match e with
    avar s' =>
      if string_dec s s' then v else e
  | anum n => anum n
  | aplus e1 e2 => aplus (subst e1 s v) (subst e2 s v)
  end.

Definition b_subst (b:bexpr) (s:string) (v:aexpr) : bexpr :=
  match b with blt e1 e2 => blt (subst e1 s v)(subst e2 s v) end.

Fixpoint l_subst (l:list aexpr)(s:string)(v:aexpr) {struct l} : list aexpr :=
  match l with 
    nil => nil
  | a::tl => subst a s v::l_subst tl s v
  end.

Fixpoint a_subst (a:assert)(s:string)(v:aexpr) {struct a} :assert :=
  match a with
    a_b e => a_b (b_subst e s v)
  | a_not a => a_not (a_subst a s v)
  | pred p l => pred p (l_subst l s v)
  | a_conj a1 a2 => a_conj(a_subst a1 s v)(a_subst a2 s v)
  end.

Fixpoint pc (i:a_instr)(a:assert) {struct i} : assert :=
  match i with
    prec a' i => a'
  | a_skip => a
  | a_assign x e => a_subst a x e
  | a_sequence i1 i2 => pc i1 (pc i2 a)
  | a_while b a' i => a'
  end.

Fixpoint vcg (i:a_instr)(post : assert) {struct i} :
   list condition :=
match i with
  prec a i => c_imp a (pc i post)::vcg i post
| a_skip => nil
| a_assign _ _ => nil
| a_sequence i1 i2 => 
    vcg i2 post ++ vcg i1 (pc i2 post)
| a_while e a i =>
    c_imp (a_conj (a_not (a_b e)) a) post ::
    c_imp (a_conj (a_b e) a) (pc i a) :: vcg i a
  end.

Fixpoint af' (g:string->Z)(a:aexpr) {struct a} : Z :=
  match a with
    avar s => g s
  | anum n => n
  | aplus e1 e2 => af' g e1 + af' g e2
  end.

Fixpoint lf' (g:string->Z)(l:list aexpr){struct l} : 
   list Z :=
   match l with
     nil => nil
   | e::tl => af' g e::lf' g tl
   end.
  
Definition p_env := list(string*(list Z->Prop)).

Fixpoint f_p (preds : p_env)
  (s:string) (args:list Z) {struct preds} : Prop :=
  match preds with
    (a,m)::tl =>
    if string_dec a s then m args else f_p tl s args
  | nil => True
  end.

Definition bf' (g:string->Z)(b:bexpr) : Prop :=
 match b with
   blt e1 e2 => af' g e1 < af' g e2
 end.

Fixpoint i_a 
  (preds: p_env) (g:string->Z)(a:assert) {struct a}: Prop :=
  match a with
    a_b e => bf' g e
  | a_not a => ~ i_a preds g a
  | pred p l => f_p preds p (lf' g l)
  | a_conj a1 a2 =>
    i_a preds g a1 /\ i_a preds g a2
  end.

Definition i_c
  (m: p_env) (g:string->Z)(c:condition) :=
match c with
  c_imp a1 a2 => i_a m g a1 -> i_a m g a2
end.

Definition valid (preds: p_env) (c:condition) :=
  forall g, i_c preds g c.

Inductive ax_sem (preds : p_env) :
      assert -> instr -> assert -> Prop :=
  ax1 : forall P, ax_sem preds P skip P
| ax2 : forall P x e, ax_sem preds (a_subst P x e) (assign x e) P
| ax3 : forall P Q R i1 i2, 
          ax_sem preds P i1 Q -> ax_sem preds Q i2 R ->
          ax_sem preds P (sequence i1 i2) R
| ax4 : forall P b i,
          ax_sem preds (a_conj (a_b b) P) i P ->
          ax_sem preds P (while b i) (a_conj (a_not (a_b b)) P)
| ax5 : forall P P' Q' Q i,
        valid preds (c_imp P P') -> ax_sem preds P' i Q' ->
        valid preds (c_imp Q' Q) ->
        ax_sem preds P i Q.

Inductive nax (preds: p_env) :
  assert -> instr -> assert -> Prop :=
  nax1 : forall P Q, valid preds (c_imp P Q) ->
      nax preds P skip Q
| nax2 : forall P P' Q x e,
    valid preds (c_imp P (a_subst P' x e)) ->
    valid preds (c_imp P' Q) ->
    nax preds P (assign x e) Q
| nax3 : forall P P' Q' R' R i1 i2,
    valid preds (c_imp P P') ->
    valid preds (c_imp R' R) ->
    nax preds P' i1 Q' -> nax preds Q' i2 R' ->
    nax preds P (sequence i1 i2) R
| nax4 : forall P P' Q b i,
    valid preds (c_imp P P') ->
    valid preds (c_imp (a_conj (a_not (a_b b)) P') Q) ->
    nax preds (a_conj (a_b b) P') i P' ->
    nax preds P (while b i) Q.

Fixpoint i_lc (preds: list (string*(list Z->Prop)))
  (g:string->Z)(l:list condition) {struct l}: Prop :=
  match l with
    nil => True
  | c::tl => i_c preds g c /\ i_lc preds g tl
  end.

Fixpoint e_to_f(r:list(string*Z))(g:string->Z)(var:string):Z :=
  match r with
    nil => g var
  | (s,v)::tl =>
    if string_dec s var then v else e_to_f tl g var
  end.

Declare Scope a_scope.
Notation "r @ g" := (e_to_f r g) (at level 30, right associativity): a_scope.
Delimit Scope a_scope with A.
Open Scope a_scope.

(* Correctness proofs: axiomatic semantics is correct. *)

Lemma af'_correct : forall r1 e v g,
  aeval r1 e v -> af' (r1@g) e = v.
intros r1 e v g H; induction H; simpl; auto.
case (string_dec x x); auto.
intros Habs; elim Habs; auto.
simpl in IHaeval; case (string_dec y x); auto.
intros Hxy ; assert (Habs:x<>y) by auto; elim Habs; auto.
rewrite IHaeval1; rewrite IHaeval2; auto.
Qed.

Lemma update_af' : forall x v r1 r2 g,
  s_update r1 x v r2 -> af' (r2@g) (avar x) = v.
intros x v r1 r2 g H; induction H.
simpl; case (string_dec x x); auto.
intros Habs; case Habs; auto.
simpl; case (string_dec y x).
intros Hxy.
assert (Hnxy : x<> y) by assumption; case Hnxy; auto.
intros _; simpl in IHs_update; apply IHs_update.
Qed.

Lemma update_af'_diff : forall x v r1 r2 g s,
  s_update r1 x v r2 -> x <> s -> 
  af' (r2@g)(avar s) = af' (r1@g) (avar s).
intros x v r1 r2 g s H; induction H; intros Hnxs.
simpl; case (string_dec x s).
intros Hxs; elim Hnxs; auto.
auto.
simpl; case (string_dec y s); auto.
Qed.

Lemma update_af'_var_subst : forall r1 x v r2 e g s,
  s_update r1 x v r2 -> aeval r1 e v ->
  af' (r2@g) (avar s) = af' (r1@g) (subst (avar s) x e).
intros r1 x v r2 e g s H He; simpl subst.
case (string_dec x s).
intros; subst s; rewrite (af'_correct r1 e v); auto.
apply update_af' with (1:= H).
intros Hnxs; apply update_af'_diff with (1:= H); auto.
Qed.

Lemma update_af'_subst : forall r1 x v r2 e' g e, 
  s_update r1 x v r2 -> aeval r1 e' v ->
  af' (r2@g) e = af' (r1@g) (subst e x e').
intros r1 x v r2 e' g e Hup He'; induction e.
apply update_af'_var_subst with (1:= Hup); auto.
trivial.
simpl; rewrite IHe1; rewrite IHe2; auto.
Qed.

Lemma update_lf'_subst :
  forall r1 x v r2 e' g l, s_update r1 x v r2 -> aeval r1 e' v ->
  lf' (r2@g) l = lf' (r1@g) (l_subst l x e').
intros r1 x v r2 e' g l Hu He'; induction l.
simpl; auto.
simpl; rewrite update_af'_subst with (1:= Hu)(2:= He').
rewrite IHl; auto.
Qed.

Lemma update_f_p_subst :
  forall r1 x v r2 e' m g s l, s_update r1 x v r2 -> aeval r1 e' v ->
  (f_p m s (lf' (r1@g) (l_subst l x e')) <-> f_p m s (lf' (r2@g) l)).
intros r1 x v r2 e' m g s l Hu He'; induction m.
simpl; intros; split; auto.
destruct a as [p1 P]; simpl; case (string_dec p1 s).
rewrite update_lf'_subst with (1:= Hu) (2:= He').
intros; split; auto.
intros; apply IHm.
Qed.

Lemma a_subst_correct :
  forall a r1 e v m g r2 x,
    aeval r1 e v ->
    s_update r1 x v r2 ->
    (i_a m (r1@g) (a_subst a x e)<->
    i_a m (r2@g) a).
induction a; simpl; intros r1 e v m g r2 x H Hu.
destruct b as [e1 e2]; unfold bf', b_subst.
repeat rewrite update_af'_subst with (1:= Hu) (2:=H); split; auto.
split; intros H1 Habs; case H1; 
elim (IHa r1 e v m g r2 x H Hu); auto.
split; intros [H1 H2]; (split; [elim (IHa1 r1 e v m g r2 x H Hu)|
                               elim (IHa2 r1 e v m g r2 x H Hu)]); auto.
apply update_f_p_subst with (1:=Hu)(2:=H).
Qed.

Lemma beval_true_interpret :
  forall r b g, beval r b true -> bf' (r@g) b.
intros r b g H; inversion H; simpl.
rewrite (af'_correct r e1 v1);
 try rewrite (af'_correct r e2 v2); auto.
Qed.

Lemma beval_false_interpret :
  forall r b g, beval r b false -> ~ bf' (r@g) b.
intros r b g H; inversion H; simpl.
rewrite (af'_correct r e1 v1);
 try rewrite (af'_correct r e2 v2); auto with zarith.
Qed.

Global Hint Resolve beval_true_interpret beval_false_interpret : core.

Lemma ax_sem_nax :
  forall m P i Q, ax_sem m P i Q -> nax m P i Q.
induction 1.
apply nax1; red; simpl; auto.
apply nax2 with P; red; simpl; auto.
apply nax3 with P Q R; try red; simpl; auto.
apply nax4 with P; try red; simpl; auto.
inversion_clear IHax_sem.
apply nax1; unfold valid in *; simpl in *; auto.
apply nax2 with P'0; unfold valid in *; simpl in *; auto.
apply nax3 with P'0 Q'0 R'; unfold valid in *; simpl in *; auto.
apply nax4 with P'0; unfold valid in *; simpl in *; auto.
Qed.

Global Hint Resolve ax1 ax2 ax3 ax4 : core.

Lemma nax_ax_sem :
  forall m P i Q, nax m P i Q -> ax_sem m P i Q.
induction 1.
apply ax5 with Q Q; unfold valid in *; simpl in *; eauto.
apply ax5 with (a_subst P' x e) P'; simpl in *; eauto.
apply ax5 with P' R'; simpl in *; eauto.
apply ax5 with P' (a_conj (a_not (a_b b)) P'); simpl in *; eauto.
Qed.

Theorem nax_sound :
  forall m r i r' g, exec r i r' -> 
  forall P Q, nax m P i Q ->
  i_a m (r@g) P -> i_a m (r'@g) Q.
Proof.
intros m r i r' g H; induction H; intros P Q Ha; inversion Ha;
unfold valid in *; simpl in *; intros; subst; clear Ha; eauto.
match goal with
 H: aeval _ _ _, G: s_update _ _ _ _ |- _ =>
 destruct (a_subst_correct P' _ _ _ m g _ _ H G) as [Hs1 _]
end; auto.
match goal with
  H:nax m (a_conj _ ?P') ?i1 ?Q',G:exec _ (while ?b _) ?r'',
  K: _ |- _ => assert (Ha := H); apply K;
  change (i_a m (r''@g) (a_conj (a_not (a_b b)) P'));
  apply IHexec2 with (P:=P')
end.
apply nax4 with (3:= Ha); unfold valid; simpl; auto.
apply IHexec1 with (1:= Ha); simpl; auto.
Qed.

Theorem ax_sem_sound :
  forall m r i r' g P Q, exec r i r' -> ax_sem m P i Q ->
  i_a m (r@g) P -> i_a m (r'@g) Q.
intros; eapply nax_sound; eauto.
apply ax_sem_nax; auto.
Qed.

(* Correctness proof: the vcg *)

Definition valid_l (ps: p_env)(l:list condition) : Prop :=
  forall g, i_lc ps g l.

Theorem i_lc_app_l : 
  forall m g l1 l2, i_lc m g (l1++l2) ->
    i_lc m g l1.
intros m g l1 l2; induction l1; simpl; auto.
intros [H1 H2]; auto.
Qed.

Theorem i_lc_app_r :
 forall m g l1 l2, i_lc m g (l1++l2) ->
  i_lc m g l2.
intros m g l1 l2; induction l1;simpl; auto.
intros [H1 H2]; auto.
Qed.

Theorem vcg_ax :
  forall m i A, valid_l m (vcg i A) ->
  ax_sem m (pc i A) (un_annot i) A.
unfold valid_l; intros m i; induction i; intros A Hc; simpl.
simpl in *; apply ax5 with (pc i A) A.
intros g; elim (Hc g); auto.
apply IHi; intros g; elim (Hc g); auto.
red; simpl; auto.
apply ax1.
apply ax2.
simpl in *; apply ax3 with (pc i2 A).
apply IHi1; intros g; apply i_lc_app_r with (1:= Hc g).
apply IHi2; intros g; apply i_lc_app_l with (1:= Hc g).
simpl in *; apply ax5 with a (a_conj (a_not (a_b b)) a).
red; simpl; auto.
apply ax4.
apply ax5 with (pc i a) a.
intros g; simpl; generalize (Hc g); intuition.
apply IHi; intros g; simpl; generalize (Hc g); intuition.
red; simpl; auto.
intros g; simpl; generalize (Hc g); intuition.
Qed.

Theorem vcg_sound :
  forall ps i A g r1 r2, valid_l ps (vcg i A) -> exec r1 (un_annot i) r2 ->
  i_a ps (r1@g) (pc i A) -> i_a ps (r2@g) A.
Proof.
intros; eapply ax_sem_sound; eauto.
apply vcg_ax; auto.
Qed.

End ax.
