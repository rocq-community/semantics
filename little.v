From Stdlib Require Import ZArith List Lia.
Require Import syntax.
Open Scope Z_scope.


Module little(S : little_syntax).

Import S.

Definition env := list(string*Z).

Inductive aeval : env -> aexpr -> Z -> Prop :=
  ae_int : forall r n, aeval r (anum n) n
| ae_var1 : forall r x v, aeval ((x,v)::r) (avar x) v
| ae_var2 : forall r x y v v' , x <> y -> aeval r (avar x) v' ->
              aeval ((y,v)::r) (avar x) v'
| ae_plus : forall r e1 e2 v1 v2,
              aeval r e1 v1 -> aeval r e2 v2 ->
              aeval r (aplus e1 e2) (v1 + v2).

Global Hint Resolve ae_int ae_var1 ae_var2 ae_plus : core.

Inductive beval : env -> bexpr -> bool -> Prop :=
| be_lt1 : forall r e1 e2 v1 v2,
            aeval r e1 v1 -> aeval r e2 v2 ->
            v1 < v2 -> beval r (blt e1 e2) true
| be_lt2 : forall r e1 e2 v1 v2,
            aeval r e1 v1 -> aeval r e2 v2 ->
            v2 <= v1 -> beval r (blt e1 e2) false.

Inductive s_update : env->string->Z->env->Prop :=
| s_up1 : forall r x v v', s_update ((x,v)::r) x v' ((x,v')::r)
| s_up2 : forall r r' x y v v', s_update r x v' r' ->
            x <> y -> s_update ((y,v)::r) x v' ((y,v)::r').

Inductive exec : env->instr->env->Prop :=
| SN1 : forall r, exec r skip r
| SN2 : forall r r' x e v, aeval r e v -> s_update r x v r' -> exec r (assign x e) r'
| SN3 : forall r r' r'' i1 i2,
    exec r i1 r' -> exec r' i2 r'' -> exec r (sequence i1 i2) r''
| SN4 : forall r r' r'' b i,
    beval r b true -> exec r i r' -> exec r' (while b i) r'' -> exec r (while b i) r''
| SN5 : forall r b i,
    beval r b false -> exec r (while b i) r.


Global Hint Resolve be_lt1 be_lt2 s_up1 s_up2 SN1 SN2 SN3 SN4 SN5 : core.

Inductive sos_step : env->instr->instr->env->Prop :=
  SOS1 : forall r r' x e v,
   aeval r e v -> s_update r x v r' ->
   sos_step r (assign x e) skip r'
| SOS2 : forall r i2, sos_step r (sequence skip i2) i2 r
| SOS3 : forall r r' i1 i1' i2,
               sos_step r i1 i1' r' ->
               sos_step r (sequence i1 i2)(sequence i1' i2) r'
| SOS4 :
     forall r b i, beval r b true ->
       sos_step r (while b i) (sequence i (while b i)) r
| SOS5 :
     forall r b i, beval r b false ->
       sos_step r (while b i) skip r.

Inductive sos_star : env->instr->instr->env->Prop :=
  SOS6 : forall r i, sos_star r i i r
| SOS7 : forall r r' r'' i i' i'',
             sos_step r i i' r' -> sos_star r' i' i'' r'' ->
             sos_star r i i'' r''.

Global Hint Resolve SOS1 SOS2 SOS3 SOS5 SOS4 SOS6 SOS7 : core.

Lemma sos_star_trans :
   forall r r' r'' i i' i'',
    sos_star r i i' r' -> sos_star r' i' i'' r'' ->
    sos_star r i i'' r''.
Proof.
induction 1; eauto.
Qed.

Lemma sos_sequence_aux : forall r i is r',
  sos_star r i is r' -> is = skip ->
  forall i' i'' r'', sos_star r' i' i'' r'' ->
  sos_star r (sequence i i') i'' r''.
Proof.
induction 1; intros; try (subst i); eauto.
(* Before using modules,the previous line finished off the proof. *)
apply SOS7 with (r':=r')(i':=sequence i' i'0); auto.
Qed.

Lemma sos_sequence : forall  r r' r'' i i',
  sos_star r i skip r' -> sos_star r' i' skip r'' ->
  sos_star r (sequence i i') skip r''.
Proof.
  intros; eapply sos_sequence_aux; eauto.
Qed.

Global Hint Resolve sos_sequence : core.

Lemma sn_imp_sos :
 forall r r' i,  exec r i r' -> sos_star r i skip r'.
Proof.
  intros r r' i H; elim H; eauto.
Qed.

Lemma sos_sequence_assoc_aux : forall r r' i i',
  sos_star r i i' r' -> i' = skip ->
  forall i1 i2 i3, i = (sequence i1 (sequence i2 i3)) ->
  sos_star r (sequence (sequence i1 i2) i3) skip r'.
Proof.
induction 1; intros; subst; try discriminate.
match goal with id : sos_step _ _ _ _ |- _ => inversion id; subst; eauto end.
(* Before the change in module structure, the proof was over here. *)
match goal with id : sos_star _ _ _ _ |- _ => apply SOS7 with (2:=id);auto end.
apply SOS7 with (i':=sequence (sequence i1' i2) i3)(r':=r'); auto.
Qed.

Lemma sos_sequence_assoc : forall r r' i1 i2 i3,
  sos_star r (sequence i1 (sequence i2 i3)) skip r' ->
  sos_star r (sequence (sequence i1 i2) i3) skip r'.
Proof.
intros; eapply sos_sequence_assoc_aux; eauto.
Qed.

Lemma sos_step_imp_sn : forall r r' i i',
  sos_step r i i' r' ->  forall r'', exec r' i' r'' -> exec r i r''.
Proof.
 induction 1; intros r2 Hexec; try (inversion Hexec; subst; eauto).
Qed.

Lemma sos_imp_sn_aux : forall r i is r',
  sos_star r i is r' -> is = skip -> exec r i r'.
Proof.
 induction 1; intros; subst; eauto.
 eapply sos_step_imp_sn; eauto.
Qed.

Lemma sos_imp_sn : forall r i r', sos_star r i skip r' -> exec r i r'.
Proof.
  intros; eapply sos_imp_sn_aux; eauto.
Qed.

Theorem sos_eq_sn : forall r i r', sos_star r i skip r' <-> exec r i r'.
Proof.
 intros; split; [apply sos_imp_sn | apply sn_imp_sos]; assumption.
Qed.

Fixpoint lookup (r:env)(name:string){struct r} : option Z :=
  match r with
    nil => None
  | (a,b)::tl => if (string_dec a name) then Some b else lookup tl name
  end.

Definition bind (A B:Type)(v:option A)(f:A->option B) :
     option B :=
  match v with Some x => f x | None => None end.
Arguments bind : default implicits.

Fixpoint af (r:env)(a:aexpr) {struct a}: option Z :=
  match a with
    avar index => lookup r index
  | anum n => Some n
  | aplus e1 e2 =>
     bind (af r e1)
     (fun v1 => bind (af r e2) (fun v2 => Some (v1+v2)))
   end.

Definition bf (r:env)(b:bexpr) : option bool :=
  let (e1, e2) := b in
  bind (af r e1)
    (fun v1 => bind (af r e2)
      (fun v2 =>
       if Z.ltb v1 v2 then Some true else Some false)).

Fixpoint uf (r:env)(x:string)(n:Z){struct r}
  : option(env) :=
    match r with
      nil => None
    | (y,n')::tl =>
      if string_dec y x then
        Some((x,n)::tl)
      else
        bind (uf tl x n) (fun tl' => Some ((y,n')::tl'))
    end.

Definition bind2 (A B C:Type)(v:option(A*B))
  (f: A->B->option C) :option C:=
  match v with Some(a,b) => f a b | None => None end.
Arguments bind2 : default implicits.

Definition eq_skip (i:instr) : {i=skip}+{i<>skip}.
case i; auto; right; discriminate.
Defined.

Fixpoint f_sos (r:env)(i:instr) {struct i} : option (env*instr) :=
  match i with
    skip => None
  | assign x e =>
    bind (bind (af r e) (fun n => uf r x n))
      (fun r' => Some(r', skip))
  | sequence i1 i2 =>
    if eq_skip i1 then Some(r, i2) else
    bind2 (f_sos r i1) (fun r' i' => Some(r', sequence i' i2))
  | while b i =>
    bind (bf r b)
      (fun v => if v then Some(r, sequence i (while b i))
                else Some(r, skip))
  end.

Fixpoint f_star (n:nat)(r:env)(i:instr){struct n}
   :option(env*instr) :=
  match n with
    0%nat => Some(r,i)
  | S n =>
    if eq_skip i then
       Some(r,i)
    else
        bind2 (f_sos r i) (fun r' i' => f_star n r' i')
  end.

Lemma aeval_lookup :
  forall r e n, aeval r e n ->
    forall name, e = avar name -> lookup r name = Some n.
Proof.
 intros r e n H; elim H; simpl.
 intros; discriminate.
 intros r0 x v name Heq; injection Heq; intros; subst.
 destruct (string_dec name name); intuition auto.
 intros r0 x y v v' Hneq Hev Hrec name Heq;
  injection Heq; intros; subst.
  destruct (string_dec y name); auto.
  intros; elim Hneq; auto.
 intros; discriminate.
Qed.

Lemma aeval_f :
  forall r e n, aeval r e n -> af r e = Some n.
Proof.
 induction 1; simpl; auto.
 destruct (string_dec x x); intuition.
 destruct (string_dec y x); auto.
 elim H; auto.
 rewrite IHaeval1; simpl; rewrite IHaeval2; simpl; auto.
Qed.


Lemma beval_f :
  forall r e b, beval r e b -> bf r e = Some b.
Proof.
  induction 1; simpl;
  rewrite aeval_f with (1:= H);
  rewrite aeval_f with (1:= H0);simpl;
  generalize (Zlt_cases v1 v2); case (Z.ltb v1 v2); auto;
  intros H'; assert False by lia; contradiction.
Qed.

Lemma s_update_f :
  forall r x v r', s_update r x v r' -> uf r x v = Some r'.
Proof.
 induction 1; simpl.
 case (string_dec x x); intuition.
 case (string_dec y x); intuition.
 assert False ; auto; intuition.
 rewrite IHs_update; auto.
Qed.

Lemma sos_step_f_sos :
  forall r i i' r', sos_step r i i' r' -> f_sos r i = Some(r', i').
Proof with eauto.
  induction 1...
  unfold f_sos, bind...
  match goal with id : _ |- _ => rewrite aeval_f with (1:=id) end.
  match goal with id : _ |- _ => rewrite s_update_f with (1:=id) end...
  simpl.
  case (eq_skip i1).
   intros; subst; inversion H.
   intros; rewrite IHsos_step; eauto.
  simpl; match goal with id :_ |- _ => rewrite beval_f with (1:=id); auto end.
  simpl; match goal with id :_ |- _ => rewrite beval_f with (1:=id); auto end.
Qed.

Lemma lookup_aeval :
  forall r x v, lookup r x = Some v -> aeval r (avar x) v.
Proof with auto.
  induction r; intros x v.
  simpl; intros; discriminate.
  destruct a as [y n]; simpl; case (string_dec y x)...
  intros Heq Heq2; injection Heq2; intros; subst...
Qed.

Global Hint Resolve lookup_aeval : core.

Ltac find_deep_bind a :=
  match a with
    bind ?a _ => find_deep_bind a
  | bind2 ?a _ => find_deep_bind a
  | _ => a
  end.

Ltac unbind_hyp H v Heq :=
  match type of H with
  |  bind ?a ?b = Some _ =>
     let c := find_deep_bind a in
     (case_eq c; [intros v Heq | intros Heq]; rewrite Heq in H;
     [simpl in H | discriminate H])
  |  bind2 ?a ?b = Some _ =>
     let c := find_deep_bind a in
     case_eq c; [intros v Heq | intros Heq]; rewrite Heq in H;
     [simpl in H | discriminate H]
  end.

Lemma af_eval :
  forall r e v, af r e = Some v -> aeval r e v.
Proof with eauto.
  induction e; intros v...
  simpl; intros Heq; injection Heq; intros; subst...
  simpl; case_eq (af r e2); case_eq (af r e1); try (intros;discriminate).
  intros v1 Heq1 v2 Heq2 Heq; injection Heq; intros; subst...
Qed.

Global Hint Resolve af_eval Z.ge_le : core.

Lemma bf_eval :
  forall r e v, bf r e = Some v -> beval r e v.
Proof with eauto with zarith.
  intros r (e1,e2) v;simpl.
  case_eq (af r e1); case_eq (af r e2); try (intros; discriminate).
  intros v1 Heq1 v2 Heq2; unfold bind.
  generalize (Zlt_cases v2 v1); destruct (Z.ltb v2 v1);
  intros comp Heq; injection Heq; intros; subst v...
Qed.

Lemma uf_s :
  forall r x v r', uf r x v = Some r' ->
  s_update r x v r'.
Proof with eauto.
  induction r.
  simpl; intros; discriminate.
  destruct a as (y,n); simpl; intros x v r'.
  case (string_dec y x).
    intros Heq1 Heq2; injection Heq2; intros; subst; auto.

    case_eq (uf r x v); try(intros; discriminate).
    intros r'' Heqr'' Hn Heq; injection Heq; intros; subst r'; auto.
Qed.

Global Hint Resolve bf_eval uf_s : core.

Lemma f_sos_sos_step :
 forall r i r' i', f_sos r i = Some(r',i') -> sos_step r i i' r'.
Proof with eauto.
intros r i r'; induction i; intros i' H.
simpl in H; unbind_hyp H v1 He; unbind_hyp H r1 Hu;
  injection H; intros; subst...
simpl in H.
destruct (eq_skip i1).
subst i1; injection H; intros; subst...
unbind_hyp H p H1; destruct p; injection H; intros; subst...
simpl in H; unbind_hyp H t Ht; destruct t; injection H; intros; subst...
simpl in H; discriminate.
Qed.

Global Hint Resolve f_sos_sos_step : core.

Lemma f_star_sem : forall n r i r' i', f_star n r i = Some(r',i')->
 sos_star r i i' r'.
Proof with eauto.
 induction n; intros r i r' i' H.
 simpl in H; injection H; intros; subst; eauto.
 simpl in H.
destruct (eq_skip i).
subst i; injection H; intros; subst...
 unbind_hyp H p H1; destruct p as [r1 i1]...
Qed.

Lemma f_star_exec : forall n r i r',
  f_star n r i = Some(r',skip) -> exec r i r'.
Proof.
intros; apply sos_imp_sn; eapply f_star_sem; eauto.
Qed.

Lemma sos_star_f : forall r i r' i', sos_star r i i' r' ->
  exists n, f_star n r i = Some(r', i').
induction 1.
exists 0%nat; simpl; auto.
case_eq (eq_skip i); intros Hi Hi'.
rewrite Hi in H; inversion H.
destruct IHsos_star as [n Hn]; exists (S n); simpl; rewrite Hi'.
rewrite sos_step_f_sos with (1:= H); auto.
Qed.

Lemma f_star_eq_sos :
 forall r i r' i', (exists n, f_star n r i = Some(r',i'))<->sos_star r i i' r'.
Proof.
 intros r i r' i'; split;
  [intros [n Hn]; apply f_star_sem with n; auto| apply sos_star_f; auto].
Qed.

Definition one_hundred := 100%nat.

(* id should have the type : sos_star r i i' r' *)
Ltac add_exec_hyp_aux id r i i' r' :=
  let res := eval vm_compute in (f_star one_hundred r' i') in
  match res with
  | Some(?r'', ?i'') =>
     (cut (sos_star r i i'' r'');
       [clear id; intros id |
        apply sos_star_trans with (1:= id);
        apply (f_star_sem one_hundred); apply refl_equal]);
     match i'' with
       skip => cut (exec r i r'');
            [clear id; intros id | apply sos_imp_sn_aux with skip; trivial]
     | _ => add_exec_hyp_aux id r i i'' r''
     end
  end.

Ltac add_exec_hyp id r i :=
  assert (id : sos_star r i i r); [apply SOS6 | add_exec_hyp_aux id r i i r].


Ltac solve_exec_aux r i :=
  let H := fresh "Hse" in
  (add_exec_hyp H r i; (eapply ex_intro || eapply exist); eapply H).

Ltac solve_exec :=
  match goal with
    |- exists r, exec ?r0 ?i0 r => solve_exec_aux r0 i0
  | |- {r | exec ?r0 ?i0 r} => solve_exec_aux r0 i0
  end.

End little.
