From Stdlib Require Import Bool List String ZArith.
Require Import syntax little denot axiom.
Require intervals.
Module ab(S:little_syntax).

Module A := axiom.ax(S).
Import A D L S.

Module Type Abstract_domain.
Parameter t : Type.
Parameter bot : t.
Parameter plus : t -> t -> t.
Parameter  of_int : Z -> t.
Parameter join : t -> t -> t.
Parameter add_test_constraint_right : bool -> t -> t -> option t.
Parameter add_test_constraint_left : bool -> t -> t -> option t.
Parameter widen : t -> t -> t.
Parameter eq : t -> t -> bool.

Parameter thinner : t -> t -> Prop.
Axiom thinner_refl : forall v, thinner v v.
Axiom thinner_trans : forall v1 v2 v3, thinner v1 v2 ->
 thinner v2 v3 -> thinner v1 v3.
Axiom thinner_bot : forall v, thinner v bot.
Axiom thinner_plus :
   forall x y z t, thinner x y -> thinner z t ->
     thinner (plus x z)(plus y t).

Parameter to_p : t -> Z -> Prop.
Axiom thinner_prop :
  forall i1 i2 x, thinner i1 i2 -> to_p i1 x -> to_p i2 x.

Axiom bot_semantics : forall x, to_p bot x.

Axiom plus_correct : forall v1 v2 x1 x2,
   to_p v1 x1 -> to_p v2 x2 -> to_p (plus v1 v2) (x1+x2).

Axiom of_int_correct : forall n, to_p (of_int n) n.

Axiom add_test_constraint_right_true_none :
   forall v1 v2, add_test_constraint_right true v1 v2 = None ->
     forall x1 x2, to_p v1 x1 -> 
     to_p v2 x2 -> ~x1 < x2.

Axiom add_test_constraint_left_true_none :
   forall v1 v2, add_test_constraint_left true v1 v2 = None ->
     forall x1 x2, to_p v1 x1 -> to_p v2 x2 -> ~x1 < x2.

Axiom add_test_constraint_right_false_none :
   forall v1 v2, add_test_constraint_right false v1 v2 = None ->
     forall x1 x2, to_p v1 x1 -> to_p v2 x2 -> x1 < x2.

Axiom add_test_constraint_left_false_none :
   forall v1 v2, add_test_constraint_left false v1 v2 = None ->
     forall x1 x2, to_p v1 x1 -> to_p v2 x2 -> x1 < x2.

Axiom add_test_constraint_right_true_sound :
  forall v1 v2 v x1 x2,
     add_test_constraint_right true v1 v2 = Some v ->
     to_p v1 x1 -> to_p v2 x2 -> x1 < x2 -> to_p v x1.

Axiom add_test_constraint_left_true_sound :
  forall v1 v2 v x1 x2,
     add_test_constraint_left true v1 v2 = Some v ->
     to_p v1 x1 -> to_p v2 x2 -> x1 < x2 -> to_p v x2.

Axiom add_test_constraint_right_false_sound :
  forall v1 v2 v x1 x2,
     add_test_constraint_right false v1 v2 = Some v ->
     to_p v1 x1 -> to_p v2 x2 -> ~x1 < x2 -> to_p v x1.

Axiom add_test_constraint_left_false_sound :
  forall v1 v2 v x1 x2,
     add_test_constraint_left false v1 v2 = Some v ->
     to_p v1 x1 -> to_p v2 x2 -> ~ x1 < x2 -> to_p v x2.

Axiom thinner_join :
   forall x y z t, thinner x y -> thinner z t ->
     thinner (join x z)(join y t).
Axiom thinner_join_left : forall i j, thinner i (join i j).
Axiom join_comm : forall i i', join i i' = join i' i.
Axiom join_assoc :
  forall i i' i'', join (join i i') i'' = join i (join i' i'').
Axiom join_involutive : forall i, join i i = i.
Axiom join_bot : forall i, join i bot = bot.
Axiom eq_sound : forall x y, eq x y = true -> x = y.
Axiom eq_complete : forall x, eq x x = true.

Axiom add_test_constraint_right_monotonic :
  forall neg v1 v2 v1' v2' v v',
    add_test_constraint_right neg v1 v2 = Some v ->
    add_test_constraint_right neg v1' v2' = Some v' ->
    thinner v1 v1' -> thinner v2 v2' -> thinner v v'.

Axiom add_test_constraint_left_monotonic :
  forall neg v1 v2 v1' v2' v v',
    add_test_constraint_left neg v1 v2 = Some v ->
    add_test_constraint_left neg v1' v2' = Some v' ->
    thinner v1 v1' -> thinner v2 v2' -> thinner v v'.

Axiom add_test_constraint_right_monotonic_none :
  forall neg v1 v2 v1' v2' v,
    add_test_constraint_right neg v1 v2 = Some v ->
    thinner v1 v1' -> thinner v2 v2' ->
    ~add_test_constraint_right neg v1' v2' = None.

Axiom add_test_constraint_left_monotonic_none :
  forall neg v1 v2 v1' v2' v,
    add_test_constraint_left neg v1 v2 = Some v ->
    thinner v1 v1' -> thinner v2 v2' ->
    ~add_test_constraint_left neg v1' v2' = None.

Axiom thinner_widen : forall v1 v2, thinner v1 (widen v1 v2).

Parameter to_syn : t -> (string*list Z).
Parameter m : list(string*(list Z -> Prop)).
Axiom to_syn_ok : 
  forall v x s l p, to_syn v = (s,l) -> 
    syntax.lookup string_dec m (fun l => True) s = p ->
    to_p v x = p (l++x::nil).
Axiom false_top : forall l,
    syntax.lookup string_dec m (fun l => True) false_cst l = False.

End Abstract_domain.

Module abi(Ab:Abstract_domain).
Import Ab.
Definition ab_env := list(string*Ab.t).

(*
Fixpoint ab_lookup (l:ab_env)(s:string) {struct l} : Ab.t :=
  match l with
    nil => Ab.bot
  | (s1,i)::tl => if string_dec s s1 then i else ab_lookup tl s
  end.
*)

Fixpoint ab_eval (g:string->Ab.t) (e: aexpr) {struct e}: Ab.t :=
  match e with
    anum n => Ab.of_int n
  | avar x => g x
  | aplus e1 e2 => Ab.plus (ab_eval g e1)(ab_eval g e2)
  end.

Fixpoint ab_update (l:ab_env)(s:string)(i:Ab.t) {struct l} : ab_env :=
  match l with
    nil => nil
  | (s1,i')::tl =>
    if string_dec s s1 then (s1,i)::tl else (s1,i')::ab_update tl s i
  end.

Fixpoint join_env (l1 l2:ab_env) {struct l1} : ab_env :=
  match l1,l2 with
    nil,nil => nil
  | (s,i)::tl1, (_,i')::tl2 => (s,Ab.join i i')::join_env tl1 tl2
  | _, _ => nil
  end.

Infix "@@" := join_env (at level 35, right associativity).

Definition ab_lookup :ab_env -> string -> t := 
  fun r => @syntax.lookup string string_dec t r bot.

Definition intersect_env (neg:bool)(l:ab_env)(b:bexpr) : option ab_env :=
  match b with
    blt (avar x) e =>
    match Ab.add_test_constraint_right neg (ab_lookup l x)
            (ab_eval (ab_lookup l) e) with
      None => None
    | Some v => Some (ab_update l x v)
    end
  | blt e (avar x) =>
    match Ab.add_test_constraint_left neg (ab_eval (ab_lookup l) e)
       (ab_lookup l x) with
    | None => None
    | Some v => Some (ab_update l x v)
    end
  | _ => Some l
  end.

Fixpoint widen (l1 l2:ab_env) {struct l1}: ab_env :=
  match l1 with
    nil => nil
  | (s,v1)::tl =>
    (s,Ab.widen v1 (ab_lookup l2 s))::widen tl l2
    end.

Definition fp1 (l0 l:ab_env) (b:bexpr)(i:instr)
      (f:ab_env-> a_instr*option ab_env) :=
match intersect_env true l b with
  None => (prec false_assert (mark i), Some l)
| Some l' => let (i', l'') := f l' in
  match l'' with
    None => (i', None)
  | Some l2 => (i', Some (l0 @@ l' @@ l2))
  end
end.

Inductive fp2_type : Type :=
  found : a_instr -> option ab_env -> fp2_type
| cont : ab_env -> fp2_type.

Fixpoint stable (l1 l2:ab_env) {struct l1} : bool :=
match l1, l2 with
  nil, nil => true
| (s,v)::tl1, (_,v')::tl2 => Ab.eq v v' && stable tl1 tl2
| _, _ => false
end.

Definition fp2 (init l:ab_env)(b:bexpr)(i:instr)
  (f:ab_env-> a_instr*option ab_env) : fp2_type :=
let (i', l') := fp1 init l b i f in
match l' with 
  None => found i' None
| Some l' => 
  let (i'', l'') := fp1 init l' b i f in
  match l'' with
    None => found i'' None
  | Some l'' => if stable l' l'' then found i'' (Some l') else cont (widen l' l'')
  end
end.

Fixpoint widen2 (l:ab_env) : ab_env :=
  match l with nil => nil | (s,_)::tl => (s,Ab.bot)::widen2 tl end.

Definition fp (l:ab_env)(b:bexpr)(i:instr)
  (f:ab_env->a_instr*option ab_env):=
match fp2 l l b i f with
  found i' l' => (i', l')
| cont l' =>
  match fp2 l l' b i f with
    found i'' l'' => (i'', l'')
  | cont l'' => let l := widen2 l in
    match fp1 l l b i f with
      (i, Some _) => (i, Some l)
    | (i, None) => (i, None)
    end
  end
 end.

Fixpoint str_in_list (s:string)(l:list string) {struct l} : bool :=
match l with
  s1::tl => if string_dec s s1 then true else str_in_list s tl
| _ => false
end.

Fixpoint lz_to_a (l:list Z) : list aexpr :=
  match l with n::tl => anum n::lz_to_a tl | nil => nil  end.

Definition to_assert (v:t)(e:aexpr) :=
  let (ps,l) := to_syn v in pred ps (lz_to_a l++e::nil).

Fixpoint to_a1 (l:ab_env)(ignored:list string) {struct l} : assert :=
match l with
  nil => to_assert bot (anum 0)
| (s,v)::tl => 
  if str_in_list s ignored then to_a1 tl ignored
  else let (ps, l) := to_syn v in 
    a_conj (to_assert v (avar s)) (to_a1 tl (s::ignored))
end.

Definition to_a (l:ab_env) := to_a1 l nil.

Fixpoint abstract_i (i:instr)(l:ab_env) {struct i}:a_instr*option ab_env :=
match i with
  skip => (prec (to_a l) a_skip, Some l)
| sequence i1 i2 =>
  let (i'1, l') := abstract_i i1 l in
  match l' with
    None => (a_sequence i'1 (prec false_assert (mark i2)), None)
  | Some l' => let (i'2, l'') := abstract_i i2 l' in (a_sequence i'1 i'2, l'')
  end
| assign x e =>
  (prec (to_a l)(a_assign x e), Some(ab_update l x (ab_eval (ab_lookup l) e)))
| while b i =>
  match intersect_env true l b with
    None =>
   (prec (to_a l)(a_while b (a_conj (a_not (a_b b))(to_a l))(mark i)), Some l)
  | Some l' =>
    let (i',l'') := fp l b i (abstract_i i) in
      match l'' with
        None => (prec (to_a l) (a_while b (to_a l) i'), intersect_env false l b)
      | Some l'' => (prec (to_a l)(a_while b (to_a l'') i'), intersect_env false l'' b)
      end
  end
end.

Definition to_a' (l:option ab_env) : assert :=
  match l with None => false_assert | Some l => to_a l end.

(* Section proofs. *)

Lemma lf_lz_to_a : forall g l, 
  lf' g (lz_to_a l) = l.
intros g l; induction l; simpl; auto.
rewrite IHl; auto.
Qed.

Lemma f_p_lookup : forall m s l, 
   f_p m s l =
   syntax.lookup string_dec (A:=list Z->Prop) m  (fun _ => True) s l.
intros m' s l; induction m'; simpl; auto.
destruct a as [y p]; destruct (string_dec y s); auto.
Qed.

Lemma lf'_app : forall g l1 l2, lf' g (l1++l2) = lf' g l1++lf' g l2.
intros g l1 l2; induction l1; simpl; auto.
rewrite IHl1; auto.
Qed.

(* Properties of lookup *)
Lemma ab_lookup_i_a_rec :
  forall e ig s g, ~str_in_list s ig=true -> i_a m g (to_a1 e ig) ->
       i_a m g (to_assert (ab_lookup e s) (avar s)).
induction e; intros ig s g Hi; simpl.
unfold ab_lookup; simpl; intros; unfold to_assert.
generalize (to_syn_ok bot (g s)); simpl.
destruct (to_syn bot) as [bs bl]; intros Hok; assert(Hok' :=  Hok bs bl).
simpl; rewrite lf'_app; rewrite lf_lz_to_a; rewrite f_p_lookup; simpl.
rewrite <- (Hok' (syntax.lookup string_dec m (fun _ => True) bs)); auto.
apply bot_semantics.

destruct a as [s' i']; destruct (string_dec s s') as [Hses' | Hsns']; simpl.
subst s'; destruct (str_in_list s ig);try (elim Hi; auto; fail).
destruct (to_syn i') as [ _ _ ]; unfold ab_lookup; simpl.
destruct (string_dec s s); intuition; fail.
unfold ab_lookup; simpl; destruct (string_dec s' s).
elim Hsns'; auto; fail.
case_eq (str_in_list s' ig); simpl; intros Hin Hyp.
apply IHe with (ig:=ig) (s:=s);auto.
apply IHe with (ig:=s'::ig)(s:=s).
simpl; destruct (string_dec s s'); contradiction || assumption.
destruct (to_syn i'); simpl in * |- *; intuition.
Qed.

Lemma ab_lookup_i_a :
  forall e s g, i_a Ab.m g (to_a e) ->
  i_a Ab.m g (to_assert (ab_lookup e s) (avar s)).
Proof.
unfold to_a; intros e s g; apply (ab_lookup_i_a_rec e nil s g); simpl; discriminate.
Qed.

Lemma ab_eval_i_a :
  forall e a g, i_a Ab.m g (to_a e) ->
      i_a Ab.m g (to_assert (ab_eval (ab_lookup e) a) a).
intros e a g Hyp; induction a; simpl.
 apply ab_lookup_i_a; auto.
 unfold to_assert; case_eq (to_syn (of_int n));intros ps l Hts; simpl.
 rewrite f_p_lookup.
rewrite lf'_app; simpl.
rewrite <- to_syn_ok with (p:=syntax.lookup string_dec m (fun _ => True) ps)
  (s:=ps)(v := of_int n).
apply of_int_correct.
rewrite lf_lz_to_a; auto.
auto.

simpl; unfold to_assert.
case_eq (to_syn (plus (ab_eval (ab_lookup e) a1)(ab_eval (ab_lookup e) a2)));
  intros ps l Hts; simpl.
unfold to_assert in IHa1, IHa2.
case_eq (to_syn (ab_eval (ab_lookup e) a1)); intros ps1 l1 Hts1.
case_eq (to_syn (ab_eval (ab_lookup e) a2)); intros ps2 l2 Hts2.
rewrite Hts1 in IHa1; rewrite Hts2 in IHa2; simpl in IHa1, IHa2.
rewrite f_p_lookup.
rewrite f_p_lookup in IHa1; rewrite f_p_lookup in IHa2.
repeat rewrite lf'_app in * |- *;simpl in *|-*; 
repeat rewrite lf_lz_to_a in * |- *.
rewrite <- to_syn_ok with (p:=syntax.lookup string_dec m (fun _ => True) ps)
  (v := (plus (ab_eval (ab_lookup e) a1) (ab_eval (ab_lookup e) a2)))
  (s := ps); auto.
apply plus_correct.
rewrite to_syn_ok with (p:=syntax.lookup string_dec m (fun _ => True) ps1)
 (l:=l1)(s:=ps1); auto.
rewrite to_syn_ok with (p:=syntax.lookup string_dec m (fun _ => True) ps2)
 (l:=l2)(s:=ps2); auto.
Qed.

Lemma i_a_update_rec :
  forall m g s i e l, i_a m g (to_a1 e l) ->
    i_a m g (to_assert i (avar s)) ->
    i_a m g (to_a1 (ab_update e s i) l).
intros m' g s i; induction e; simpl; intros l He Hi; auto.
destruct a as (s1, i1'); destruct (string_dec s s1);  simpl.

destruct (to_syn i);
destruct (to_syn i1'); subst s1; destruct (str_in_list s l); simpl in He |- *;
intuition auto.
destruct (to_syn i1'); destruct (str_in_list s1 l); simpl in He |- *; intuition auto.
Qed.

Lemma i_a_update :
  forall m g s i e, i_a m g (to_a e) -> i_a m g (to_assert i (avar s)) ->
    i_a m g (to_a (ab_update e s i)).
Proof.
intros m' g s i e; exact (i_a_update_rec m' g s i e nil).
Qed.


Inductive thinner_env : ab_env -> ab_env -> Prop  :=
 cte1 : thinner_env nil nil
| cte2 : forall s i1 i2 t1 t2, Ab.thinner i1 i2 ->
    thinner_env t1 t2 -> thinner_env ((s,i1)::t1)((s,i2)::t2).

Lemma thinner_env_prop_rec :
  forall l l', thinner_env l l' -> 
  forall g ig, i_a Ab.m g (to_a1 l ig) ->i_a Ab.m g (to_a1 l' ig).
intros l l'; induction 1; intros g ig Hl; simpl in Hl |- *; auto.
destruct (str_in_list s ig).
auto.
destruct (to_syn i1); destruct (to_syn i2); split; simpl in Hl;
 destruct Hl as [H1 H2]; auto.
unfold to_assert in *. 
case_eq (to_syn i1); intros ps1 l1 Hts1.
case_eq (to_syn i2); intros ps2 l2 Hts2.
generalize H1; clear H1.
rewrite Hts1.
simpl; repeat rewrite lf'_app; repeat rewrite lf_lz_to_a; simpl.
repeat rewrite f_p_lookup.
rewrite <- to_syn_ok with (1:=Hts1); auto.
rewrite <- to_syn_ok with (1:=Hts2); auto.
intros; eapply Ab.thinner_prop; eauto.
Qed.

Lemma thinner_env_prop :
  forall l l', thinner_env l l' -> 
  forall g, i_a Ab.m g (to_a l) ->i_a Ab.m g (to_a l').
exact (fun l l' H g => thinner_env_prop_rec l l' H g nil).
Qed.

Lemma thinner_env_refl : forall l, thinner_env l l.
induction l.
constructor.
destruct a; constructor; auto.
apply Ab.thinner_refl.
Qed.

Lemma thinner_join_right :  forall i i', Ab.thinner i (Ab.join i' i).
intros; rewrite Ab.join_comm; apply Ab.thinner_join_left.
Qed.

Inductive intersect_case_type (b:bexpr) : Type :=
  ict1 : forall x e, b = blt (avar x) e ->
           (forall neg l, intersect_env neg l b =
    match Ab.add_test_constraint_right neg (ab_lookup l x)
            (ab_eval (ab_lookup l) e) with
      None => None
    | Some v => Some (ab_update l x v)
    end) -> intersect_case_type b
| ict2 : forall e x, b = blt e (avar x) -> (forall s, e <> avar s) ->
   (forall neg l, intersect_env neg l b =
    match Ab.add_test_constraint_left neg (ab_eval (ab_lookup l) e)
       (ab_lookup l x) with
    | None => None
    | Some v => Some (ab_update l x v)
    end) -> intersect_case_type b
| ict3 : forall a1 a2, b = blt a1 a2 -> 
           (forall s, a1 <> avar s)->(forall s, a2 <> avar s)->
           (forall neg l, intersect_env neg l b = Some l) ->
           intersect_case_type b.

Definition intersect_case :
  forall b, intersect_case_type b.
intros b; destruct b as [[ x | n1 | e e'] a2].
eapply ict1; auto.
destruct a2 as [ x | n2 | e2 e2'].
eapply ict2; auto; intros; discriminate.
eapply ict3; auto; intros; discriminate.
eapply ict3; auto; intros; discriminate.
destruct a2 as [ x | n2 | e2 e2'].
eapply ict2; auto; intros; discriminate.
eapply ict3; auto; intros; discriminate.
eapply ict3; auto; intros; discriminate.
Defined.

Lemma l_subst_app : forall l1 l2 x e',
  l_subst (l1++l2) x e' = l_subst l1 x e' ++ l_subst l2 x e'.
intros l1 l2 x e'; induction l1; simpl; auto.
rewrite IHl1; auto.
Qed.

Lemma l_subst_lz_to_a : forall l x e, l_subst (lz_to_a l) x e = lz_to_a l.
intros l x e; induction l; simpl; auto.
rewrite IHl; auto.
Qed.

Lemma subst_to_assert : forall v e x e', a_subst (to_assert v e) x e' =
     to_assert v (subst e x e').
intros v e x e'; unfold to_assert; destruct (to_syn v) as [p l].
simpl; rewrite l_subst_app; rewrite l_subst_lz_to_a; auto.
Qed.

Lemma to_assert_bot : forall e g, i_a m g (to_assert bot e).
intros e g; unfold to_assert.
case_eq (to_syn bot); intros ts l Hts; simpl.
rewrite f_p_lookup.
rewrite lf'_app; rewrite lf_lz_to_a; simpl.
rewrite <- to_syn_ok with (1:=Hts); auto.
apply Ab.bot_semantics.
Qed.

Lemma i_a_a_subst_to_a_ignored :
  forall m g x a e l, str_in_list x l = true -> 
    i_a m g (to_a1 e l) -> i_a m g (a_subst (to_a1 e l) x a).
Proof.
intros m' g x a; induction e; intros l Heq; simpl; auto.
rewrite subst_to_assert; simpl; auto.
destruct a0; simpl;
 case_eq (str_in_list s l); simpl; auto.
destruct (to_syn t0); intros Hs0nl [Hs0 Htl]; split.
rewrite subst_to_assert.
simpl subst.
destruct (string_dec x s) as [Hss0 | Hsns0]; auto.
rewrite Hss0 in Heq; rewrite Heq in Hs0nl; discriminate.
apply IHe; simpl; destruct (string_dec x s); auto.
Qed.

Lemma i_a_ab_update_rec :
  forall m a g i e x l,
  i_a m g (to_a1 e l) -> i_a m g (to_assert i a) ->
  i_a m g (a_subst (to_a1 (ab_update e x i) l) x a).
intros m' a g i e x; induction e; intros l Hyp Ha; simpl; auto.
rewrite subst_to_assert; simpl; auto.
destruct a0.
destruct (string_dec x s); simpl.
case_eq (str_in_list s l); intros Hin.
apply i_a_a_subst_to_a_ignored.
subst s; auto.
simpl in Hyp; rewrite Hin in Hyp; intuition; fail.
destruct (to_syn i); simpl; split.
rewrite subst_to_assert; simpl; destruct (string_dec x s); intuition ; fail.
apply i_a_a_subst_to_a_ignored.
simpl; destruct (string_dec x s); try contradiction; auto.
simpl in Hyp; destruct (to_syn t0); rewrite Hin in Hyp;
 simpl in Hyp; intuition;fail.
case_eq (str_in_list s l); intros Hin.
apply IHe; simpl in Hyp; rewrite Hin in Hyp; intuition;fail.
destruct (to_syn t0); simpl; split.
rewrite subst_to_assert; unfold l_subst, subst.
destruct (string_dec x s);try contradiction.
simpl in Hyp; destruct (to_syn t0); rewrite Hin in Hyp;
 simpl in Hyp; intuition;fail.
apply IHe; auto.
simpl in Hyp; destruct (to_syn t0); rewrite Hin in Hyp; simpl in Hyp; intuition.
Qed.

Lemma i_a_ab_update :
 forall m a g i e s, i_a m g (to_a e) -> 
   i_a m g (to_assert i a) ->
   i_a m g (a_subst (to_a (ab_update e s i)) s a).
Proof.
intros m' a g i e s; exact (i_a_ab_update_rec m' a g i e s nil).
Qed.

Lemma app_i_lc :
  forall m g l1 l2, i_lc m g l1 -> i_lc m g l2 -> i_lc m g (l1++l2).
Proof.
intros m' g l1 l2; induction l1; simpl; intuition.
Qed.

Lemma abstract_i_pre_condition :
  forall i e p, pc (fst (abstract_i i e)) p = (to_a e).
induction i; intros e p; simpl; auto.
assert (IHi1' := IHi1 e); destruct (abstract_i i1 e) as [i'1 [e' |]];
 simpl in IHi1' |- *; auto.
assert (IHi2' := IHi2 e'); destruct (abstract_i i2 e') as [i'2 [e''|]];
 simpl; auto.
simpl; destruct (intersect_env true e b); simpl; auto.
destruct (fp e b i (abstract_i i)) as [i' [l' | ]]; simpl; auto.
Qed.

Lemma mark_pre_condition :
  forall i, pc (mark i) false_assert = false_assert.
Proof.
induction i; simpl; auto.
rewrite IHi2; auto.
Qed.

Lemma i_lc_vcg_mark : forall g i,
   i_lc Ab.m g (vcg (mark i) false_assert).
Proof.
intros g; induction i; simpl; auto.
apply app_i_lc; simpl; auto.
rewrite mark_pre_condition; auto.
split; [intuition | split; auto].
rewrite f_p_lookup; rewrite false_top; intuition.
Qed.

Inductive compatible (A:Type) : list(string*A)->list(string*A) -> Prop :=
 cc1 : compatible A nil nil
| cc2 : forall s a1 a2 tl1 tl2, compatible A tl1 tl2 -> 
     compatible A ((s,a1)::tl1)((s,a2)::tl2).

Arguments compatible : default implicits.

Lemma thinner_compatible :
   forall l1 l2, thinner_env l1 l2 -> compatible l1 l2.
induction 1; try constructor; auto.
Qed.

Lemma compatible_widen :  forall l l', compatible l (widen l l').
induction l; simpl; try constructor.
intros l'; destruct a as [s v]; constructor; auto.
Qed.

Lemma compatible_widen2 :
  forall l, compatible l (widen2 l).
induction l; try destruct a; simpl; try constructor; auto.
Qed.

Lemma compatible_thinner_widen2 :
   forall l l', compatible l l' -> thinner_env l (widen2 l').
induction 1; simpl; try constructor; auto.
apply Ab.thinner_bot.
Qed.

Lemma compatible_refl : forall A l, @compatible A l l.
induction l; try destruct a; constructor; auto.
Qed.

Lemma compatible_sym : forall A l l', @compatible A l l' -> compatible l' l.
induction 1; constructor; auto.
Qed.

Lemma compatible_trans : forall A l l' l'', @compatible A l l' ->
   compatible l' l'' -> compatible l l''.
intros A l l' l'' H; generalize l''; clear l''; induction H; intros l'' H'; inversion H'; 
constructor; auto.
Qed.

Lemma compatible_update :
  forall l s e, compatible l (ab_update l s e).
induction l; simpl.
intros s e; apply cc1.
destruct a as [s0 i0]; intros s e; destruct (string_dec s s0); constructor; auto.
apply compatible_refl.
Qed.

Lemma compatible_intersect_env :
  forall neg l b l', intersect_env neg l b = Some l' -> compatible l l'.
intros neg l b; destruct (intersect_case b) as [x e Hb Hi | e x Hb _ Hi | e1 e2 Hb H1 H2 Hi].
intros l'; rewrite Hi.
destruct (Ab.add_test_constraint_right neg (ab_lookup l x)
             (ab_eval (ab_lookup l) e)) as [v | ].
intros Heq; injection Heq; intro; subst l'; apply compatible_update.
intros; discriminate.
intros l'; rewrite Hi.
destruct (Ab.add_test_constraint_left neg (ab_eval (ab_lookup l) e)
            (ab_lookup l x)) as [ v | ].
intros Heq; injection Heq; intro; subst l'; apply compatible_update.
intros; discriminate.
intros l'; rewrite Hi; intros Heq; injection Heq; intros; subst.
apply compatible_refl.
Qed.

Lemma join_env_assoc : forall l l' l'', (l @@ l') @@ l'' = l @@ l' @@ l''.
induction l; destruct l'; destruct l''; simpl; auto.
destruct p; auto.
destruct p; destruct p0; try destruct a; auto.
destruct a; auto.
destruct a; auto.
destruct a; auto.
destruct p; auto.
destruct a; auto.
destruct p; auto.
destruct p0; auto.
simpl; rewrite join_assoc; rewrite IHl; auto.
Qed.

Lemma join_env_comm : forall l l', compatible l l' ->  l @@ l' = l' @@ l.
induction 1; auto.
simpl; rewrite join_comm; rewrite IHcompatible; auto.
Qed.

Lemma join_env_involutive : forall l, l @@ l = l.
induction l; simpl; auto.
destruct a; auto; rewrite join_involutive; rewrite IHl; auto.
Qed.

Lemma compatible_join_env_left : 
  forall e e', compatible e e' -> compatible e (e @@ e').
induction 1; simpl; constructor; auto.
Qed.

Lemma compatible_stable_eq :
  forall l l', compatible l l' -> stable l l' = true -> l = l'.
induction 1; simpl; auto.
destruct (string_dec s s); try (intuition; fail).
case_eq (Ab.eq a1 a2); simpl; try (intros; discriminate).
intros Hcmp Hstable ; rewrite IHcompatible; auto.
rewrite Ab.eq_sound with (1:=Hcmp); auto.
Qed.

Lemma stable_refl : forall l, stable l l = true.
induction l; simpl; auto.
destruct a; simpl.
rewrite eq_complete; auto.
Qed.

Lemma fp1_compatible :
  forall f e l1 b i1 i' l2, (forall l l', snd (f l) = Some l' -> compatible l l') ->
  compatible e l1 ->
  fp1 e l1 b i1 f = (i', Some l2) -> compatible e l1 -> compatible e l2.
intros f e l1 b i1 i' l2 Hf Hcel1; unfold fp1.
case_eq (intersect_env true l1 b); [intros l' Hi | intros Hi].
case_eq (f l'); intros a_i [l'' | ] Hfl' Heq.
injection Heq; do 2 intro; subst i' l2.
intros; apply compatible_join_env_left.
apply compatible_trans with l1; auto.
apply compatible_trans with l'; auto.
apply compatible_intersect_env with true b; auto.
apply compatible_join_env_left.
apply Hf; rewrite Hfl'; auto.
discriminate.
intros Heq; injection Heq; do 2 intro; subst i' l2; auto.
Qed.

Lemma fp2_compatible :
  forall f e l1 b i1 i2 l2, (forall l l', snd (f l) = Some l' -> compatible l l') ->
  fp2 e l1 b i1 f = found i2 (Some l2) -> compatible e l1 -> compatible e l2.
intros f e l1 b i1 i2 l2 Hf; unfold fp2.
case_eq (fp1 e l1 b i1 f); intros a_i [l' | ] Hfp1.
case_eq (fp1 e l' b i1 f); intros a_i' [l'' | ] Hfp1'.
destruct (stable l' l'').
intros Heq Hcel1; injection Heq; do 2 intro; subst l2.
apply fp1_compatible with (3:= Hfp1); auto.
intros; discriminate.
intros; discriminate.
intros; discriminate.
Qed.

Lemma fp2_compatible2 :
  forall f e l1 b i1 l2, (forall l l', snd (f l) = Some l' -> compatible l l') ->
  fp2 e l1 b i1 f = cont l2 -> compatible e l1 -> compatible e l2.
intros f e l1 b i1 l2 Hf; unfold fp2.
case_eq (fp1 e l1 b i1 f); intros i' [l' | ] Hfp1.
case_eq (fp1 e l' b i1 f); intros a_i' [l'' | ] Hfp1'.
destruct (stable l' l'').
intros; discriminate.
intros Heq Hcel1; injection Heq; intro; subst l2.
apply compatible_trans with l'.
apply fp1_compatible with (3:= Hfp1); auto.
apply compatible_widen; auto.
intros; discriminate.
intros; discriminate.
Qed.

Lemma fp_compatible :
   forall e b i f i' l',
   (forall e e', snd(f e) = Some e' -> compatible e e') ->
   fp e b i f = (i', Some l') ->
   compatible e l'.
intros e b i f i' l' Hf.
unfold fp.
case_eq (fp2 e e b i f); [intros a_i [l1 | ] Hfp2 Heq | intros l1 Hfp2].
injection Heq; do 2 intro; subst i' l'.
apply fp2_compatible with (2:= Hfp2); auto.
apply compatible_refl.
discriminate.
case_eq (fp2 e l1 b i f);[intros a_i' [l2 | ] Hfp2' Heq | intros l2 Hfp2'].
injection Heq; do 2 intro; subst i' l'.
apply fp2_compatible with (2:=Hfp2'); auto.
apply fp2_compatible2 with (2:= Hfp2); auto.
apply compatible_refl.
discriminate.
case_eq (fp1 (widen2 e)(widen2 e) b i f); intros a_i [l3 | ] Hfp1 Heq.
injection Heq; do 2 intro; subst i' l'.
apply compatible_widen2.
discriminate.
Qed.

Lemma abstract_i_compatible :
  forall i e e', snd(abstract_i i e) = Some e' -> compatible e e'.
induction i; simpl; intros e e'.

intros Heq; injection Heq; intro; subst e'; apply compatible_update.
assert (IHi1' := IHi1 e).
destruct (abstract_i i1 e) as [i'1 [e1 | ]]; simpl in IHi1'.
assert (IHi2' := IHi2 e1).
destruct (abstract_i i2 e1) as [i'2 [e2 | ]]; simpl in IHi2'; intros Heq.
injection Heq; intro; subst e'; apply compatible_trans with e1; auto.
discriminate Heq.
intros; discriminate.
destruct (intersect_env true e b).
case_eq (fp e b i (abstract_i i)); intros i' [l'' | ] Hfp Hi.
apply compatible_trans with l''.
apply fp_compatible with (2:= Hfp).
exact IHi.
apply compatible_intersect_env with false b; auto.
apply compatible_intersect_env with false b; auto.
intros Heq; injection Heq; intro; subst e'; apply compatible_refl.
intros Heq; injection Heq; intro; subst e'; apply compatible_refl.
Qed.

(* End of compatible section. *)
Lemma to_a1_to_a_lookup :
  forall e g s l, i_a Ab.m g (to_a1 e l) ->
    str_in_list s l = false ->
    i_a Ab.m g (to_assert (ab_lookup e s)(avar s)).
induction e.
simpl.
intros; apply to_assert_bot. 
destruct a as [s1 v].
intros g s l; unfold to_assert, ab_lookup; simpl.
intros Hia Hin; destruct (string_dec s s1) as [Hss1 | Hsns1].
subst s1; rewrite Hin in Hia; simpl in Hia.
destruct (to_syn v); destruct Hia as [H H0].
destruct (string_dec s s); try (intuition;fail).

destruct (str_in_list s1 l).
destruct (string_dec s1 s); [case Hsns1; auto; fail |idtac].
unfold to_assert,ab_lookup in IHe. apply IHe with l; auto.
unfold to_assert, ab_lookup in IHe.
destruct (string_dec s1 s);[elim Hsns1; intuition; fail|idtac].
apply IHe with (s1::l); simpl in *.
destruct (to_syn v); simpl in Hia; intuition.
destruct (string_dec s s1);intuition.
Qed.

Ltac i_a_to_to_p :=
  match goal with 
    |- i_a m ?g (to_assert ?v ?e) => 
    unfold to_assert; case_eq (to_syn v); intros i_a_to_to_p_s 
      i_a_to_to_p_l i_a_to_to_p_Hts;
    simpl; rewrite lf'_app; rewrite lf_lz_to_a; simpl; rewrite f_p_lookup;
    rewrite <- to_syn_ok with (1:=i_a_to_to_p_Hts); auto; clear i_a_to_to_p_Hts
      i_a_to_to_p_s i_a_to_to_p_l
  end.
Ltac to_p_to_i_a :=
match goal with g : string->Z |- to_p ?v ?gs1 =>
  case_eq (to_syn v); intros to_p_to_i_a_s to_p_to_i_a_l to_p_to_i_a_Hts;
  rewrite to_syn_ok with (1:= to_p_to_i_a_Hts)
  (p:=syntax.lookup string_dec m (fun _ => True) to_p_to_i_a_s); auto;
  match gs1 with
    (?g ?s1) => change ((g s1)::nil) with (lf' g ((avar s1)::nil))
  | (af' ?g ?e) => change (gs1::nil) with (lf' g (e::nil))
  end;
  rewrite <- (lf_lz_to_a g to_p_to_i_a_l); rewrite <- lf'_app;
  rewrite <- f_p_lookup;
  match goal with 
    |- f_p _ _ (lf' ?g (_ ++ ?e ::nil)) =>
    cut (i_a m g (to_assert v e))
  end;[unfold to_assert; rewrite to_p_to_i_a_Hts; auto|
   clear to_p_to_i_a_Hts to_p_to_i_a_s to_p_to_i_a_l]

end.

Lemma intersect_env_true_i_a :
  forall e b g, 
      i_a Ab.m g (to_a e) -> i_a Ab.m g (a_b b) -> 
      i_a Ab.m g (to_a' (intersect_env true e b)).
Proof.
intros e b g; destruct (intersect_case b) as
   [s1 e2 Heq Hint | e1  s2 Heq Hexc Hint | e1 e2 Heq Hexc1 Hexc2 Hint];
 intros He Hb; assert (Hint' := Hint true e); clear Hint.
case_eq (Ab.add_test_constraint_right true (ab_lookup e s1)
             (ab_eval (ab_lookup e) e2)).
unfold to_a'.
intros v Hadd; rewrite Hadd in Hint'; rewrite Hint'; apply i_a_update; auto.
i_a_to_to_p.
apply Ab.add_test_constraint_right_true_sound with (1:=Hadd)
        (v2 := ab_eval (ab_lookup e) e2) (x2:=af' g e2).
to_p_to_i_a.
apply ab_lookup_i_a; auto.
to_p_to_i_a.
apply ab_eval_i_a; auto.
rewrite Heq in Hb; exact Hb.
intros Hadd.
elim Ab.add_test_constraint_right_true_none with  (1:=Hadd) (x1:=g s1)
  (x2:= af' g e2).
to_p_to_i_a.
apply ab_lookup_i_a; auto.
to_p_to_i_a.
apply ab_eval_i_a; auto.
rewrite Heq in Hb; exact Hb.

case_eq (Ab.add_test_constraint_left true (ab_eval (ab_lookup e) e1)
               (ab_lookup e s2)).
intros v Hadd; rewrite Hadd in Hint'; rewrite Hint'; simpl.
apply i_a_update; auto.
i_a_to_to_p.
apply Ab.add_test_constraint_left_true_sound with (1:=Hadd)
        (v1 := ab_eval (ab_lookup e) e1) (x1:=af' g e1).
to_p_to_i_a.
apply ab_eval_i_a; auto.
to_p_to_i_a.
apply ab_lookup_i_a; auto.
rewrite Heq in Hb; exact Hb.
intros Hadd.
elim Ab.add_test_constraint_left_true_none with (1:=Hadd)
  (x1 := af' g e1)(x2:= af' g (avar s2)).
to_p_to_i_a.
apply ab_eval_i_a; auto.
to_p_to_i_a.
apply ab_lookup_i_a; auto.
rewrite Heq in Hb; exact Hb.
rewrite Hint'; simpl; auto.
Qed.

Lemma intersect_env_false_i_a :
  forall e b g, 
      i_a Ab.m g (to_a e) -> ~i_a Ab.m g (a_b b) -> 
      i_a Ab.m g (to_a' (intersect_env false e b)).
Proof.
intros e b g; destruct (intersect_case b) as
   [s1 e2 Heq Hint | e1  s2 Heq Hexc Hint | e1 e2 Heq Hexc1 Hexc2 Hint];
 intros He Hb; assert (Hint' := Hint false e); clear Hint.

case_eq (Ab.add_test_constraint_right false (ab_lookup e s1)
             (ab_eval (ab_lookup e) e2)).
unfold to_a'.
intros v Hadd; rewrite Hadd in Hint'; rewrite Hint'; apply i_a_update; auto.
i_a_to_to_p.
apply Ab.add_test_constraint_right_false_sound with (1:=Hadd)
  (v2:=(ab_eval (ab_lookup e) e2))(x2 := af' g e2).
to_p_to_i_a.
apply ab_lookup_i_a; auto. 
to_p_to_i_a.
apply ab_eval_i_a; auto.
rewrite Heq in Hb; exact Hb.
intros Hadd.
elim Hb; rewrite Heq.
apply Ab.add_test_constraint_right_false_none with (1:=Hadd)
  (x1 := af' g (avar s1))(x2:= af' g e2).
to_p_to_i_a.
apply ab_lookup_i_a; auto.
to_p_to_i_a.
apply ab_eval_i_a; auto.

case_eq (Ab.add_test_constraint_left false (ab_eval (ab_lookup e) e1)
               (ab_lookup e s2)).
intros v Hadd; rewrite Hadd in Hint'; rewrite Hint'; simpl.
apply i_a_update; auto.
i_a_to_to_p.
apply Ab.add_test_constraint_left_false_sound with (1:=Hadd)
  (v1:=(ab_eval (ab_lookup e) e1))(x1:= af' g e1).
to_p_to_i_a.
apply ab_eval_i_a; auto.
to_p_to_i_a.
apply ab_lookup_i_a; auto.
rewrite Heq in Hb; exact Hb.

intros Hadd.
elim Hb; rewrite Heq.
simpl.
apply Ab.add_test_constraint_left_false_none with (1:=Hadd) 
  (v1:= ab_eval (ab_lookup e) e1) (v2 := ab_lookup e s2).
to_p_to_i_a.
apply ab_eval_i_a; auto.
to_p_to_i_a.
apply ab_lookup_i_a; auto.
rewrite Hint'; simpl; auto.
Qed.

Definition fpw (A:Type)(g:string->A)(s:string)(v:A)(s1:string) :=
  if string_dec s s1 then v else g s1.

Arguments fpw : default implicits.

Lemma subst_fpw :
  forall g s e' e, af' g (subst e s e') = af' (fpw g s (af' g e')) e.
intros g x e' e; induction e; simpl; auto.
unfold fpw; destruct (string_dec x s); auto.
rewrite IHe1; rewrite IHe2; auto.
Qed.

Lemma l_subst_fpw :
  forall g s e l,  lf' g (l_subst l s e) = lf' (fpw g s (af' g e)) l.
intros g s e l; induction l; simpl; auto.
rewrite subst_fpw; rewrite IHl; auto.
Qed.

Lemma a_subst_fpw :
  forall m a x e g, i_a m g (a_subst a x e) = i_a m (fpw g x (af' g e)) a.
intros m' a x e g; induction a; simpl.
destruct b as [e1 e2]; simpl.
do 2 rewrite subst_fpw; auto.
rewrite IHa; auto.
rewrite IHa1; rewrite IHa2; auto.
induction m'; auto.
simpl.
destruct a as [ps p]; destruct (string_dec ps s); simpl; auto.
rewrite l_subst_fpw; auto.
Qed.


Lemma precondition_shift :
  forall m i a a', 
    (forall g, i_a m g a -> i_a m g a') ->
    forall g, i_a m g (pc i a)-> i_a m g (pc i a').
intros m'; induction i; simpl; auto.
intros a a' Haa' g; repeat rewrite a_subst_fpw.
apply Haa'.

intros a a' Haa' g;  apply IHi1; apply IHi2; auto.
Qed.

Lemma thinner_join_env_left :
  forall e e', compatible e e' -> thinner_env e (e @@ e').
intros e e' H; induction H; simpl.
apply cte1.
apply cte2; auto.
apply Ab.thinner_join_left.
Qed.

Lemma thinner_join_env_right :
  forall e e', compatible e e' -> thinner_env e (e' @@ e).
intros e e' H; induction H; simpl.
apply cte1.
apply cte2; auto.
apply thinner_join_right.
Qed.

Lemma join_env_prop_right_rec :
  forall l l' g, compatible l l' -> forall r, i_a Ab.m g (to_a1 l r) -> 
  i_a Ab.m g (to_a1 (l' @@ l) r).
intros l l' g Hc; induction Hc; intros r; simpl; auto.
destruct (str_in_list s r); simpl; auto.
destruct (to_syn a1); intros [Ha1 Htl1].
destruct (to_syn (join a2 a1)); split; auto.
i_a_to_to_p.
apply Ab.thinner_prop with a1; auto.
apply thinner_join_right; auto.
to_p_to_i_a; exact Ha1.
Qed.

Lemma join_env_prop_right :
  forall l l' g, compatible l l' -> i_a Ab.m g (to_a l) -> 
  i_a Ab.m g (to_a (l' @@ l)).
intros l l' g Hc; exact (join_env_prop_right_rec l l' g Hc nil).
Qed.

Lemma thinner_lookup :
  forall l l' s, thinner_env l l' -> 
  Ab.thinner (ab_lookup l s)(ab_lookup l' s).
induction 1; unfold ab_lookup; simpl.
apply Ab.thinner_refl.
destruct (string_dec s0 s); auto.
Qed.

Lemma thinner_eval :
  forall l l' a, thinner_env l l' ->
  Ab.thinner (ab_eval (ab_lookup l) a)(ab_eval (ab_lookup l') a).
intros l l' a Hth; induction a; auto.
simpl; apply thinner_lookup; auto.
simpl; apply Ab.thinner_refl.
simpl; apply Ab.thinner_plus; assumption.
Qed.

Lemma thinner_update :
  forall l l' s i1 i2,
  thinner_env l l' -> Ab.thinner i1 i2 ->
  thinner_env (ab_update l s i1) (ab_update l' s i2).
intros l l' s i1 i2 Hte Hth; induction Hte.
simpl; apply cte1.
simpl.
destruct (string_dec s s0);apply cte2; auto.
Qed.

Lemma thinner_join_env :  forall e1 e2 e3 e4,
  compatible e1 e3 -> thinner_env e1 e2 -> thinner_env e3 e4 ->
  thinner_env (e1 @@ e3)(e2 @@ e4).
intros e1 e2 e3 e4 Hc H; generalize e3 e4 Hc; clear e3 e4 Hc.
induction H; simpl.
intros e3 e4 Hc; inversion Hc; intros Ht3; inversion Ht3; apply cte1.
intros e3 e4 Hc; inversion Hc; intros Ht3; inversion Ht3; apply cte2; auto.
apply Ab.thinner_join; auto.
Qed.

Lemma intersect_env_true_none :
   forall l b, intersect_env true l b = None ->
   forall g, i_a Ab.m g (to_a l) -> ~bf' g b.
intros l b; destruct (intersect_case b) as
  [x e Hb Hi | e x Hb _ Hi | e1 e2 Hb H1 H2 Hi].
rewrite Hi.
case_eq (Ab.add_test_constraint_right true (ab_lookup l x)
          (ab_eval (ab_lookup l) e)).
intros v Hadd Habs; discriminate Habs.
intros Hadd _ g Hl.
rewrite Hb.
simpl; apply Ab.add_test_constraint_right_true_none with (1:=Hadd).
to_p_to_i_a.
apply ab_lookup_i_a; auto.
to_p_to_i_a.
apply ab_eval_i_a; auto.
rewrite Hi.
case_eq (Ab.add_test_constraint_left true (ab_eval (ab_lookup l) e)
          (ab_lookup l x)).
intros v Hadd Habs; discriminate Habs.
intros Hadd _ g Hl.
rewrite Hb.
simpl; apply Ab.add_test_constraint_left_true_none with (1:=Hadd).
to_p_to_i_a.
apply ab_eval_i_a; auto.
to_p_to_i_a.
apply ab_lookup_i_a; auto.
rewrite Hi; intros; discriminate.
Qed.

Lemma fp1_precondition :
  forall e l b i1 i2 i3 l',
  compatible e l ->
  fp1 e l b i1 (abstract_i i2) = (i3, Some l') ->
  forall g, i_a Ab.m g (a_conj (a_b b)(to_a l)) ->
  i_a Ab.m g (pc i3 (to_a l')).
intros e l b i1 i2 i3 l' Hcel.
unfold fp1.
case_eq (intersect_env true l b).
intros l0 Hi.
assert (Hcll0 : compatible l l0) by
 (apply compatible_intersect_env with true b; auto).
case_eq (abstract_i i2 l0); intros i' [l'' | ] Hai Heq.
assert (Hcl0l'': compatible l0 l'') by
 (apply (abstract_i_compatible i2); rewrite Hai; auto).
injection Heq; do 2 intro; subst i3 l'.
intros g; simpl; intros [Hb Hl].
assert (Has_i : i_a Ab.m g (to_a' (Some l0))) by
 (rewrite <- Hi; apply intersect_env_true_i_a; auto).
simpl in Has_i.
apply precondition_shift with (to_a l0); auto.
intros g0 Hal0.
apply join_env_prop_right.

apply compatible_sym; apply compatible_trans with l0.
apply compatible_trans with l; auto.
apply compatible_join_env_left; auto.
apply thinner_env_prop with l0; auto.
apply thinner_join_env_left; auto.
change i' with (fst (i', Some l'')).
rewrite <- Hai; rewrite abstract_i_pre_condition; auto.

discriminate.

intros Hi Heq; injection Heq; do 2 intro; subst i3 l'; clear Heq.
simpl; intros g [Hb Hl].
case (intersect_env_true_none l b Hi g); auto.
Qed.

Lemma widen2_top_rec : forall e l g, i_a Ab.m g (to_a1 (widen2 e) l).
induction e; intros l g; simpl.
i_a_to_to_p.
apply Ab.bot_semantics.
destruct a as [s p]; simpl; destruct (str_in_list s l); simpl; auto.
destruct (to_syn bot).
split; auto.
i_a_to_to_p.
apply Ab.bot_semantics.
Qed.

Lemma widen2_top : forall e g, i_a Ab.m g (to_a (widen2 e)).
intros e; exact (widen2_top_rec e nil).
Qed.

Lemma fp2_precondition1 :
   forall e l b i1 i2 i' l',
   compatible e l ->
   fp2 e l b i1 (abstract_i i2) = found i' (Some l') ->
   forall g, i_a Ab.m g (a_conj (a_b b)(to_a l')) ->
    i_a Ab.m g (pc i' (to_a l')).
intros e l b i1 i2 i' l' Hcel.
unfold fp2.
case_eq (fp1 e l b i1 (abstract_i i2)); intros i3 [l'1 | ] Hfp1.
assert (Hcel'1 : compatible e l'1).
apply fp1_compatible with (3:= Hfp1); auto.
exact (abstract_i_compatible i2).
case_eq (fp1 e l'1 b i1 (abstract_i i2)); intros i4 [l'2 | ] Hfp1'.
assert (Hcel'2 : compatible e l'2).
apply fp1_compatible with (3:= Hfp1'); auto.
exact (abstract_i_compatible i2).
case_eq (stable l'1 l'2); intros Hst Heq.
injection Heq; do 2 intro; subst l'1 i4; clear Heq.
intros g Ha; apply precondition_shift with (a:= (to_a l'2)).
rewrite compatible_stable_eq with (2:= Hst); auto.
apply compatible_trans with e; auto; apply compatible_sym; auto.
apply fp1_precondition with (2:= Hfp1'); auto.
discriminate.
intros; discriminate.
intros; discriminate.
Qed.

Lemma fp_precondition :
  forall e b i1 i2 i3 l', fp e b i1 (abstract_i i2) =(i3, Some l') ->
   forall g, i_a Ab.m g (a_conj (a_b b) (to_a l')) -> 
   i_a Ab.m g (pc i3 (to_a l')).
intros e b i1 i2 i3 l'.
unfold fp.
case_eq (fp2 e e b i1 (abstract_i i2));
   [intros i' [l1 | ] Hfp2 Heq| intros l Hfp2] .
injection Heq; do 2 intro; subst i3 l1.
assert (Hcee: compatible e e) by apply compatible_refl.
exact (fp2_precondition1 _ _ _ _ _ _ _ Hcee Hfp2).
discriminate.
case_eq (fp2 e l b i1 (abstract_i i2));
   [intros i' [l1 | ] Hfp2' Heq| intros l1 Hfp2'] .
injection Heq; do 2 intro; subst i3 l1.
assert (Hcel : compatible e l).
apply fp2_compatible2 with (2:= Hfp2); auto.
exact (abstract_i_compatible i2).
apply compatible_refl.
exact (fp2_precondition1 _ _ _ _ _ _ _ Hcel Hfp2').
discriminate.
case_eq (fp1 (widen2 e)(widen2 e) b i1 (abstract_i i2));
   intros a_i [l2 | ] Hfp1 Heq g Ha.
injection Heq; do 2 intro; subst a_i l'.
apply precondition_shift with (a := to_a l2).
intros; apply widen2_top.
apply fp1_precondition with (2:=Hfp1); auto.
apply compatible_refl.
discriminate.
Qed.

Lemma intersect_env_true_accept :
  forall l l', thinner_env l l' ->
  forall b l1, intersect_env true l b = Some l1 ->
  exists l1', intersect_env true l' b = Some l1' /\ thinner_env l1 l1'.
intros l l' H b l1.
destruct (intersect_case b) as
  [x e Hb Hi | e x Hb Hn Hi | a1 a2 Hb Hn1 Hn2 Hi].
rewrite (Hi true l); rewrite (Hi true l'); clear Hi.
case_eq (Ab.add_test_constraint_right true (ab_lookup l x)
          (ab_eval (ab_lookup l) e)).
intros v Hadd.
intros H'; injection H'; intros Hupdate; clear H'.
case_eq (Ab.add_test_constraint_right true (ab_lookup l' x)
           (ab_eval (ab_lookup l') e)).
intros v' Hadd'.
exists (ab_update l' x v').
split; auto.
subst l1.
apply thinner_update; auto.
apply Ab.add_test_constraint_right_monotonic with (1:= Hadd)(2:=Hadd').
apply thinner_lookup; auto.
apply thinner_eval; auto.
intros Hnone.
elim Ab.add_test_constraint_right_monotonic_none with (1:=Hadd)(v1':=ab_lookup l' x)(v2':= ab_eval (ab_lookup l') e).
apply thinner_lookup; auto.
apply thinner_eval; auto.
auto.
intros; discriminate.
rewrite (Hi true l); rewrite (Hi true l'); clear Hi.
case_eq (Ab.add_test_constraint_left true (ab_eval (ab_lookup l) e)
           (ab_lookup l x)).
intros v Hadd.
intros H'; injection H'; intros Heq; clear H'.
case_eq (Ab.add_test_constraint_left true (ab_eval (ab_lookup l') e)
           (ab_lookup l' x)).
intros v' Hadd'.
exists (ab_update l' x v'); split; auto.
subst l1.
apply thinner_update; auto.
apply Ab.add_test_constraint_left_monotonic with (1:=Hadd)(2:=Hadd').
apply thinner_eval; auto.
apply thinner_lookup; auto.
intros Hnone.
elim Ab.add_test_constraint_left_monotonic_none with
  (1:=Hadd)(v1':= ab_eval (ab_lookup l') e)(v2':=ab_lookup l' x); auto.
apply thinner_eval; auto.
apply thinner_lookup; auto.
intros; discriminate.
rewrite Hi; intros Heq'; injection Heq'; intros Heq; clear Heq'.
subst l1.
rewrite Hi.
exists l'; auto.
Qed.

Lemma intersect_env_false_accept :
  forall l l', thinner_env l l' ->
  forall b l1, intersect_env false l b = Some l1 ->
  exists l1', intersect_env false l' b = Some l1' /\ thinner_env l1 l1'.
intros l l' H b l1.
destruct (intersect_case b) as
  [x e Hb Hi | e x Hb Hn Hi | a1 a2 Hb Hn1 Hn2 Hi].
rewrite (Hi false l); rewrite (Hi false l'); clear Hi.
case_eq (Ab.add_test_constraint_right false (ab_lookup l x)
          (ab_eval (ab_lookup l) e)).
intros v Hadd.
intros H'; injection H'; intros Hupdate; clear H'.
case_eq (Ab.add_test_constraint_right false (ab_lookup l' x)
           (ab_eval (ab_lookup l') e)).
intros v' Hadd'.
exists (ab_update l' x v').
split; auto.
subst l1.
apply thinner_update; auto.
apply Ab.add_test_constraint_right_monotonic with (1:= Hadd)(2:=Hadd').
apply thinner_lookup; auto.
apply thinner_eval; auto.
intros Hnone.
elim Ab.add_test_constraint_right_monotonic_none with (1:=Hadd)(v1':=ab_lookup l' x)(v2':= ab_eval (ab_lookup l') e).
apply thinner_lookup; auto.
apply thinner_eval; auto.
auto.
intros; discriminate.
rewrite (Hi false l); rewrite (Hi false l'); clear Hi.
case_eq (Ab.add_test_constraint_left false (ab_eval (ab_lookup l) e)
           (ab_lookup l x)).
intros v Hadd.
intros H'; injection H'; intros Heq; clear H'.
case_eq (Ab.add_test_constraint_left false (ab_eval (ab_lookup l') e)
           (ab_lookup l' x)).
intros v' Hadd'.
exists (ab_update l' x v'); split; auto.
subst l1.
apply thinner_update; auto.
apply Ab.add_test_constraint_left_monotonic with (1:=Hadd)(2:=Hadd').
apply thinner_eval; auto.
apply thinner_lookup; auto.
intros Hnone.
elim Ab.add_test_constraint_left_monotonic_none with
  (1:=Hadd)(v1':= ab_eval (ab_lookup l') e)(v2':=ab_lookup l' x); auto.
apply thinner_eval; auto.
apply thinner_lookup; auto.
intros; discriminate.
rewrite Hi; intros Heq'; injection Heq'; intros Heq; clear Heq'.
subst l1.
rewrite Hi.
exists l'; auto.
Qed.

Lemma thinner_intersect_env_false1 :
  forall e e' b e1 e1', thinner_env e e' -> 
    intersect_env false e b = Some e1 ->
    intersect_env false e' b = Some e1' ->
       thinner_env e1 e1'.
intros e e' b e1 e1' Ht Hi1.
destruct (intersect_env_false_accept e e' Ht b e1 Hi1) as [x [Hx Htx]].
rewrite Hx; intros He1'; injection He1'; intros; subst x; auto.
Qed.

Lemma fp1_thinner :
  forall f:ab_env->
     (a_instr* option ab_env),
    (forall e e', snd (f e) = Some e' -> compatible e e') ->
    forall e e' b i1 i3 l', thinner_env e e' ->
      fp1 e e' b i1 f = (i3, Some l') -> thinner_env e l'.
intros f Hf e e' b i1 i3 l' Hte'; unfold fp1.
assert (Hce' : compatible e e') by (apply thinner_compatible; auto).
case_eq (intersect_env true e' b); [intros l'0 Hie | idtac].
assert (Hcl'0 : compatible e' l'0) 
 by (apply compatible_intersect_env with true b; auto).
case_eq (f l'0); intros i' [l'' | ] Hf'.
assert (Hcl'' : compatible l'0 l'') by (apply Hf; rewrite Hf'; auto).
intros Heq; injection Heq; intros; subst l'.
apply thinner_join_env_left.
apply compatible_trans with e'; auto.
apply compatible_trans with l'0; auto.
apply compatible_join_env_left; auto.
intros; discriminate.
intros Hi Heq; injection Heq; intros; subst l'; auto.
Qed.

Lemma thinner_widen2 :
  forall l, thinner_env l (widen2 l).
induction l.
apply cte1.
destruct a as [s p]; simpl; apply cte2.
apply Ab.thinner_bot.
auto.
Qed.

Lemma thinner_env_trans :
  forall x y z, thinner_env x y -> thinner_env y z -> thinner_env x z.
intros x y z H; generalize z; clear z; induction H; intros z Hz; inversion Hz.
constructor.
constructor; auto.
apply Ab.thinner_trans with i2; auto.
Qed.

Lemma fp2_thinner :
  forall f:ab_env->
     (a_instr* option ab_env),
    (forall e e', snd (f e) = Some e' -> compatible e e') ->
  forall e e' b i1 i' e'', thinner_env e e' ->
  fp2 e e' b i1 f = found i' (Some e'') ->
  thinner_env e e''.
intros f Hf e e' b i1 i' e'' Hte'.
unfold fp2.
case_eq (fp1 e e' b i1 f); intros i'0 [l' | ] Hfp.
case_eq (fp1 e l' b i1 f); intros i'1 [l'' | ] Hfp'.
case (stable l' l'').
simpl.
intros Heq; injection Heq; intros; subst e''.
apply fp1_thinner with (f:=f)(3:=Hfp);auto.
intros; discriminate.
intros; discriminate.
intros; discriminate.
Qed.

Lemma thinner_widen :
  forall l l', thinner_env l (widen l l').
induction l; intros l'.
simpl; constructor.
destruct a as [s v]; simpl.
constructor; auto.
apply Ab.thinner_widen.
Qed.

Lemma fp2_cont_thinner :
  forall f,
    (forall e e', snd (f e) = Some e' -> compatible e e') ->
  forall e e' b i1 e'', thinner_env e e' ->
  fp2 e e' b i1 f = cont e'' ->
  thinner_env e e''.
intros f Hf e e' b i1 e'' Hte'.
unfold fp2.
case_eq (fp1 e e' b i1 f); intros i'0 [l' | ] Hfp.
case_eq (fp1 e l' b i1 f); intros i'1 [l'' | ] Hfp'.
case (stable l' l'').
simpl.
intros; discriminate.
intros Heq; injection Heq; intros; subst e''.
apply thinner_env_trans with l'.
apply fp1_thinner with (3:= Hfp); auto.
apply thinner_widen.
intros; discriminate.
intros; discriminate.
Qed.

Lemma fp_thinner :
  forall f,
    (forall e e', snd (f e) = Some e' -> compatible e e') ->
  forall e b i1 i3 l', fp e b i1 f = (i3,Some l') -> thinner_env e l'.
intros f Hf e b i1 i3 l'.
unfold fp.
case_eq (fp2 e e b i1 f); 
   [intros i' [l'0 |] Hfp Heq | intros l'0 Hfp]; simpl.
injection Heq; intros; subst l'.
apply fp2_thinner with (f:=f) (3:=Hfp); auto.
apply thinner_env_refl.
discriminate.
case_eq (fp2 e l'0 b i1 f);
  [intros i'1 [l'1|] Hfp' Heq | intros l'1 Hfp']; simpl.
injection Heq; intros; subst l'1.
apply fp2_thinner with (f:=f)(3:= Hfp'); auto.
apply fp2_cont_thinner with (f:=f)(3:= Hfp); auto.
apply thinner_env_refl.
discriminate.
intros Hfp''.
apply thinner_env_trans with (widen2 e).
apply thinner_widen2.
case_eq (fp1 (widen2 e)(widen2 e) b i1 f); intros a_i [l | ] Hfp1.
rewrite Hfp1 in Hfp''; injection Hfp''; do 2 intro; subst a_i l'.
apply thinner_env_refl.
rewrite Hfp1 in Hfp''; discriminate.
Qed.

Lemma join_widen2 : forall e e', compatible e e' -> (widen2 e) @@ e' = widen2 e.
induction 1; try (simpl; auto; fail).
unfold widen2, join_env; fold widen2; fold join_env;  rewrite IHcompatible.
rewrite Ab.join_comm; rewrite Ab.join_bot; auto.
Qed.

Lemma fp1_abstract_i_body_accept:
  forall f e l b i1 i' l' l'',
  fp1 e l b i1 f = (i', Some l') ->
  intersect_env true l b = Some l'' ->
  exists l''', f l'' = (i', Some l''').
intros f e l b i1 i' l' l''.
unfold fp1.
destruct (intersect_env true l b) as [l1 | ].
case_eq (f l1); intros a_i [l2 | ] Hf.
intros Heq Hi; injection Heq; do 2 intro; subst l' i'.
injection Hi; intro; subst l''; exists l2; auto.
intros; discriminate.
intros; discriminate.
Qed.

Lemma fp2_abstract_i_body_accept :
    forall f e l b i1 i' l' l'',
      fp2 e l b i1 f = found i' (Some l') ->
      intersect_env true l' b = Some l'' ->
     exists l''', f l'' = (i', Some l''').
intros f e l b i1 i' l' l''; unfold fp2.
case_eq (fp1 e l b i1 f); intros a_i [l1 | ] Hfp1.
case_eq (fp1 e l1 b i1 f); intros a_i2 [l2 | ] Hfp2.
destruct (stable l1 l2).
intros Heq; injection Heq; do 2 intro; subst i' l'.
intros.
apply fp1_abstract_i_body_accept with (1:= Hfp2); auto.
intros; discriminate.
intros; discriminate.
intros; discriminate.
Qed.

Lemma fp_abstract_i_body_accept :
  forall e b i1 i2 i3 l' l'', fp e b i1 (abstract_i i2) = (i3, Some l') ->
  intersect_env true l' b = Some l'' ->
  exists l''', abstract_i i2 l'' = (i3, Some l''').
intros e b i1 i2 i3 l' l''.
unfold fp.
case_eq (fp2 e e b i1 (abstract_i i2)); [intros a_i l1 Hfp2 | intros l1 Hfp2].
intros Heq Hi; injection Heq; do 2 intro; subst l1 a_i.
apply fp2_abstract_i_body_accept with (1:= Hfp2); auto.
case_eq (fp2 e l1 b i1 (abstract_i i2));[intros a_i2 l2 Hfp2' | intros l2 Hfp2'].
intros Heq Hi; injection Heq; do 2 intro; subst l2 a_i2.
apply fp2_abstract_i_body_accept with (1:= Hfp2'); auto.
case_eq (fp1 (widen2 e)(widen2 e) b i1 (abstract_i i2)).
intros a_i [l3 | ] Hfp1 Heq Hi.
injection Heq; do 2 intro; subst a_i l'.
apply fp1_abstract_i_body_accept with (1:= Hfp1); auto.
discriminate.
Qed.

Lemma fp1_abstract_i_body_imp_invariant :
 forall e l b i1 f i2 i3 l1 l2 l3,
 (forall l l', snd (f l) = Some l' -> compatible l l') ->
 compatible e l ->
 intersect_env true l b = Some l1 ->
 f l1 = (i3, Some l3) ->
 fp1 e l b i1 f = (i2, Some l2) ->
 thinner_env l3 l2.
intros e l b i1 f i2 i3 l1 l2 l3 Hfc Hcel Hi Hf.
unfold fp1; rewrite Hi; rewrite Hf.
assert (compatible l l1) by (apply compatible_intersect_env with true b; auto).
assert (compatible l1 l3) by (apply Hfc; rewrite Hf; auto).
intros Heq; injection Heq; do 2 intro; subst i2 l2.
apply thinner_env_trans with (join_env l1 l3).
apply thinner_join_env_right.
apply compatible_sym.
apply Hfc; rewrite Hf; auto.
apply thinner_join_env_right.
apply compatible_sym; apply compatible_trans with l; auto.
apply compatible_trans with l1; auto.
apply compatible_join_env_left; auto.
Qed.

Lemma fp2_abstract_i_body_imp_invariant :
  forall e e' b i1 i3 i4 l' l'' l''' f,
  (forall l l', snd (f l) = Some l' -> compatible l l') ->
  compatible e e' ->
  fp2 e e' b i1 f = found i3 (Some l') ->
  intersect_env true l' b = Some l'' ->
  f l'' = (i4, Some l''') ->
  thinner_env l''' l'.
intros e e' b i1 i3 i4 l' l'' l''' f Hf Hcee'.
unfold fp2.
case_eq (fp1 e e' b i1 f); intros i' [l1 | ] Hfp1.
case_eq (fp1 e l1 b i1 f); intros a_i [l2 | ] Hfp1'.
case_eq (stable l1 l2); intros Hst.
assert (Hcel1 : compatible e l1).
apply fp1_compatible with (3:= Hfp1); auto.
assert (Hcel2 : compatible e l2).
apply fp1_compatible with (3:= Hfp1'); auto.
assert (Hl1l2 : l1 = l2).
apply compatible_stable_eq; auto.
apply compatible_trans with e; auto.
apply compatible_sym; auto.
intros Heq; injection Heq; do 2 intro; subst i3 l' l1.
intros Hi Hai.
apply fp1_abstract_i_body_imp_invariant with (3:=Hi)(4:=Hai)(5:=Hfp1');auto.
intros; discriminate.
intros; discriminate.
intros; discriminate.
Qed.

Lemma fp_abstract_i_body_imp_invariant :
  forall e b i1 i3 i4 l' l'' l''' f, 
  (forall l l', snd (f l) = Some l' -> compatible l l') ->
  intersect_env true l' b = Some l'' ->
  fp e b i1 f = (i3,Some l') ->
  f l'' = (i4, Some l''') ->
  thinner_env l''' l'.
intros e b i1 i3 i4 l' l'' l''' f Hf Hi.
unfold fp.
case_eq (fp2 e e b i1 f); 
  [intros i' [l1 | ] Hfp2 Heq Hai| intros l1 Hfp2].
injection Heq; do 2 intro; subst i3 l'.
apply fp2_abstract_i_body_imp_invariant with (3:= Hfp2)(4:=Hi)(5:=Hai);auto.
apply compatible_refl.
discriminate.
case_eq (fp2 e l1 b i1 f);
  [intros i2' [l2 | ] Hfp2' Heq Hai | intros l2 Hfp2'].
injection Heq; do 2 intro; subst i3 l'.
apply fp2_abstract_i_body_imp_invariant with (3:= Hfp2')(4:=Hi)(5:=Hai);auto.
apply fp2_compatible2 with (2 := Hfp2); auto.
apply compatible_refl.
intros; discriminate.
case_eq (fp1 (widen2 e) (widen2 e) b i1 f); intros i' [_l | ] Hfp1 Heq Hai.
injection Heq; do 2 intro; subst i3 l'.
apply compatible_thinner_widen2.
apply compatible_sym; apply compatible_trans with (widen2 e).
apply compatible_widen2.
apply compatible_trans with l''.
apply compatible_intersect_env with true b; auto.
apply Hf; rewrite Hai; auto.
discriminate.
Qed.

Lemma vcg_shift :
   forall m i p q, (forall g, i_lc m g (vcg i p)) -> (forall g, i_c m g (c_imp p q)) -> 
        forall g, (i_c m g (c_imp (pc i p) (pc i q)) /\
        i_lc m g (vcg i q)).
Proof.
intros m' i; induction i.
simpl; intros p q Hv Hpq g; split; auto.
assert (Hi' := IHi p q).
assert (Hv2 : forall g, i_lc m' g (vcg i p)) by (intros g'; elim (Hv g'); auto).
destruct (Hi' Hv2 Hpq g) as [Hi1 Hi2]; simpl in Hi1; clear Hi'.
split; elim (Hv g); auto.

simpl; intros p q Hv Hpq g; split; auto.

simpl; intros p q Hv Hpq g; split; auto.
repeat rewrite a_subst_fpw; auto.

simpl; intros p q Hv Hpq g; auto.
assert (IHi2' := IHi2 p q).
assert (Hv1 : forall g, i_lc m' g (vcg i2 p)).
intros g'; apply i_lc_app_l with (1:= Hv g').
assert (Hi2_1 : forall g, i_c m' g (c_imp (pc i2 p)(pc i2 q))).
intros g'; elim (IHi2' Hv1 Hpq g'); auto.
assert (Hv2 : forall g, i_lc m' g (vcg i1 (pc i2 p))).
intros g'; apply i_lc_app_r with (1:= Hv g').
destruct (IHi1 (pc i2 p)(pc i2 q) Hv2 Hi2_1 g) as
  [Hi1_1 Hi1_2].
split;[exact Hi1_1 | apply app_i_lc; auto].
elim (IHi2' Hv1 Hpq g); auto.

simpl; intros p q Hv Hpq; intros g; split.
auto.
destruct (Hv g) as [Hv1 [Hv2 Hv3]].
split.
intros; apply Hpq; auto.
auto.
Qed.

Lemma thinner_env_to_a1 :
  forall l1 l2, thinner_env l1 l2 ->
  forall g l, i_a Ab.m g (to_a1 l1 l) ->
    i_a Ab.m g (to_a1 l2 l).
induction 1; intros g l;  simpl.
auto.
case (str_in_list s l).
auto.
destruct (to_syn i1); destruct (to_syn i2).
simpl; intros [H' H'']; split; auto.
i_a_to_to_p.
apply Ab.thinner_prop with (1:= H); auto.
to_p_to_i_a; auto.
Qed.

Lemma thinner_env_to_a :
  forall l1 l2, thinner_env l1 l2 ->
  forall g, i_a Ab.m g (to_a l1) ->
   i_a Ab.m g (to_a l2).
intros l1 l2 Ht g; apply (thinner_env_to_a1 l1 l2 Ht g nil).
Qed.

Lemma fp_monotonic_entry :
  forall g e b i1 i2 i3 l, fp e b i1 (abstract_i i2) = (i3, Some l) ->
  i_a Ab.m g (to_a e) -> i_a Ab.m g (to_a l).
intros g e b i1 i2 i3 l H.
apply thinner_env_to_a.
apply fp_thinner with (f:= abstract_i i2) (2:=H).
exact (abstract_i_compatible i2).
Qed.

Lemma mark_pc : forall i, pc (mark i) false_assert = false_assert.
induction i; simpl; auto.
rewrite IHi2; auto.
Qed.

Lemma mark_sound : forall i g, i_lc Ab.m g (vcg (mark i) false_assert).
intros i g; induction i; simpl; auto.
rewrite mark_pc; apply app_i_lc; auto.
rewrite mark_pc; rewrite f_p_lookup; rewrite false_top; intuition.
Qed.

Lemma fp1_invariant_init :
   forall e l b i f i',
      compatible e l ->
      fp1 e l b i f = (i', Some l) ->
      fp1 l l b i f = (i', Some l).
intros e l b i f i' Hc; unfold fp1.
destruct (intersect_env true l b); try (simpl; auto; fail).
destruct (f a) as [i'' [ l'' | ]]; try (intros; discriminate).
intros Heq; injection Heq; intros Hl Hi'; subst i'; clear Heq.
rewrite <- Hl.
rewrite join_env_assoc; rewrite join_env_involutive; auto.
Qed.

Lemma fp2_invariant : forall e e' b i f l i', 
     (forall e e', snd(f e) = Some e' -> compatible e e') ->
   compatible e e' -> fp2 e e' b i f = found i' (Some l) ->
   fp2 l l b i f = found i' (Some l).
intros e e' b i f l i' Hf Hce'; unfold fp2.
case_eq (fp1 e e' b i f); intros i1 l1 Heqfp1; destruct l1 as [l1 | ];
  try(intros; discriminate).
case_eq (fp1 e l1 b i f); intros i2 l2 Heqfp1_2; destruct l2 as [l2 | ];
  try(intros; discriminate).
case_eq (stable l1 l2); intros Hstable; try (intros; discriminate).
intros Heq; injection Heq; do 2 intro; subst i2 l1; clear Heq.
assert (compatible e l) by
  (apply fp1_compatible with (f:=f) (l1:=e')(i1:=i)(b:=b)(i':=i1); auto).
assert (l = l2). 
apply compatible_stable_eq; auto.
apply compatible_trans with e.
apply compatible_sym; auto.
apply fp1_compatible with (f:=f) (l1:=l)(i1:=i)(b:=b)(i':=i'); auto.
subst l2.
rewrite fp1_invariant_init with (2:=Heqfp1_2); auto.
rewrite fp1_invariant_init with (2:=Heqfp1_2); auto.
rewrite Hstable; auto.
Qed.

Lemma fp1_widen2_invariant :  forall e b i i' l, 
  fp1 (widen2 e)(widen2 e) b i (abstract_i i) = (i', Some l) -> l = widen2 e.
intros e b i i' l; unfold fp1.
case_eq (intersect_env true (widen2 e) b);
  [intros a Hinter| intros Hinter] ; simpl.
case_eq (abstract_i i a); intros i'0 [l'' | ] Ha; 
  try (intros; discriminate).
intros Heq; injection Heq; do 2 intro; subst l i'; clear Heq.
rewrite join_widen2; auto. 
assert (compatible a l'') by
   (apply (abstract_i_compatible i a l''); rewrite Ha; auto).
apply compatible_trans with a.
apply compatible_trans with (widen2 e).
apply compatible_widen2.
apply compatible_intersect_env with (1:=Hinter).
apply compatible_join_env_left; auto.
intros Heq; injection Heq; do 2 intro; subst l; auto.
Qed.

Lemma fp2_widen2_eq_fp1 :
  forall e b i i', 
    fp1 (widen2 e)(widen2 e) b i (abstract_i i) = (i', Some (widen2 e)) ->
    fp2 (widen2 e)(widen2 e) b i (abstract_i i) = found i' (Some(widen2 e)).
intros e b i i' Hfp1; unfold fp2; repeat rewrite Hfp1; rewrite stable_refl; auto.
Qed.

Lemma fp_invariant : forall e b i i2 l', fp e b i (abstract_i i) = (i2, Some l') ->
          fp l' b i (abstract_i i) = (i2, Some l').
intros e b i i2 l'; unfold fp.
case_eq (fp2 e e b i (abstract_i i)); [intros i1 l1 | intros l1]; intros Hfp2.
intros Heq; injection Heq; do 2 intro; subst i1 l1; clear Heq.
rewrite fp2_invariant with (3:=Hfp2); auto.
apply abstract_i_compatible.
apply compatible_refl.
assert (Hac :=abstract_i_compatible i).
case_eq (fp2 e l1 b i (abstract_i i)).
intros i' l2 Hfp2_2 Heq;injection Heq; do 2 intro; subst i' l2; clear Heq.
rewrite fp2_invariant with (e:= e)(e':=l1)(f:=abstract_i i)(i':=i2); auto.
apply fp2_compatible2 with (2:=Hfp2); auto.
apply compatible_refl.
intros l2 Hfp2_2.
case_eq (fp1 (widen2 e)(widen2 e) b i (abstract_i i));
intros i' [l3 | ] Hfp1 Heq; try (intros; discriminate).
injection Heq; do 2 intro; subst l' i2; clear Heq.
rewrite fp1_widen2_invariant with (1:=Hfp1) in Hfp1.
rewrite fp2_widen2_eq_fp1 with (1:=Hfp1); auto.
Qed.

Lemma fp1_none_precondition : 
  forall e e' b i i' a e'', fp1 e e' b i (abstract_i i) = (i', None) ->
  intersect_env true e' b = Some e'' ->  pc i' a = to_a e''.
intros e e' b i i' a e''; unfold fp1.
destruct (intersect_env true e' b).
case_eq (abstract_i i a0); intros i1 [l | ]; try (intros; discriminate).
intros Hai Heq; injection Heq; intro; subst i1.
intros Heq'; injection Heq'; intro; subst a0.
assert (Hai' : fst (abstract_i i e'') = i') by (rewrite Hai; auto).
rewrite <- Hai'.
apply abstract_i_pre_condition.
intros; discriminate.
Qed.

Lemma fp1_none_start : 
   forall e e' b i i2, fp1 e e' b i (abstract_i i) = (i2, None) ->
     exists e2, intersect_env true e' b = Some e2 /\
      abstract_i i e2 = (i2,None).
intros e e' b i i2; unfold fp1.
case_eq (intersect_env true e' b); [intros e2 Heq | intros; discriminate].
exists e2; destruct (abstract_i i e2) as [i' [l' | ]]; 
  try(intros; discriminate); auto.
Qed.

Lemma fp2_none_start_found :
  forall e e' b i i2, 
     fp2 e e' b i (abstract_i i) = found i2 None ->
     thinner_env e e' ->
     exists l, exists e2, abstract_i i e2 = (i2, None) /\
     thinner_env e l /\ intersect_env true l b = Some e2.
intros e e' b i i2; unfold fp2.
case_eq (fp1 e e' b i (abstract_i i)); intros i' [l' | ] Hfp1.
case_eq (fp1 e l' b i (abstract_i i)); intros i'' [l'' | ] Hfp1_2.
destruct (stable l' l''); try(simpl; intros; discriminate).
intros Heq; injection Heq; intro; subst i''.
elim fp1_none_start with (1:= Hfp1_2).
intros e2 [Hinter Hai] Hth; exists l'; exists e2; split; auto.
split; auto.
apply fp1_thinner with (3:= Hfp1).
apply abstract_i_compatible.
assumption.
intros Heq Hth; injection Heq; intro; subst i'.
elim fp1_none_start with (1:= Hfp1).
intros e2 [Hinter Hai]; exists e'; exists e2; auto.
Qed.

Lemma fp_none_start :
  forall e b i i2, fp e b i (abstract_i i) = (i2, None) -> 
    exists e', exists e2, 
     abstract_i i e2 = (i2,None) /\ thinner_env e e' /\
     intersect_env true e' b = Some e2.
intros e b i i2; unfold fp.
case_eq (fp2 e e b i (abstract_i i));
  [intros i' [l' | ] Hfp2 Heq| intros e' Hfp2];
  try(intros; discriminate).
injection Heq; intro; subst i'.
elim fp2_none_start_found with (1:=Hfp2).
intros e' [e2 [Hai [Hth Hinter]]].
exists e'; exists e2; auto.
apply thinner_env_refl.
case_eq (fp2 e e' b i (abstract_i i));
 [intros i' [l'' | ] Hfp2_2 Heq | intros l'' Hfp2_2];
 try(intros; discriminate).
injection Heq; intro; subst i'.
elim fp2_none_start_found with (1:=Hfp2_2).
intros l' [e2 [Hai [Hth Hinter]]].
exists l'; exists e2; split; auto.
apply fp2_cont_thinner with (f:=abstract_i i)(3:= Hfp2); auto.
apply abstract_i_compatible.
apply thinner_env_refl.
case_eq (fp1 (widen2 e) (widen2 e) b i (abstract_i i));
  intros i' [l3 |] Hfp1 Heq; try discriminate.
injection Heq; intro; subst i'.
elim fp1_none_start with (1:= Hfp1).
intros e2 [Hinter Hai]; exists (widen2 e); exists e2; split; auto.
split; auto.
apply thinner_widen2.
Qed.

Theorem abstract_i_sound : forall i e i' e', 
  abstract_i i e = (i', e') -> forall g, i_lc m  g (vcg i' (to_a' e')).
induction i.
simpl; intros e i' e' Heq; injection Heq; intros; subst i' e'; simpl; split; auto.
intros Hyp; apply i_a_ab_update; auto.
apply ab_eval_i_a; auto.

simpl; intros e i' e'.
assert (IHi1' := IHi1 e); clear IHi1.
destruct (abstract_i i1 e) as [i'1 [l' | ]].
assert (Hpc:= abstract_i_pre_condition i2 l').
assert (IHi2' := IHi2 l'); clear IHi2.
destruct (abstract_i i2 l') as [i'2 [l'' | ]].
intros Heq; injection Heq; do 2 intro; subst i' e'; simpl.
intros g; simpl; apply app_i_lc.
apply (IHi2' i'2 (Some l'')); auto.
simpl in Hpc; rewrite Hpc; apply (IHi1' i'1 (Some l')); auto.
intros Heq; injection Heq; intros Hi' He'; subst i' e'.
intros g; simpl; apply app_i_lc.
apply IHi2' with (i':=i'2)(e':= (@None ab_env)); auto.
simpl in Hpc; rewrite Hpc; apply (IHi1' i'1 (Some l')); auto.
intros Heq; injection Heq; intros Hi' He'; subst i' e'.
intros g; simpl; split.
rewrite f_p_lookup; rewrite false_top; intuition.
apply app_i_lc.
apply mark_sound.
apply (IHi1' i'1 (@None ab_env)); auto.

simpl; intros e i' e'.
case_eq (intersect_env true e b).
intros l Hl.
case_eq (fp e b i (abstract_i i)).
intros i2 [l' | ] Hfp.
case_eq (intersect_env false l' b).
intros l'' Hneg Heq; 
injection Heq; do 2 intro; subst i' e'; intros g.
simpl.
split.
apply fp_monotonic_entry with (1:= Hfp).
split.
intros [Hb Hl']; change (to_a l'') with (to_a' (Some l'')).
rewrite <- Hneg; apply intersect_env_false_i_a; auto.
split.
exact (fp_precondition e b i i i2 l' Hfp g).
assert(Hel':=fp_thinner (abstract_i i)(abstract_i_compatible i) _ _ _ _ _ Hfp).
destruct (intersect_env_true_accept e l' Hel' b l Hl) as [l0 [Hl0 Hthl0]].
destruct (fp_abstract_i_body_accept
                 _ _ _ _ _ l' l0 Hfp Hl0) as [l1 Hl1].
assert (IHi' := IHi l0 i2 (Some l1) Hl1).
assert (Hl1l' := fp_abstract_i_body_imp_invariant e b i i2 i2 _ _ _
               (abstract_i i) (abstract_i_compatible i) Hl0 Hfp Hl1).
assert (Hl1l'_c : forall g, i_c Ab.m g (c_imp (to_a l1)(to_a l')))
  by exact (thinner_env_prop _ _ Hl1l').
destruct (vcg_shift _ _ (to_a l1)(to_a l') IHi' Hl1l'_c g); auto.
intros Hinter Heq; injection Heq; do 2 intro; subst i' e'.
simpl; intros g; split.
apply (fp_monotonic_entry g e b i i i2 l');auto.
split.
intros [Hnt Hia]; change (i_a m g (to_a' None)); rewrite <- Hinter.
apply intersect_env_false_i_a; auto.
split.
intros [Hb Hia]; apply fp_precondition with (1:=Hfp); simpl; auto.
assert(Hel':=fp_thinner (abstract_i i)(abstract_i_compatible i) _ _ _ _ _ Hfp).
destruct (intersect_env_true_accept e l' Hel' b l Hl) as [l0 [Hl0 Hthl0]].
destruct (fp_abstract_i_body_accept
                 _ _ _ _ _ l' l0 Hfp Hl0) as [l1 Hl1].
assert (IHi' := IHi l0 i2 (Some l1) Hl1).
assert (Hl1l' := fp_abstract_i_body_imp_invariant e b i i2 i2 _ _ _
               (abstract_i i) (abstract_i_compatible i) Hl0 Hfp Hl1).
assert (Hl1l'_c : forall g, i_c Ab.m g (c_imp (to_a l1)(to_a l')))
  by exact (thinner_env_prop _ _ Hl1l').
destruct (vcg_shift m i2 (to_a l1)(to_a l') IHi' Hl1l'_c g); auto.
intros Heq; injection Heq; do 2 intros; subst i' e'; clear Heq.
simpl.
split; auto.
split.
intros [Hnt Hia]; apply intersect_env_false_i_a; auto.
elim fp_none_start with (1:= Hfp).
intros e' [e2 [Hai [Hth Hinter]]].
assert (Hpc := abstract_i_pre_condition i e2 (to_a e)).
rewrite Hai in Hpc; simpl in Hpc; rewrite Hpc.
change (to_a e2) with (to_a' (Some e2)).
rewrite <- Hinter.
split.
intros [Hb Hia].
apply  intersect_env_true_i_a.
apply thinner_env_prop with e; auto.
exact Hb.
assert (HFalse_e: forall g, i_c Ab.m g (c_imp (to_a' None) (to_a e)))
 by (simpl; rewrite f_p_lookup; rewrite false_top; intuition).
assert (IHi' := IHi e2 i2 None Hai).
destruct (vcg_shift m i2 (to_a' None)(to_a e) IHi' HFalse_e g); auto.

intros Hinter Heq; injection Heq; do 2 intro; subst e' i'; simpl.
intros g.
split.
intros Hyp; split; auto.
intros Habs.
assert (Habs' : i_a Ab.m g (a_b b)) by exact Habs.
assert (i_a Ab.m g (to_a' None)).
rewrite <- Hinter; apply intersect_env_true_i_a; auto.
elim intersect_env_true_none with (1:=Hinter)(2:=Hyp);auto.
split.
intuition.
split.
intuition.

assert (Hi := fun g => i_lc_vcg_mark g i).
assert (Ha : forall g, i_c Ab.m g
              (c_imp false_assert (a_conj (a_not (a_b b))(to_a e)))).
simpl; intros g'; rewrite f_p_lookup; intros Hf.
rewrite Ab.false_top in Hf; intuition.

destruct (vcg_shift Ab.m (mark i) false_assert
                  (a_conj (a_not (a_b b))(to_a e)) Hi Ha g)
  as [Hv1 Hv2]; auto.

simpl; intros e i' e' Heq; injection Heq; do 2 intro; subst i' e'; simpl; auto.
Qed.

End abi.

Module Ab_intervals <: Abstract_domain.

Definition t := (intervals.ext_Z*intervals.ext_Z)%type.
Definition bot := intervals.bot.
Definition plus := intervals.plus.
Definition of_int := intervals.of_int.
Definition join := intervals.join.
Definition add_test_constraint_right := intervals.add_test_constraint_right.
Definition add_test_constraint_left := intervals.add_test_constraint_left.
Definition widen := intervals.widen.
Definition eq := intervals.eq.
Definition thinner := intervals.thinner.
Definition thinner_refl := intervals.thinner_refl.
Definition thinner_trans := intervals.thinner_trans.
Definition thinner_bot := intervals.thinner_bot.
Definition thinner_plus := intervals.thinner_plus.
Definition to_p := intervals.to_p.
Definition thinner_prop := intervals.thinner_prop.
Definition bot_semantics := intervals.bot_semantics.
Definition plus_correct := intervals.plus_correct.
Definition of_int_correct := intervals.of_int_correct.
Definition add_test_constraint_right_true_none := 
  intervals.add_test_constraint_right_true_none.
Definition add_test_constraint_left_true_none := 
  intervals.add_test_constraint_left_true_none.
Definition add_test_constraint_right_false_none := 
  intervals.add_test_constraint_right_false_none.
Definition add_test_constraint_left_false_none := 
  intervals.add_test_constraint_left_false_none.
Definition add_test_constraint_right_true_sound := 
  intervals.add_test_constraint_right_true_sound.
Definition add_test_constraint_left_true_sound := 
  intervals.add_test_constraint_left_true_sound.
Definition add_test_constraint_right_false_sound := 
  intervals.add_test_constraint_right_false_sound.
Definition add_test_constraint_left_false_sound := 
  intervals.add_test_constraint_left_false_sound.
Definition thinner_join := intervals.thinner_join.
Definition thinner_join_left := intervals.thinner_join_left.
Definition join_comm := intervals.join_comm.
Definition join_assoc := intervals.join_assoc.
Definition join_involutive := intervals.join_involutive.
Definition join_bot := intervals.join_bot.
Definition eq_sound := intervals.eq_sound.
Definition eq_complete := intervals.eq_complete.
Definition add_test_constraint_right_monotonic :=
  intervals.add_test_constraint_right_monotonic.
Definition add_test_constraint_left_monotonic :=
  intervals.add_test_constraint_left_monotonic.
Definition add_test_constraint_right_monotonic_none :=
  intervals.add_test_constraint_right_monotonic_none.
Definition add_test_constraint_left_monotonic_none :=
  intervals.add_test_constraint_left_monotonic_none.
Definition thinner_widen := intervals.thinner_widen.
Import intervals.
Definition to_syn (v:ext_Z*ext_Z) :=
  match v with
    (minfty,pinfty) => (true_cst, nil)
  | (minfty, cZ u) => (ge_cst, u::nil)
  | (cZ l, pinfty) => (le_cst, l::nil)
  | (cZ l, cZ u) => (between_cst, l::u::nil)
  | _ => (false_cst, nil)
  end.

Definition m : list (string*(list Z->Prop)) :=
  (between_cst, fun l => match l with l::u::x::nil => l <= x <= u | _ => False end)::
  (false_cst, fun _ => False)::
  (ge_cst, fun l => match l with u::x::nil => x <= u | _ => False end)::
  (le_cst, fun l => match l with l::x::nil => l <= x | _ => False end)::
  (true_cst, fun l => True)::nil.

(* A tactic to handle the equality tests in programs. *)
(* This tactic suppose that the first premise in the goal is
  an equality or disequality, as generated by string_dec. *)
Ltac decide_strings :=
  match goal with
    |- context[string_dec ?x ?x] =>
       case (string_dec x x);
         [intros _ | 
          intros Habsurd_decide_strings; case Habsurd_decide_strings; trivial]
  | |-  context[string_dec ?x ?y] =>
        case (string_dec x y);
          [intros Habsurd_decide_strings;
           case (@lt_irrefl x);
           pattern x at 2; rewrite Habsurd_decide_strings;
           destruct all_distinct as
           [Hdecide_strings1 [Hdecide_strings2 [Hdecide_strings3 
            Hdecide_strings4]]]; auto;
           repeat match goal with id : _ |- _ =>
                   apply lt_trans with (1:=id); try assumption
                  end  | intros _]
  end.


Lemma to_syn_ok : 
  forall v x s l p, to_syn v = (s,l) -> 
    syntax.lookup string_dec m (fun l => True) s = p ->
    to_p v x = p (l++x::nil).
unfold to_syn, m; intros [[lb | | ][ub | | ]] x  s l p H; injection H; intros Hl Hs;
 subst s l; simpl; repeat decide_strings; intros Hp; subst p; simpl; auto.
Qed.

Lemma false_top : forall l,
    syntax.lookup string_dec m (fun l => True) false_cst l = False.
unfold m; simpl; repeat decide_strings; auto.
Qed.

End Ab_intervals.

Module B := abi(Ab_intervals).

End ab.
