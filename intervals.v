From Stdlib Require Import ZArith List Lia.
Open Scope Z_scope.
Open Scope list_scope.

Ltac intuition1 := intuition auto with core zarith.

Inductive ext_Z :Type :=
  cZ : Z -> ext_Z | minfty : ext_Z | pinfty : ext_Z.

Definition bot := (minfty, pinfty).
Definition comp_add (x y:ext_Z) : ext_Z :=
  match x,y with
    minfty, _ => minfty
  | _, minfty => minfty
  | pinfty, _ => pinfty
  | _, pinfty => pinfty
  | cZ x, cZ y => cZ(x+y)
  end.

Definition plus (i1 i2:ext_Z*ext_Z) : ext_Z*ext_Z :=
  let (l1,u1) := i1 in  let (l2,u2) := i2 in (comp_add l1 l2, comp_add u1 u2).

Definition of_int (x:Z) := (cZ x, cZ x).

(* compute the minimum of two ext_Z *)
Definition cp_min (n1 n2:ext_Z) : ext_Z :=
  match n1, n2 with
    minfty, a => minfty
  | cZ n1, cZ n2 => cZ (Z.min n1 n2)
  | _, minfty => minfty
  | a, pinfty => a
  | pinfty, a => a
  end.

(* compute the maximum of two ext_Z *)
Definition cp_max (n1 n2:ext_Z) : ext_Z :=
  match n1, n2 with
    minfty, a => a
  | cZ n1, cZ n2 => cZ (Z.max n1 n2)
  | a, minfty => a
  | pinfty, _ => pinfty
  | _, pinfty => pinfty
  end.

Lemma Zle_to_Zmin : forall n m, n <= m -> Z.min n m = n.
intros n n'; unfold Z.min, Z.le.
case (n?=n'); intuition1.
Qed.

Lemma Zle_to_Zmax : forall n m, m <= n -> Z.max n m = n.
intros n n'; unfold Z.max.
intros Hle; cut (n >= n').
unfold Z.ge.
case_eq (n ?= n'); intros Heq H; try (elim H; auto; fail).
rewrite Zcompare_Eq_eq with (1:=Heq); auto.
auto.
lia.
Qed.

Lemma cp_min_assoc :
  forall a b c, cp_min (cp_min a b) c = cp_min a (cp_min b c).
intros [a | | ]; simpl; auto; intros [b | |]; simpl; auto; intros [c| |]; simpl; auto.
rewrite Z.min_assoc; auto.
Qed.

Lemma cp_max_assoc :
  forall a b c, cp_max (cp_max a b) c = cp_max a (cp_max b c).
intros [a | | ]; simpl; auto; intros [b | |]; simpl; auto; intros [c| |]; simpl; auto.
rewrite Z.max_assoc; auto.
Qed.

Lemma cp_max_r_cp_min_l :
  forall a b, cp_max a b = b -> cp_min a b = a.
intros [a | | ][b | | ]; simpl; auto.
intros H; injection H; intros H1.
assert (a <= b) by (rewrite <- H1; apply Z.le_max_l).
rewrite Zle_to_Zmin; auto.
Qed.

Lemma cp_min_r_cp_max_l :
  forall a b, cp_min a b = b -> cp_max a b = a.
intros [a | | ][b | | ]; simpl; auto.
intros H; injection H; intros H1.
assert (b <= a) by (rewrite <- H1; apply Z.le_min_l).
rewrite Zle_to_Zmax; auto.
Qed.

Definition join (i1 i2:ext_Z*ext_Z) : ext_Z*ext_Z :=
  let (l1, u1):= i1 in let (l2, u2) := i2 in (cp_min l1 l2, cp_max u1 u2).

Definition ext_eq : forall a b:ext_Z, {a=b}+{a<>b}.
intros a b; destruct a as [na | | ]; destruct b as [nb | | ];
try (left; apply refl_equal); try (right; discriminate).
case (Z.eq_dec na nb); intros Heq; (left; rewrite Heq; apply refl_equal) ||
 (right; intros H'; elim Heq; injection H'; auto).
Defined.

Definition add_test_constraint_right (d:bool) (i j:ext_Z*ext_Z) : option (ext_Z*ext_Z) :=
  let (bi, ui):=i in let (bj, uj):=j in
  (if d then
    let ujm1 := comp_add uj (cZ (-1)) in
    if ext_eq bi (cp_max bi uj) then None
    else Some (bi, cp_min ui ujm1)
  else
    let v := cp_max ui bj in
    if ext_eq bj v then
      if ext_eq ui v then Some(cp_max bi bj,ui)
      else None
    else Some (cp_max bi bj, ui)).

Definition add_test_constraint_left (d:bool) (i j:ext_Z*ext_Z) : option (ext_Z*ext_Z) :=
  let (bi, ui):=i in let (bj, uj):=j in
  (if d then
    let bip1 := comp_add bi (cZ 1) in
    if ext_eq uj (cp_min bi uj) then None
    else Some (cp_max bip1 bj, uj)
  else
    let v := cp_max ui bj in
    if ext_eq bj v then
      if ext_eq ui v then Some(bj,cp_min ui uj)
      else None
    else Some (bj, cp_min ui uj)).

Definition widen (i j:ext_Z*ext_Z) :=
  let (bi, ui) := i in let (bj, uj) := j in
  let b :=
    if ext_eq (cp_min bi bj) bi then bi
    else minfty in
  let u :=
    if ext_eq (cp_max ui uj) ui then ui
    else pinfty in
    (b,u).

Definition eq (i j:ext_Z*ext_Z) : bool :=
  let (bi,ui) := i in let (bj,uj) := j in
  if ext_eq bi bj then if ext_eq ui uj then true else false else false.

Definition thinner (i j : ext_Z*ext_Z) : Prop :=
   let (bi,ui) := i in let (bj,uj) := j in
   cp_min bi bj = bj /\ cp_max ui uj = uj.

Lemma cp_min_comm : forall i j, cp_min i j = cp_min j i.
intros [ni | | ] [nj | | ];simpl; auto.
rewrite Z.min_comm; auto.
Qed.

Lemma cp_max_comm :
   forall x y, cp_max x y = cp_max y x.
Proof.
intros [x | | ] [y | | ]; simpl; auto.
rewrite Z.max_comm; auto.
Qed.

Lemma thinner_refl : forall v, thinner v v.
intros [[b | | ] [u| |]]; simpl; auto;
  try rewrite Zmax_idempotent; try rewrite Zmin_idempotent; auto.
Qed.

Lemma cp_min_trans :
  forall x y z, cp_min x y = x -> cp_min y z = y -> cp_min x z = x.
intros [x | | ] [y| |]; try (simpl; intros; discriminate);
intros [z | | ]; try(simpl; intros; discriminate); simpl; auto.
intros H1 H2; injection H1; injection H2; intros H3 H4.
rewrite Zle_to_Zmin; auto.
apply Z.le_trans with y.
rewrite <-H4; auto with zarith.
rewrite <- H3; auto with zarith.
Qed.

Lemma cp_max_trans :
  forall x y z, cp_max x y = x -> cp_max y z = y -> cp_max x z = x.
intros [x | | ] [y| |]; try (simpl; intros; discriminate);
intros [z | | ]; try(simpl; intros; discriminate); simpl; auto.
intros H1 H2; injection H1; injection H2; intros H3 H4.
rewrite Zle_to_Zmax; auto.
apply Z.le_trans with y.
rewrite <- H3; apply Z.le_max_r.
rewrite <-H4; apply Z.le_max_r.
Qed.

Lemma thinner_trans : forall v1 v2 v3, thinner v1 v2 ->
 thinner v2 v3 -> thinner v1 v3.
unfold thinner; intros [b1 u1] [b2 u2] [b3 u3] [H1 H2] [H3 H4].
split.
rewrite cp_min_comm; apply cp_min_trans with b2; rewrite cp_min_comm; auto.
rewrite cp_max_comm; apply cp_max_trans with u2; rewrite cp_max_comm; auto.
Qed.

Lemma thinner_bot : forall v, thinner v bot.
unfold bot; intros [[a | | ][b | | ]]; unfold thinner; simpl; auto.
Qed.

Lemma cp_min_plus :
  forall x y z t,
    cp_min x y = x -> cp_min z t = z ->
    cp_min (comp_add x z)(comp_add y t)= comp_add x z.
intros [x | | ] [y | | ];simpl;try (intros;discriminate);
intros [z | | ] [t' | | ];simpl; try (intros; discriminate); auto.
intros H1 H2; injection H1; injection H2; intros H4 H3.
apply f_equal with (f:=cZ); apply Zle_to_Zmin.
apply Z.le_trans with (x + t').
apply Zplus_le_compat_l; rewrite <- H4; apply Z.le_min_r.
apply Zplus_le_compat_r; rewrite <- H3; apply Z.le_min_r.
Qed.

Lemma cp_max_plus :
  forall x y z t,
    cp_max x y = x -> cp_max z t = z ->
    cp_max (comp_add x z)(comp_add y t)= comp_add x z.
intros [x | | ] [y | | ];simpl;try (intros;discriminate);
intros [z | | ] [t' | | ];simpl; try (intros; discriminate); auto.
intros H1 H2; injection H1; injection H2; intros H4 H3.
apply f_equal with (f:=cZ); apply Zle_to_Zmax.
apply Z.le_trans with (x + t').
apply Zplus_le_compat_r; rewrite <- H3; apply Z.le_max_r.
apply Zplus_le_compat_l; rewrite <- H4; apply Z.le_max_r.
Qed.

Lemma thinner_plus :
   forall x y z t, thinner x y -> thinner z t ->
     thinner (plus x z)(plus y t).
intros [lx ux] [ly uy] [lz uz] [lt' ut] [H1 H2][H3 H4]; split; simpl.
rewrite cp_min_comm; apply cp_min_plus; rewrite cp_min_comm; auto.
rewrite cp_max_comm; apply cp_max_plus; rewrite cp_max_comm; auto.
Qed.

Lemma cp_max_refl : forall x, cp_max x x = x.
intros [x | | ]; simpl; unfold Z.max; auto.
rewrite Z.compare_refl; auto.
Qed.

Lemma cp_min_refl : forall x, cp_min x x = x.
intros [x | | ]; simpl; unfold Z.min; auto.
rewrite Z.compare_refl; auto.
Qed.

Lemma eq_sound : forall x y, eq x y = true -> x = y.
intros [b1 u1][b2 u2]; unfold eq; case (ext_eq b1 b2); case (ext_eq u1 u2);
 try (intros; discriminate).
intros; subst; auto.
Qed.

Lemma eq_complete : forall x, eq x x = true.
intros [[l | |][u| |]]; simpl; auto;
try case (Z.eq_dec l l); try case (Z.eq_dec u u); intros; auto;
try match goal with id :~_ |- _ => case id; apply refl_equal end.
Qed.

Lemma join_bot : forall i, join i bot = bot.
intros [[b | |]  [u | | ]]; unfold bot; simpl; auto.
Qed.

Lemma thinner_join :
  forall e1 e2 e3 e4, thinner e1 e2 -> thinner e3 e4 ->
  thinner (join e1 e3)(join e2 e4).
intros [l1 u1] [l2 u2] [l3 u3][l4 u4]; unfold thinner; simpl;
 intros [H1 H2][H3 H4]; unfold join; split; simpl.
destruct l1 as [l1 | | ]; destruct  l2 as [l2 | | ];
 simpl in H1, H2, H3, H4 |- *; try discriminate; auto;
destruct l3 as [l3 | | ]; simpl in H1, H2, H3, H4 |- *; try discriminate; auto;
destruct l4 as [l4 | | ]; simpl in H1, H2, H3, H4 |- *; try discriminate; auto.
rewrite Z.min_assoc; rewrite <- (Z.min_assoc l1 l3 l2); rewrite (Z.min_comm l3 l2).
injection H1; injection H3; clear H1 H3; intros H3 H1.
rewrite Z.min_assoc; rewrite H1; rewrite <- Z.min_assoc; rewrite H3; auto.
injection H1; clear H1; intros H1; rewrite Z.min_assoc; rewrite H1; auto.
injection H3; clear H3; intros H3; rewrite Z.min_assoc; rewrite (Z.min_comm l3).
rewrite <- Z.min_assoc; rewrite H3; auto.

destruct u1 as [u1 | | ]; destruct  u2 as [u2 | | ];
 simpl in H1, H2, H3, H4 |- *; try discriminate; auto;
destruct u3 as [u3 | | ]; simpl in H1, H2, H3, H4 |- *; try discriminate; auto;
destruct u4 as [u4 | | ]; simpl in H1, H2, H3, H4 |- *; try discriminate; auto.
injection H2; injection H4; clear H2 H4; intros H4 H2.
rewrite Z.max_assoc; rewrite <- (Z.max_assoc u1); rewrite (Z.max_comm u3).
rewrite Z.max_assoc; rewrite H2; rewrite <- Z.max_assoc; rewrite H4; auto.
injection H2; clear H2; intros H2; rewrite Z.max_assoc; rewrite H2; auto.
injection H4; clear H4; intros H4; rewrite Z.max_assoc; rewrite (Z.max_comm u3).
rewrite <- Z.max_assoc; rewrite H4; auto.
Qed.

Lemma thinner_join_left :  forall i i', thinner i (join i i').
intros [b1 u1] [b2 u2]; split.
destruct b1 as [l | | ]; destruct b2 as [l' | | ]; simpl; auto.
rewrite Z.min_assoc; rewrite Zmin_idempotent; auto.
rewrite Zmin_idempotent; auto.
destruct u1 as [l | | ]; destruct u2 as [l' | | ]; simpl; auto.
rewrite Z.max_assoc; rewrite Zmax_idempotent; auto.
rewrite Zmax_idempotent; auto.
Qed.

Lemma join_comm : forall i i', join i i' = join i' i.
intros [u l] [u' l']; unfold join.
 rewrite cp_min_comm; rewrite cp_max_comm; auto.
Qed.

Lemma join_assoc : forall i i' i'', join (join i i') i'' = join i (join i' i'').
intros [l u][l' u'][l'' u'']; unfold join; rewrite cp_min_assoc; rewrite cp_max_assoc.
auto.
Qed.

Lemma join_involutive : forall i, join i i = i.
intros [l u]; unfold join; rewrite cp_min_refl; rewrite cp_max_refl; auto.
Qed.

Ltac Zmin_max_to_le :=
 match goal with id : cZ (Z.min ?a ?b) = cZ ?a |- _ =>
  assert (Dummy := id); clear id;
  assert (id : a <= b) by
    (injection Dummy; clear Dummy; intros Dummy; rewrite <- Dummy;
     apply Z.le_min_r); clear Dummy
| id : cZ (Z.min ?a ?b) = cZ ?b |- _ =>
  assert (Dummy:= id); clear id;
  assert (id : b <= a) by
    (injection Dummy; clear Dummy; intros Dummy; rewrite <- Dummy;
        apply Z.le_min_l); clear Dummy
| id : cZ (Z.max ?a ?b) = cZ ?a |- _ =>
  assert (Dummy := id); clear id;
  assert (id : b <= a) by
    (injection Dummy; clear Dummy; intros Dummy; rewrite <- Dummy;
     apply Z.le_max_r); clear Dummy
| id : cZ (Z.max ?a ?b) = cZ ?b |- _ =>
  assert (Dummy:= id); clear id;
  assert (id : a <= b) by
    (injection Dummy; clear Dummy; intros Dummy; rewrite <- Dummy;
        apply Z.le_max_l); clear Dummy
 end.

Ltac cp_max_min_diff :=
  match goal with
  | id : cZ ?a <> cp_max (cZ ?a) (cZ ?b) |- _ =>
    assert (Dummy:=id); clear id ;
    assert (id : a <> b) by
      (intros Dummy';case Dummy; rewrite Dummy'; rewrite cp_max_refl; auto);
    clear Dummy
  | id : cZ ?a <> cp_max (cZ ?b) (cZ ?a) |- _ =>
    assert (Dummy:=id); clear id;
    assert (id : a <> b) by
      (intros Dummy';case Dummy; rewrite Dummy'; rewrite cp_max_refl; auto)
  | id : cZ ?a <> cp_min ?a ?b |- _ =>
    assert (Dummy:=id); clear id;
    assert (id : a <> b) by
      (intros Dummy';case Dummy; rewrite Dummy'; rewrite cp_min_refl; auto)
  | id : cZ ?a <> cp_min (cZ ?b) (cZ ?a) |- _ =>
    assert (Dummy:=id); clear id;
    assert (id : a <> b) by
      (intros Dummy';case Dummy; rewrite Dummy'; rewrite cp_min_refl; auto)
  end.

Lemma Zmax_le_compat :
  forall a b c d, a <= b -> c <= d -> Z.max a c <= Z.max b d.
intros; apply Z.max_lub.
apply Z.le_trans with b; auto; apply Z.le_max_l.
apply Z.le_trans with d; auto; apply Z.le_max_r.
Qed.

Lemma Zmin_le_compat :
  forall a b c d, a <= b -> c <= d -> Z.min a c <= Z.min b d.
intros; apply Z.min_glb.
apply Z.le_trans with a; auto; apply Z.le_min_l.
apply Z.le_trans with c; auto; apply Z.le_min_r.
Qed.

Lemma thinner_widen : forall v1 v2, thinner v1 (widen v1 v2).
intros [[l1 | | ][u1 | | ]]
  [[l2 | | ][u2 | | ]]; try (unfold thinner, widen; intuition1; fail);
match goal with |- thinner (?x, ?y) (widen _ (?z, ?t)) =>
  unfold thinner, widen;
  case (ext_eq (cp_min x z) x);case (ext_eq (cp_max y t) y);
  try rewrite cp_max_refl; try rewrite cp_min_refl; try (intuition1; fail)
end.
Qed.

Definition to_p (v:ext_Z*ext_Z)(x:Z) : Prop :=
  match v with
    (minfty,pinfty) => True
  | (minfty,cZ u) => x <= u
  | (cZ l, cZ u) => l <= x <= u
  | (cZ l, pinfty) => l <= x
  | _ => False
  end.

Lemma to_p_thinner : forall l u x, to_p (l,u) x ->
    thinner (l, cZ x) (l, u)/\ thinner (cZ x, u)(l,u).
intros [l | |] [u | |] x ;unfold to_p, thinner; simpl; try(intuition1;fail);
repeat rewrite Zmin_idempotent; repeat rewrite Zmax_idempotent.
intros; rewrite Z.max_comm; rewrite Zle_to_Zmax; try lia;
 rewrite Z.min_comm; rewrite Zle_to_Zmin; auto; lia.
intros; rewrite Z.min_comm; rewrite Zle_to_Zmin; auto.
intros; rewrite Z.max_comm; rewrite Zle_to_Zmax; auto.
Qed.

Lemma plus_correct :
  forall i1 i2 x1 x2, to_p i1 x1 -> to_p i2 x2 -> to_p (plus i1 i2) (x1+x2).
Proof.
intros i1 i2 x1 x2 H1 H2.
destruct i1 as [[l1 | | ][u1 | | ]]; generalize H1; simpl;
 clear H1; intros H1; contradiction || auto;
destruct i2 as [[l2 | | ][u2 | | ]]; generalize H2; simpl;
 intros; contradiction || auto; try lia.
Qed.

Lemma of_int_correct : forall n, to_p (of_int n) n.
intros; simpl; auto with zarith.
Qed.

Lemma to_p_cp_max_min :
   forall l u x, to_p (l,u) x -> cp_max l (cZ x) = cZ x /\
                  cp_min (cZ x) u = cZ x.
intros [l | | ][u | | ]; unfold to_p; simpl; try(intuition1; fail).
intros; rewrite Z.max_comm; rewrite Zle_to_Zmax;try rewrite Zle_to_Zmin;
 intuition1.
intros; rewrite Z.max_comm; rewrite Zle_to_Zmax; intuition1.
intros; rewrite Zle_to_Zmin; intuition1.
Qed.

Lemma cp_max_min_to_p :
  forall l u x, cp_max l (cZ x) = cZ x -> cp_min (cZ x) u = cZ x-> to_p (l,u) x.
intros [l | | ][u | | ]; unfold to_p; simpl; try(intros; auto; discriminate).
intros x H1 H2; injection H1; injection H2; intros H3 H4;split;
 [rewrite <- H4; apply Z.le_max_l | rewrite <- H3; apply Z.le_min_r].
intros x H1 _ ; injection H1; intros H3;rewrite <- H3; apply Z.le_max_l.
intros x _ H1; injection H1; intros H3; rewrite <- H3; apply Z.le_min_r.
Qed.

Lemma thinner_prop :
  forall i1 i2 x, thinner i1 i2 -> to_p i1 x -> to_p i2 x.
intros [l1 u1][l2 u2] x [H1 H2] H3.
destruct (to_p_cp_max_min _ _ _ H3).
apply cp_max_min_to_p.
rewrite cp_max_comm; apply cp_max_trans with l1.
rewrite cp_max_comm; auto.
apply cp_min_r_cp_max_l; auto.
apply cp_min_trans with u1; auto.
apply cp_max_r_cp_min_l; auto.
Qed.

Lemma bot_semantics : forall x, to_p bot x.
simpl; intuition1.
Qed.

Lemma add_test_constraint_right_true_none :
   forall v1 v2, add_test_constraint_right true v1 v2 = None ->
     forall x1 x2, to_p v1 x1 ->
     to_p v2 x2 -> ~x1 < x2.
Proof.
intros [b1 u1] [b2 u2]; unfold add_test_constraint_right.
case (ext_eq b1 (cp_max b1 u2)); intros Heq.
intros _; destruct b1 as [b1 | | ]; destruct u2 as [u2 | | ];
try (assert (H' : u2 <= b1) by(injection Heq;
            intros h; rewrite h; apply Z.le_max_r));
 destruct u1 as [u1 | | ]; simpl in Heq;
 try discriminate heq; simpl; intros e1 e2 g; simpl;
  try(intuition1 ;fail); try discriminate;
destruct b2 as [b2 | | ]; simpl; try(intuition1 ;fail).
intros; discriminate.
Qed.

Lemma add_test_constraint_left_true_none :
   forall v1 v2, add_test_constraint_left true v1 v2 = None ->
     forall x1 x2, to_p v1 x1 -> to_p v2 x2 -> ~x1 < x2.
Proof.
intros [b1 u1] [b2 u2]; unfold add_test_constraint_left.
case (ext_eq b1 (cp_max b1 u2)); intros Heq.
intros _; destruct b1 as [b1 | | ]; destruct u2 as [u2 | | ];
try (assert (H' : u2 <= b1) by(injection Heq;
            intros h; rewrite h; apply Z.le_max_r));
 destruct u1 as [u1 | | ]; simpl in Heq;
 try discriminate heq; simpl; intros e1 e2 g; simpl;
 try(intuition1;fail); try discriminate;
destruct b2 as [b2 | | ]; simpl; try(intuition1;fail).
case (ext_eq u2 (cp_min b1 u2)).
intros Heq' _;destruct b1 as [b1 | | ];destruct u2 as [u2 | | ]; simpl in Heq';
try (assert (H' : u2 <= b1) by(injection Heq';
            intros h; rewrite h; apply Z.le_min_l));
 destruct u1 as [u1 | | ]; simpl in Heq;
 try discriminate heq; simpl; intros e1 e2 g;  simpl;
 try(intuition1;fail); try discriminate;
destruct b2 as [b2 | | ]; simpl; try(intuition1;fail).
intros; discriminate.
Qed.

Lemma add_test_constraint_right_false_none :
  forall v1 v2, add_test_constraint_right false v1 v2 = None ->
     forall x1 x2, to_p v1 x1 -> to_p v2 x2 -> x1 < x2.
Proof.
intros [b1 u1] [b2 u2]; unfold add_test_constraint_right.
case (ext_eq b2 (cp_max u1 b2)); intros Heq;
case (ext_eq u1 (cp_max u1 b2)); intros Heq'; try (intros; discriminate).
intros _; destruct b2 as [b2 | | ]; destruct u1 as [u1 | | ];
try (assert (H' : u1 <= b2) by
 (injection Heq; intros h; rewrite h; apply Z.le_max_l));
try (assert (H'' : ~u1 = b2)
  by (intros h; subst u1; elim Heq'; rewrite cp_max_refl; auto));
  simpl; try (intuition1; fail);
destruct u2 as [u2 | | ];
 try discriminate Heq; simpl; intros e1 e2 g;  simpl;
 try(intuition1;fail); try discriminate;
destruct b1 as [b1 | | ]; simpl; try(intuition1;fail).
Qed.

Lemma add_test_constraint_left_false_none :
   forall v1 v2, add_test_constraint_left false v1 v2 = None ->
     forall x1 x2, to_p v1 x1 -> to_p v2 x2 -> x1 < x2.
Proof.
intros [b1 u1] [b2 u2]; unfold add_test_constraint_left.
case (ext_eq b2 (cp_max u1 b2)); intros Heq;
case (ext_eq u1 (cp_max u1 b2)); intros Heq'; try (intros; discriminate).
intros _; destruct b2 as [b2 | | ]; destruct u1 as [u1 | | ];
try (assert (H' : u1 <= b2) by
 (injection Heq; intros h; rewrite h; apply Z.le_max_l));
try (assert (H'' : ~u1 = b2)
  by (intros h; subst u1; elim Heq'; rewrite cp_max_refl; auto));
  simpl; try (intuition1; fail);
destruct u2 as [u2 | | ];
 try discriminate Heq; simpl; intros e1 e2 g;  simpl;
 try(intuition1;fail); try discriminate;
destruct b1 as [b1 | | ]; simpl; try(intuition1;fail).
Qed.

Lemma add_test_constraint_right_true_sound :
  forall v1 v2 v x1 x2,
     add_test_constraint_right true v1 v2 = Some v ->
     to_p v1 x1 -> to_p v2 x2 -> x1 < x2 -> to_p v x1.
Proof.
intros [b1 u1][b2 u2] v x1 x2; unfold add_test_constraint_right.
case (ext_eq b1 (cp_max b1 u2)); intros Heq; try (intros; discriminate).
intros Hres; injection Hres; intro; subst v.
intros H1 H2 H'; destruct (to_p_cp_max_min _ _ _ H1) as [H3 H4].
destruct (to_p_cp_max_min _ _ _ H2) as [H5 H6].
apply cp_max_min_to_p; auto.
destruct u1 as [u1 | | ]; try (simpl; intuition1;fail);
destruct u2 as [u2 | | ]; try (simpl; intuition1; fail); simpl;
 try (intros; discriminate).
assert (x1 <= u1) by (simpl in H4; injection H4; intros H7; rewrite <- H7;
                      apply Z.le_min_r).
assert (x2 <= u2) by (simpl in H6; injection H6; intros H7; rewrite <- H7;
                      apply Z.le_min_r).
destruct (Zle_or_lt u1 (u2+ -1)).
rewrite (Zle_to_Zmin u1); try lia.
rewrite Zle_to_Zmin; auto.
rewrite (Z.min_comm u1); rewrite (Zle_to_Zmin (u2+ -1)); try lia.
rewrite Zle_to_Zmin; auto; lia.
assert (x2 <= u2) by (simpl in H6; injection H6; intros H7; rewrite <- H7;
                      apply Z.le_min_r).
rewrite Zle_to_Zmin; auto; lia.
Qed.

(* The next proof should be about the same, but is a textually shorter
proof that was designed before (maybe longer in time.) *)

Lemma add_test_constraint_left_true_sound :
  forall v1 v2 v x1 x2,
     add_test_constraint_left true v1 v2 = Some v ->
     to_p v1 x1 -> to_p v2 x2 -> x1 < x2 -> to_p v x2.
Proof.
intros [b1 u1][b2 u2] v x1 x2; unfold add_test_constraint_left.
case (ext_eq u2 (cp_min b1 u2)); intros Heq; try (intros; discriminate).
intros Hres; injection Hres; intro; subst v.
destruct b1 as [b1 | | ]; try (simpl; intuition1;fail);
destruct u1 as [u1 | | ]; try (simpl; intuition1;fail);
destruct b2 as [b2 | | ]; try (simpl; intuition1;fail);
destruct u2 as [u2 | | ]; try (simpl; intuition1; fail); simpl;
 try (assert (b1 <> u2) by
     (intros h;subst u2; elim Heq; rewrite cp_min_refl; auto));
   try (case (Zmax_irreducible_inf (b1+1) b2);(intros; lia));
   try (intros; lia).
Qed.

Lemma add_test_constraint_right_false_sound :
  forall v1 v2 v x1 x2,
     add_test_constraint_right false v1 v2 = Some v ->
     to_p v1 x1 -> to_p v2 x2 -> ~x1 < x2 -> to_p v x1.
Proof.
intros [b1 u1][b2 u2] v x1 x2; unfold add_test_constraint_right.
case (ext_eq b2 (cp_max u1 b2)); intros Heq.
case (ext_eq u1 (cp_max u1 b2)); intros Heq'; try (intros; discriminate);
intros H'; injection H'; intro ; subst v; clear H';
destruct b1 as [b1 | | ]; destruct u1 as [u1 | | ];
 simpl; try (simpl;intuition1;fail);
destruct b2 as [b2 | | ]; destruct u2 as [u2 | | ];
 simpl; try (simpl;intuition1;fail); try (intros;discriminate);
try (case (Zmax_irreducible_inf b1 b2); intros; lia).
intros H'; injection H'; intro; subst v; clear H'.
destruct b1 as [b1 | | ]; destruct u1 as [u1 | | ];
 simpl; try (simpl;intuition1;fail);
destruct b2 as [b2 | | ];
 try (assert (H': b2 <> u1)
        by (intro; elim Heq; subst b2; rewrite cp_max_refl; auto));
destruct u2 as [u2 | | ];
 try case (Zmax_irreducible_inf b1 b2);
 simpl; try (simpl;intuition1;fail); try (intros;discriminate).
Qed.


Lemma add_test_constraint_left_false_sound :
  forall v1 v2 v x1 x2,
     add_test_constraint_left false v1 v2 = Some v ->
     to_p v1 x1 -> to_p v2 x2 -> ~ x1 < x2 -> to_p v x2.
Proof.
intros [b1 u1][b2 u2] v x1 x2; unfold add_test_constraint_left.
case (ext_eq b2 (cp_max u1 b2)); intros Heq.
case (ext_eq u1 (cp_max u1 b2)); intros Heq'; try (intros; discriminate);
intros H'; injection H'; intro ; subst v; clear H';
destruct b1 as [b1 | | ]; destruct u1 as [u1 | | ];
 simpl; try (simpl;intuition1;fail);
destruct b2 as [b2 | | ]; destruct u2 as [u2 | | ];
 simpl; try (simpl;intuition1;fail); try (intros;discriminate);
try (case (Zmin_irreducible u1 u2); lia).
intros H'; injection H'; intro; subst v; clear H'.
destruct b1 as [b1 | | ]; destruct u1 as [u1 | | ];
 simpl; try (simpl;intuition1;fail);
destruct b2 as [b2 | | ];
 try (assert (H': b2 <> u1)
        by (intro; elim Heq; subst b2; rewrite cp_max_refl; auto));
destruct u2 as [u2 | | ];
 try case (Zmin_irreducible_inf u1 u2);
 simpl; try (simpl;intuition1;fail); try (intros;discriminate).
Qed.

Lemma add_test_constraint_right_true_lb :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_right true (l1, u1) (l2, u2) = Some (l, u) ->
    l = l1.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_right;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; intros; subst l; auto;fail).
Qed.

Lemma add_test_constraint_right_false_ub :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_right false (l1, u1) (l2, u2) = Some (l, u) ->
    u = u1.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_right;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq'
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; intros; subst l; auto;fail).
Qed.

Lemma add_test_constraint_right_true_ub_no_cut :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_right true (l1, u1) (l2, u2) = Some (l, u) ->
    cp_min u1 (comp_add u2 (cZ (-1))) = u1 ->
    u = u1.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_right;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; intros; subst u; auto;fail).
Qed.

Lemma add_test_constraint_right_false_lb_no_cut :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_right false (l1, u1) (l2, u2) = Some (l, u) ->
    cp_max l1 l2 = l1 -> l = l1.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_right;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq'
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; intros; subst u; auto;fail);
  try (intros H1 H2; rewrite H2 in H1; injection H1; auto).
Qed.

Lemma add_test_constraint_right_true_ub_cut :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_right true (l1, u1) (l2, u2) = Some (l, u) ->
    u1 <> cp_min u1 (comp_add u2 (cZ (-1))) ->
    u = comp_add u2 (cZ (-1)).
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_right;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; do 2 intro; subst u; clear H');
  try (simpl; intro Hneq;
    destruct (Zmin_irreducible  u1 (u2+ -1)) as [H|H];
    try (rewrite H in Hneq;case Hneq; auto;fail); rewrite H; auto; fail);
  simpl; auto.
Qed.

Lemma add_test_constraint_right_false_lb_cut :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_right false (l1, u1) (l2, u2) = Some (l, u) ->
    l1 <> cp_max l1 l2 -> l = l2.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_right;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq'
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; do 2 intro; subst u; clear H');
  try (simpl; intro Hneq;
    destruct (Zmax_irreducible_inf l1 l2) as [H|H];
    try (rewrite H in Hneq;case Hneq; auto;fail); subst l;
        rewrite H; auto; fail);
  simpl; auto.
Qed.

Lemma not_cp_min_cp_max :
  forall a b, ~cp_min a b = b->cp_max a b = b.
intros [a | | ][b | | ]; simpl; try (intuition1; fail).
destruct (Zle_or_lt a b).
rewrite Z.max_comm; rewrite Zle_to_Zmax; auto.
rewrite Z.min_comm; rewrite Zle_to_Zmin; auto with zarith.
intros Hn; elim Hn; auto.
Qed.

Lemma add_test_constraint_right_true_monotonic :
  forall v1 v2 v1' v2' v v',
    add_test_constraint_right true v1 v2 = Some v ->
    add_test_constraint_right true v1' v2' = Some v' ->
    thinner v1 v1' -> thinner v2 v2' -> thinner v v'.
intros [l1 u1][l2 u2][l1' u1'][l2' u2'][l u][l' u'] H H'.
rewrite add_test_constraint_right_true_lb with (1:=H).
rewrite add_test_constraint_right_true_lb with (1:=H').
destruct (ext_eq u1 (cp_min u1 (comp_add u2 (cZ (-1))))).
rewrite add_test_constraint_right_true_ub_no_cut with (1:=H); auto.
destruct (ext_eq u1' (cp_min u1' (comp_add u2' (cZ (-1))))).
rewrite add_test_constraint_right_true_ub_no_cut with (1:=H'); auto.
rewrite add_test_constraint_right_true_ub_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_max_comm; apply cp_max_trans with (comp_add u2 (cZ (-1))).
destruct u2 as [u2 | | ]; destruct u2' as [u2' | | ]; simpl in *;
  try discriminate; auto.
assert (u2 <= u2') by (injection H4; intros a; rewrite <- a; apply Z.le_max_l).
rewrite Zle_to_Zmax; auto; try lia.
apply cp_min_r_cp_max_l; rewrite cp_min_comm; auto.
rewrite add_test_constraint_right_true_ub_cut with (1:=H); auto.
destruct (ext_eq u1' (cp_min u1' (comp_add u2' (cZ (-1))))).
rewrite add_test_constraint_right_true_ub_no_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_max_comm; apply cp_max_trans with u1.
rewrite cp_max_comm; auto.
rewrite cp_max_comm; apply not_cp_min_cp_max; rewrite cp_min_comm; auto.
rewrite add_test_constraint_right_true_ub_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_max_comm; rewrite cp_max_plus; auto.
rewrite cp_max_comm; auto.
Qed.

Lemma cp_max_irreducible :
  forall a b, cp_max a b = a \/ cp_max a b = b.
intros [a | | ][b | | ];try (intuition1; fail).
simpl; case (Zmax_irreducible_inf a b); intros H; rewrite H; auto.
Qed.

Lemma cp_min_irreducible :
  forall a b, cp_min a b = a \/ cp_min a b = b.
intros [a | | ][b | | ]; try (intuition1;fail).
simpl; case (Zmin_irreducible a b); intros H; rewrite H; auto.
Qed.

Lemma add_test_constraint_right_false_monotonic :
  forall v1 v2 v1' v2' v v',
    add_test_constraint_right false v1 v2 = Some v ->
    add_test_constraint_right false v1' v2' = Some v' ->
    thinner v1 v1' -> thinner v2 v2' -> thinner v v'.
intros [l1 u1][l2 u2][l1' u1'][l2' u2'][l u][l' u'] H H'.
rewrite add_test_constraint_right_false_ub with (1:=H).
rewrite add_test_constraint_right_false_ub with (1:=H').
destruct (ext_eq l1 (cp_max l1 l2)) as [Hl1l2 | Hl1l2].
rewrite add_test_constraint_right_false_lb_no_cut with (1:=H); auto.
destruct (ext_eq l1' (cp_max l1' l2')).
rewrite add_test_constraint_right_false_lb_no_cut with (1:=H'); auto.
rewrite add_test_constraint_right_false_lb_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_min_comm; apply cp_min_trans with l2.
rewrite cp_min_comm; auto.
apply cp_max_r_cp_min_l; rewrite cp_max_comm; auto.
rewrite add_test_constraint_right_false_lb_cut with (1:=H); auto.
destruct (ext_eq l1' (cp_max l1' l2')).
rewrite add_test_constraint_right_false_lb_no_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_min_comm; apply cp_min_trans with l1.
rewrite cp_min_comm; auto.
apply cp_max_r_cp_min_l.
case (cp_max_irreducible l1 l2); auto; intros; case Hl1l2; auto.
rewrite add_test_constraint_right_false_lb_cut with (1:=H'); auto.
intros [H1 H2][H3 H4];split; auto.
Qed.

Lemma add_test_constraint_right_monotonic :
  forall neg v1 v2 v1' v2' v v',
    add_test_constraint_right neg v1 v2 = Some v ->
    add_test_constraint_right neg v1' v2' = Some v' ->
    thinner v1 v1' -> thinner v2 v2' -> thinner v v'.
intros [|].
apply add_test_constraint_right_true_monotonic.
apply add_test_constraint_right_false_monotonic.
Qed.

Lemma add_test_constraint_left_true_ub :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_left true (l1, u1) (l2, u2) = Some (l, u) ->
    u = u2.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_left;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; intros; subst u; auto;fail).
Qed.

Lemma add_test_constraint_left_false_lb :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_left false (l1, u1) (l2, u2) = Some (l, u) ->
    l = l2.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_left;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq'
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; intros; subst l; auto;fail).
Qed.

Lemma add_test_constraint_left_true_lb_no_cut :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_left true (l1, u1) (l2, u2) = Some (l, u) ->
    cp_max (comp_add l1 (cZ 1)) l2 = l2 ->
    l = l2.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_left;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; intros; subst l; auto;fail).
Qed.

Lemma add_test_constraint_left_false_lb_no_cut :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_left false (l1, u1) (l2, u2) = Some (l, u) ->
    cp_min u1 u2 = u2 -> u = u2.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_left;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq'
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; intros; subst u; auto;fail).
Qed.

Lemma add_test_constraint_left_true_lb_cut :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_left true (l1, u1) (l2, u2) = Some (l, u) ->
    l2 <> cp_max (comp_add l1 (cZ 1)) l2 ->
    l = comp_add l1 (cZ 1).
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_left;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; do 2 intro; subst l u; clear H'); simpl; auto;
 (simpl; intro Hneq;
    destruct (Zmax_irreducible_inf  (l1 + 1) l2) as [Hl1l2|Hl1l2];
    try (rewrite Hl1l2 in Hneq;case Hneq; auto;fail); rewrite Hl1l2; auto; fail).
Qed.

Lemma add_test_constraint_left_false_lb_cut :
  forall l1 u1 l2 u2 l u,
    add_test_constraint_left false (l1, u1) (l2, u2) = Some (l, u) ->
    u2 <> cp_min u1 u2 -> u = u1.
intros [l1 | | ] [u1 | | ] [l2 | | ] [u2 | | ] l u;
  unfold add_test_constraint_left;
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq
       end);
  try (match goal with |- context[ext_eq ?a ?b] =>
         case (ext_eq a b); intros Heq'
       end);
  try (simpl; intros; intuition1; discriminate);
  try (intros H'; injection H'; do 2 intro; subst u l; clear H'); simpl; auto;
  (simpl; intro Hneq;
    destruct (Zmin_irreducible u1 u2) as [H|H];
    try (rewrite H in Hneq;case Hneq; auto;fail);
        rewrite H; auto; fail);
  simpl; auto.
Qed.

Lemma add_test_constraint_left_true_monotonic :
  forall v1 v2 v1' v2' v v',
    add_test_constraint_left true v1 v2 = Some v ->
    add_test_constraint_left true v1' v2' = Some v' ->
    thinner v1 v1' -> thinner v2 v2' -> thinner v v'.
intros [l1 u1][l2 u2][l1' u1'][l2' u2'][l u][l' u'] H H'.
rewrite add_test_constraint_left_true_ub with (1:=H).
rewrite add_test_constraint_left_true_ub with (1:=H').
destruct (ext_eq l2 (cp_max (comp_add l1 (cZ 1)) l2)) as [Hl2l1 | Hl2l1].
rewrite add_test_constraint_left_true_lb_no_cut with (1:=H); auto.
destruct (ext_eq l2' (cp_max (comp_add l1' (cZ 1)) l2')).
rewrite add_test_constraint_left_true_lb_no_cut with (1:=H'); auto.
rewrite add_test_constraint_left_true_lb_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_min_comm; apply cp_min_trans with (comp_add l1 (cZ 1)).
destruct l1 as [l1 | | ]; destruct l1' as [l1' | | ]; simpl in *;
  try discriminate; auto.
assert (l1' <= l1) by (injection H1; intros a; rewrite <- a; apply Z.le_min_l).
rewrite Zle_to_Zmin; auto; try lia.
apply cp_max_r_cp_min_l; auto.
rewrite add_test_constraint_left_true_lb_cut with (1:=H); auto.
destruct (ext_eq l2' (cp_max (comp_add l1' (cZ 1)) l2')).
rewrite add_test_constraint_left_true_lb_no_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_min_comm; apply cp_min_trans with l2.
rewrite cp_min_comm; auto.
apply cp_max_r_cp_min_l; rewrite cp_max_comm;
 case (cp_max_irreducible (comp_add l1 (cZ 1)) l2);
 try (intros; case Hl2l1; auto; fail); auto.
rewrite add_test_constraint_left_true_lb_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_min_comm; rewrite cp_min_plus; auto.
rewrite cp_min_comm; auto.
Qed.

Lemma add_test_constraint_left_false_monotonic :
  forall v1 v2 v1' v2' v v',
    add_test_constraint_left false v1 v2 = Some v ->
    add_test_constraint_left false v1' v2' = Some v' ->
    thinner v1 v1' -> thinner v2 v2' -> thinner v v'.
intros [l1 u1][l2 u2][l1' u1'][l2' u2'][l u][l' u'] H H'.
rewrite add_test_constraint_left_false_lb with (1:=H).
rewrite add_test_constraint_left_false_lb with (1:=H').
destruct (ext_eq u2 (cp_min u1 u2)) as [Hl1l2 | Hl1l2].
rewrite add_test_constraint_left_false_lb_no_cut with (1:=H); auto.
destruct (ext_eq u2' (cp_min u1' u2')).
rewrite add_test_constraint_left_false_lb_no_cut with (1:=H'); auto.
rewrite add_test_constraint_left_false_lb_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_max_comm; apply cp_max_trans with u1.
rewrite cp_max_comm; auto.
apply cp_min_r_cp_max_l; auto.
rewrite add_test_constraint_left_false_lb_cut with (1:=H); auto.
destruct (ext_eq u2' (cp_min u1' u2')).
rewrite add_test_constraint_left_false_lb_no_cut with (1:=H'); auto.
intros [H1 H2][H3 H4]; split; auto.
rewrite cp_max_comm; apply cp_max_trans with u2.
rewrite cp_max_comm; auto.
apply cp_min_r_cp_max_l.
rewrite cp_min_comm.
case (cp_min_irreducible u1 u2); auto; intros; case Hl1l2; auto.
rewrite add_test_constraint_left_false_lb_cut with (1:=H'); auto.
intros [H1 H2][H3 H4];split; auto.
Qed.

Lemma add_test_constraint_left_monotonic :
  forall neg v1 v2 v1' v2' v v',
    add_test_constraint_left neg v1 v2 = Some v ->
    add_test_constraint_left neg v1' v2' = Some v' ->
    thinner v1 v1' -> thinner v2 v2' -> thinner v v'.
intros [|].
apply add_test_constraint_left_true_monotonic.
apply add_test_constraint_left_false_monotonic.
Qed.

Lemma add_test_constraint_right_monotonic_none :
  forall neg v1 v2 v1' v2' v,
    add_test_constraint_right neg v1 v2 = Some v ->
    thinner v1 v1' -> thinner v2 v2' ->
    ~add_test_constraint_right neg v1' v2' = None.
unfold add_test_constraint_right;
intros [|] [l1 u1][l2 u2][l1' u1'][l2' u2'] [l u] Hadd [H1 H2][H3 H4].
destruct (ext_eq l1' (cp_max l1' u2')).
destruct (ext_eq l1 (cp_max l1 u2)) as [A | B]; try discriminate.
destruct B; symmetry.
apply cp_max_trans with l1'.
apply cp_min_r_cp_max_l; auto.
apply cp_max_trans with u2'; auto.
rewrite cp_max_comm; auto.
discriminate.
destruct (ext_eq l2' (cp_max u1' l2')) as [C | D]; try discriminate.
destruct (ext_eq u1' (cp_max u1' l2')) as [A | B]; try discriminate.
destruct B; symmetry.
destruct (ext_eq l2 (cp_max u1 l2)) as [A | B]; try discriminate.
destruct (ext_eq u1 (cp_max u1 l2)); try discriminate.
apply cp_max_trans with u1.
rewrite cp_max_comm; auto.
apply cp_max_trans with l2; auto.
apply cp_min_r_cp_max_l; auto.
apply cp_max_trans with u1.
rewrite cp_max_comm; auto.
apply cp_max_trans with l2.
case (cp_max_irreducible u1 l2); auto; intros; case B; auto.
apply cp_min_r_cp_max_l; auto.
Qed.

Lemma add_test_constraint_left_monotonic_none :
  forall neg v1 v2 v1' v2' v,
    add_test_constraint_left neg v1 v2 = Some v ->
    thinner v1 v1' -> thinner v2 v2' ->
    ~add_test_constraint_left neg v1' v2' = None.
unfold add_test_constraint_left;
intros [|] [l1 u1][l2 u2][l1' u1'][l2' u2'] [l u] Hadd [H1 H2][H3 H4].
destruct (ext_eq u2' (cp_min l1' u2')).
destruct (ext_eq u2 (cp_min l1 u2)) as [A | B]; try discriminate.
destruct B; symmetry.
rewrite cp_min_comm; apply cp_min_trans with l1'; auto.
apply cp_min_trans with u2'; auto.
apply cp_max_r_cp_min_l; auto.
rewrite cp_min_comm; auto.
rewrite cp_min_comm; auto.
discriminate.
destruct (ext_eq l2' (cp_max u1' l2')) as [C | D]; try discriminate.
destruct (ext_eq u1' (cp_max u1' l2')) as [A | B]; try discriminate.
destruct B; symmetry.
destruct (ext_eq l2 (cp_max u1 l2)) as [A | B]; try discriminate.
destruct (ext_eq u1 (cp_max u1 l2)); try discriminate.
apply cp_max_trans with u1.
rewrite cp_max_comm; auto.
apply cp_max_trans with l2; auto.
apply cp_min_r_cp_max_l; auto.
apply cp_max_trans with u1.
rewrite cp_max_comm; auto.
apply cp_max_trans with l2.
case (cp_max_irreducible u1 l2); auto; intros; case B; auto.
apply cp_min_r_cp_max_l; auto.
Qed.
