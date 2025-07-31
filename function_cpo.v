From Stdlib Require Export Relations Classical ClassicalEpsilon Zwf.
From Stdlib Require Export Compare_dec.
From Stdlib Require Export List ZArith.

(* SECTION: Proving Tarski's fixpoint theorem. *)

Arguments antisymmetric : default implicits.
Arguments transitive : default implicits.
Arguments reflexive : default implicits.

Section cpos.
Variables (A:Type)(R:A->A->Prop).

Definition upper_bound (x:A)(f:nat -> A) :=
  forall n, R (f n) x.

Definition lub (x:A)(f:nat -> A) :=
  upper_bound x f /\ forall y, upper_bound y f -> R x y.

Lemma least_unique :
  antisymmetric R ->
  forall (P : A -> Prop)(x y: A),
  P x /\ (forall z, P z -> R x z) ->
  P y /\ (forall z, P z -> R y z) -> x = y.
Proof.
intuition.
Qed.

Lemma unique_lub :
  forall (f:nat->A)(x y: A),
     antisymmetric R ->
     lub x f -> lub y f -> x = y.
Proof.
intros f x y Ha Hx Hy.
apply least_unique with (fun x => upper_bound x f); auto.
Qed.

Definition chain (f:nat->A) := forall n, R (f n)(f (S n)).

Lemma chain_le :
  transitive R -> reflexive R ->
  forall f x y, chain f -> x <= y -> R (f x) (f y).
intros Ht Hr f x y Hc H; induction H; eauto.
Qed.

Definition complete :=
  forall f:nat->A, chain f -> exists x: A, lub x f.

End cpos.
Arguments upper_bound : default implicits.
Arguments lub : default implicits.
Arguments chain : default implicits.
Arguments complete : default implicits.

Section continuity.

Variables (A B:Type)(R :A->A->Prop)(R' :B->B->Prop).

Definition monotonic (f:A -> B) :=
    forall x y, R x y -> R' (f x) (f y).

Definition continuous (f:A -> B) :=
  forall (c: nat -> A),  chain R c ->
    forall (l:A), lub R l c ->
    lub R' (f l) (fun n => f (c n)).

Lemma continuous_imp_monotonic :
  forall f, reflexive R -> continuous f -> monotonic f.
Proof.
intros f Hr Hc x y Hxy.
assert (Hl : lub R' (f y) (fun n => f (match n with 0 => x | _ => y end))).
apply (Hc (fun n => match n with 0 => x | _ => y end)).
unfold chain; destruct n; auto.
split.
unfold upper_bound; destruct n; auto.
intros b H; exact (H 1).
destruct Hl as [Hu Hl']; exact (Hu 0).
Qed.

(* This theorem is not really used, but I keep it as a way to
   show that my definition of being continuous is close to the
   conventional one. *)

Lemma continuous_reverse :
  forall (f:A->B)(c :nat->A),
  antisymmetric R' -> chain R c ->
  continuous f ->
  forall (l:A), lub R l c ->
  forall (l':B), lub R' l' (fun n => f (c n)) ->
   l' = f l.
intros f c Ha Hch Hct l Hlub l' Hlub'.
assert (Hlub2 : lub R' (f l)(fun n => f (c n))).
exact (Hct c Hch l Hlub).
apply (unique_lub B R' (fun n => f (c n))); assumption.
Qed.

End continuity.
Arguments monotonic : default implicits.
Arguments continuous : default implicits.

Section Tarski_theory.

Variables (A:Type)(R:A->A->Prop)(bot : A)(f:A->A).

Hypotheses (Hr : reflexive R)(Ha : antisymmetric R)
   (Ht : transitive R) (Hc : complete R)
   (Hb : forall x, R bot x)(Hct : continuous R R f).

Definition least_fixpoint (f:A->A)(x:A):Prop :=
  x = f x /\ (forall y, y = f y -> R x y).

Fixpoint iter (k:nat)(x:A) : A :=
  match k with 0 => x | S p => f (iter p x) end.

Lemma f_monotonic : monotonic R R f.
apply continuous_imp_monotonic; auto.
Qed.

Lemma Hchain_iter_f_bot : chain R (fun n => iter n bot).
unfold chain. induction n.
simpl. apply Hb.
apply (f_monotonic (iter n bot) (iter (S n) bot)). assumption.
Qed.

Lemma phi_ub_iter_add_f :
   forall phi : A,
       upper_bound R phi (fun n => iter n bot) ->
       upper_bound R phi (fun n => f (iter n bot)).
intros phi Hup p; apply (Hup (S p)).
Qed.

Lemma f_phi_upper_bound :
   forall phi : A,
       upper_bound R phi (fun n => iter n bot) ->
       upper_bound R (f phi) (fun n => iter n bot).
intros phi Hup [ | p].
apply Hb.
apply (f_monotonic (iter p bot)); apply (Hup p).
Qed.

Lemma lub_iterates_fixpoint :
   forall phi : A, lub R phi (fun n => iter n bot) -> phi = f phi.
intros phi [Hub Hl]; apply Ha.
apply Hl; apply f_phi_upper_bound; assumption.
assert (Hfphi : lub R (f phi) (fun n => f (iter n bot))).
apply (Hct (fun n => iter n bot) Hchain_iter_f_bot phi);split;assumption.
destruct Hfphi as [Hub' Hl'].
apply Hl'; apply phi_ub_iter_add_f; assumption.
Qed.

Lemma phi_less_than_fixpoint :
  forall phi : A, lub R phi (fun n => iter n bot) ->
  forall psi : A, psi = f psi -> R phi psi.
intros phi [Hup Hl] psi Hfxp; apply Hl.
intros n; induction n.
simpl; auto.
simpl; rewrite Hfxp; apply f_monotonic; assumption.
Qed.

Theorem Tarski_least_fixpoint : exists phi: A, least_fixpoint f phi.
destruct (Hc (fun n => iter n bot) Hchain_iter_f_bot) as [phi Hlub].
exists phi.
split.
apply lub_iterates_fixpoint; auto.
apply phi_less_than_fixpoint; auto.
Qed.

Theorem least_fixpoint_lub_iterates :
  forall phi, least_fixpoint f phi -> lub R phi (fun n => iter n bot).
intros phi Hlfp.
destruct (Hc (fun n => iter n bot) Hchain_iter_f_bot) as [psi Hlub'].
replace phi with psi.
trivial.
symmetry.
apply least_unique with (1:= Ha) (P:= fun x => x = f x) (2:= Hlfp).
split.
apply lub_iterates_fixpoint; auto.
apply phi_less_than_fixpoint; auto.
Qed.

End Tarski_theory.
Arguments least_fixpoint : default implicits.

(* SECTION: basic properties of the basic discrete order. *)

Section opt_cpo.
Variable A: Type.

Inductive option_cpo : option A -> option A -> Prop :=
  option_cpo_none_bot : forall x: option A, option_cpo None x
| option_cpo_refl : forall x: option A, option_cpo x x.

Lemma reflexive_option_cpo : reflexive option_cpo.
Proof option_cpo_refl.

Hint Resolve option_cpo_refl option_cpo_none_bot reflexive_option_cpo : core.

Lemma antisym_option_cpo : antisymmetric option_cpo.
intros x y H; inversion H.
intros H'; inversion H'; trivial.
trivial.
Qed.

Lemma transitive_option_cpo_aux :
  forall (x y: option A),
   option_cpo x y -> forall z, option_cpo y z -> option_cpo x z.
intros x y H; inversion H; auto.
Qed.

Lemma transitive_option_cpo :  transitive option_cpo.
intros x y z H1 H2 ; apply transitive_option_cpo_aux with y ; assumption.
Qed.

Hint Resolve transitive_option_cpo : core.

Lemma chain_none_pred :
  forall f n p, chain option_cpo f ->
  p <= n -> f n = None -> f p = None.
intros f n p Hch Hpn. elim Hpn. auto.
intros m Hpm Hfmfp Hfsm. apply Hfmfp.
assert (Hcpo : option_cpo (f m) (f (S m))) by apply Hch.
inversion Hcpo; auto; rewrite <- Hfsm; auto.
Qed.


Theorem value_upper_bound :
  forall f x, chain option_cpo f -> f x <> None ->
  upper_bound option_cpo (f x) f.
intros f x Hchain Hneq y.
case (le_gt_dec x y); [intros Hlexy | intros Hltyx].
assert (Hcpo: option_cpo (f x) (f y)) by (apply chain_le; auto).
inversion Hcpo; [elim Hneq; auto | auto].
apply chain_le; auto with arith.
Qed.

Hint Resolve value_upper_bound : core.
Theorem complete_option_cpo : complete option_cpo.
intros f Hchain.
elim (classic (forall n, f n = None)).
intros Hn; exists (None (A:=A)).
split; intros p; try rewrite Hn; auto.
intros Hnotforall.
elim not_all_ex_not with
   (P:= fun x => f x = None) (1:= Hnotforall).
intros n Hneq; exists (f n); split; [auto | intros y; auto].
Qed.
End opt_cpo.
Global Hint Resolve option_cpo_refl option_cpo_none_bot reflexive_option_cpo : core.
Arguments option_cpo : default implicits.

(* SECTION: providing usable mathematical tools for a classical setting. *)

Axiom extensionality :
  forall A : Type, forall B : A -> Type,
    forall f g: forall x:A, B x,
      (forall x, f x = g x) -> f = g.

(* SECTION: lifting an order to the function space. *)
Section pointwise_update_function.
Variables (A B:Type)(f:A->B)(x:A)(v:B).

Definition p_v  (y:A) :=
     epsilon (inhabits v) (fun w => (y=x-> w =v)/\(y<>x->w=f y)).

Lemma pointwise_variant_eq : p_v x = v.
unfold p_v; elim (epsilon_spec (inhabits v)(fun w => (x=x->w=v)/\(x<>x->w=f x))).
auto.
exists v;split;[auto|intros Habs;case Habs;trivial].
Qed.

Lemma pointwise_variant_diff : forall y, y<> x -> p_v y = f y.
intros y Hn; unfold p_v;
 elim (epsilon_spec(inhabits v)(fun w =>(y=x->w=v)/\(y<>x->w=f y))).
intuition.
exists (f y);split;[intros Habs; elim Hn;auto|auto].
Qed.

End pointwise_update_function.

Arguments p_v : default implicits.
Arguments pointwise_variant_eq : default implicits.
Arguments pointwise_variant_diff : default implicits.

Section lift.

Variables (A B:Type)(R:B->B->Prop).
Hypothesis Hr : reflexive R.
Hypothesis Ha : antisymmetric R.
Hypothesis Ht : transitive R.
Hypothesis Hc : complete R.

Definition lift_order :=
   fun (f g:A->B)=> forall x, R (f x)(g x).

Lemma reflexive_lift : reflexive lift_order.
intros f x; apply Hr.
Qed.

Lemma antisymmetric_lift : antisymmetric lift_order.
intros f g HfRg HgRf.
apply extensionality with (B:= fun x:A => B).
intros x; apply (Ha (f x) (g x)); apply (HfRg x) || apply (HgRf x).
Qed.

Lemma transitive_lift : transitive lift_order.
intros f g h Hfg Hgh x; apply Ht with (g x).
apply (Hfg x).
apply (Hgh x).
Qed.

Lemma lift_lub : forall (f:A->B)(c:nat->A->B),
   (forall x, lub R (f x)(fun n=> c n x))-> lub lift_order f c.
Proof.
intros f c Hx; split.
intros n x; destruct (Hx x) as [Hu Hl]; apply Hu.
intros g Hug x; destruct (Hx x) as [_ Hl]; apply Hl.
intros n; apply (Hug n x).
Qed.

Lemma chain_lift_reverse :
  forall c, chain lift_order c -> forall x, chain R (fun n => c n x).
intros c Hch x n; apply (Hch n x).
Qed.

Lemma lift_complete : complete lift_order.
Proof.
intros c Hchain.
exists (fun x => epsilon(inhabits (c 0 x))(fun v => lub R v (fun n => c n x))).
apply lift_lub.
intros x; apply epsilon_spec.
apply Hc; apply chain_lift_reverse; assumption.
Qed.

Lemma lub_lift_reverse :
  forall (c:nat->A->B)(l:A->B),
  lub lift_order l c -> forall x, lub R (l x)(fun n => c n x).
Proof.
intros c l [Hub Hl] x.
split.
intros n; apply (Hub n x).
intros b' Hup'.
assert (Hupg' : upper_bound lift_order (p_v l x b') c).
intros n y; case (classic (y=x)).
intros Hyx; subst y; rewrite pointwise_variant_eq; apply Hup'.
intros Hn; rewrite pointwise_variant_diff; auto; apply Hub.
rewrite <- (pointwise_variant_eq l x b'); apply Hl; assumption.
Qed.

End lift.

Definition f_order (A B:Type) :=
  lift_order A (option B)(@option_cpo B).

Theorem reflexive_f_order : forall A B, reflexive (f_order A B).
intros A B f x; auto.
Qed.

Theorem antisymmetric_f_order : forall A B, antisymmetric (f_order A B).
intros; unfold f_order; apply antisymmetric_lift; apply antisym_option_cpo.
Qed.

Theorem transitive_f_order : forall A B, transitive (f_order A B).
intros; unfold f_order; apply transitive_lift; apply transitive_option_cpo.
Qed.

Theorem complete_f_order : forall A B, complete (f_order A B).
intros; unfold f_order; apply lift_complete; apply complete_option_cpo.
Qed.

(* The specific form of the Tarski least fixpoint theorem when used
  solely to define recursive functions. *)
Definition Tarski_fix
   (A B:Type) (f:(A->option B)->A->option B) : A->option B :=
  (epsilon (inhabits (fun x => None))
              (fun phi => least_fixpoint (f_order A B) f phi)).

Arguments Tarski_fix [A B].

Theorem Tarski_fix_prop :
    forall (A B:Type) (f : (A -> option B)->A -> option B),
      continuous (f_order A B)(f_order A B) f ->
      least_fixpoint (f_order A B) f (Tarski_fix f).
Proof.
intros A B f Hct; unfold Tarski_fix.
apply epsilon_spec.
assert (Ht := Tarski_least_fixpoint).
apply Tarski_least_fixpoint with (R:=f_order A B)
        (bot:=fun x:A=>@None B)
        (4:= (fun (g:A->option B) x => @option_cpo_none_bot B (g x))).
apply reflexive_f_order.
apply antisymmetric_f_order.
apply complete_f_order.
exact Hct.
Qed.

(* Properties of chains. *)

Theorem continuous_chain :
  forall (A B:Type)(R:A->A->Prop)
     R' (f:A->B), reflexive R -> continuous R R' f ->
    forall c, chain R c -> chain R' (fun x => f (c x)).
intros A B R R' f Hr Hct c Hch n;
    apply (continuous_imp_monotonic _ _ R _ _ Hr Hct (c n) (c (S n))).
auto.
Qed.

Theorem lub_some_witness1 :
   forall (A:Type) (c:nat -> option A)(v:A),
   lub (@option_cpo A) (Some v) c ->
   (exists n:nat, c n = Some v).
intros A c v [Hup Hl].
elim (classic (forall n, c n = None)).
intros Hnone.
assert (Hnone_aux : option_cpo (Some v) None).
apply Hl.
intros n.
rewrite Hnone; auto.
inversion Hnone_aux.
intros Hnot_all.
assert (Hex_not : exists n, c n <> None).
apply not_all_ex_not with (U:=nat)
  (P:= fun n => c n = None)(1:= Hnot_all).
destruct Hex_not as [n Hneq].
assert (Hopt: option_cpo (c n) (Some v)).
apply (Hup n).
exists n.
inversion Hopt; auto.
elim Hneq; auto.
Qed.

Theorem lub_some_witness :
   forall (A B:Type) c (a:A)(b:B)(f:A->option B), f a = Some b ->
   lub (lift_order A (option B) (option_cpo (A:=B))) f c  ->
   (exists n:nat, c n a = Some b).
intros A B c a b f Heq Hlub.
apply (lub_some_witness1 B (fun n => c n a) b).
assert (Hlub':= lub_lift_reverse A _ (@option_cpo B) c f Hlub a).
rewrite <- Heq; assumption.
Qed.

Theorem Tarski_fix_iterates_witness :
    forall (A B:Type) (f : (A -> option B)->A -> option B),
      continuous (f_order A B)(f_order A B) f->
      forall (x:A)(v:B), Tarski_fix f x = Some v ->
    exists n, iter (A->option B) f n (fun a => None) x = Some v.
intros A B f Hct x.
assert (H:lub (f_order A B) (Tarski_fix f)
              (fun n => iter _ f n (fun a=>None))).
apply least_fixpoint_lub_iterates.
apply reflexive_f_order.
apply antisymmetric_f_order.
apply complete_f_order.
intros g y; apply option_cpo_none_bot.
assumption.
apply Tarski_fix_prop.
assumption.
intros v Heq.
apply lub_some_witness with (A:=A)(B:=B)(1:= Heq)(2:=H).
Qed.

Theorem iterates_none_imp_fix_none :
  forall A B f,  continuous (f_order A B)(f_order A B) f-> forall x,
  (forall n, iter _ f n (fun z => None) x = None) ->
  Tarski_fix f x = None.
intros A B f Hct x Happr.
case_eq (Tarski_fix f x).
intros v Heq;
destruct (Tarski_fix_iterates_witness A B f Hct x v Heq) as
  [n Heq'].
rewrite (Happr n) in Heq'; discriminate.
trivial.
Qed.

(* SECTION: An order for functions that stay in the same type. *)

Definition f_order' (A:Type) :=  f_order A A.

Theorem reflexive_f_order' : forall A, reflexive (f_order' A).
intros; unfold f_order'; apply reflexive_f_order.
Qed.

Theorem antisymmetric_f_order' : forall A, antisymmetric (f_order' A).
intros; unfold f_order'; apply antisymmetric_f_order.
Qed.

Theorem transitive_f_order' : forall A, transitive (f_order' A).
intros; unfold f_order'; apply transitive_f_order.
Qed.

Theorem complete_f_order' : forall A, complete (f_order' A).
intros; unfold f_order'; apply complete_f_order.
Qed.

Global Hint Resolve reflexive_f_order' antisymmetric_f_order' transitive_f_order'
  complete_f_order' : core.
