From Stdlib Require Import ZArith List.

Set Implicit Arguments.
Section types.
Variable string : Type.
Variable string_dec : forall a b:string, {a=b}+{a<>b}.

Inductive aexpr0 : Type := avar (s : string) | anum (n :Z) | aplus (a1 a2:aexpr0).

Inductive bexpr0 : Type :=  blt (_ _ : aexpr0).

Inductive instr0 : Type :=
  assign (_ : string) (_ : aexpr0) | sequence (_ _: instr0)
 | while (_ :bexpr0)(_ : instr0) | skip.

Inductive assert0 : Type :=
  a_b(b: bexpr0) | a_not(a: assert0) | a_conj(a a': assert0)
| pred(s: string)(l: list aexpr0).

Inductive condition0 : Type :=
| c_imp : assert0 -> assert0 -> condition0.

Inductive a_instr0 : Type :=
  prec(a:assert0)(i:a_instr0) | a_skip
| a_assign(x:string)(e:aexpr0) | a_sequence(i1 i2:a_instr0)
| a_while(b:bexpr0)(a:assert0)(i:a_instr0).

Fixpoint lookup (A:Type)(l:list(string*A))(def:A)(x:string): A :=
  match l with nil => def
  | (y,a)::tl => if string_dec y x then a else lookup tl def x
  end.

End types.
Arguments anum [string].
Arguments skip {string}.
Arguments a_skip {string}.

Module Type little_syntax.
Parameter string : Set.

Parameter string_dec : forall a b:string, {a=b}+{a<>b}.
Parameter false_cst : string.
Parameter true_cst : string.
Parameter between_cst : string.
Parameter ge_cst : string.
Parameter le_cst : string.
Parameter lt : string -> string -> Prop.

Axiom lt_irrefl : forall x, ~lt x  x.
Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

Axiom all_distinct :
  lt between_cst false_cst /\ lt false_cst ge_cst /\
  lt ge_cst le_cst /\ lt le_cst true_cst.

Definition aexpr := aexpr0 string.
Definition bexpr := bexpr0 string.
Definition instr := instr0 string.
Definition assert := assert0 string.
Definition condition := condition0 string.
Definition a_instr := a_instr0 string.

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

End little_syntax.
