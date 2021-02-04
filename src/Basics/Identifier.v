(* External import(s). *)
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Inductive identifier: Type :=
  Identifier (i:nat).

Definition id_eqb (i i':identifier): bool :=
  match (i, i') with
  | (Identifier x, Identifier x') => beq_nat x x'
  end.

Lemma id_eqb_refl: forall i i',
  id_eqb i i' = true <-> i = i'.
Proof.
  intros. destruct i, i'; unfold id_eqb; split; intro.
  - apply PeanoNat.Nat.eqb_eq in H.
    congruence.
  - apply PeanoNat.Nat.eqb_eq.
    congruence.
Qed.

Lemma id_eqb_refl_converse: forall i i',
  id_eqb i i' = false <-> i <> i'.
Proof.
  intros. destruct i, i'; unfold id_eqb; split; intro.
  - apply PeanoNat.Nat.eqb_neq in H.
    congruence.
  - apply PeanoNat.Nat.eqb_neq.
    congruence.
Qed.

Lemma id_eqb_sym: forall i i',
  id_eqb i i' = id_eqb i' i.
Proof.
  intros. destruct i, i'; unfold id_eqb.
  apply PeanoNat.Nat.eqb_sym.
Qed.

Lemma id_eqb_equiv_eq: forall i i',
  id_eqb i i' = true <-> i = i'.
Proof.
  intros. destruct i, i'; unfold id_eqb; split; intro.
  - apply PeanoNat.Nat.eqb_eq in H.
    congruence.
  - apply PeanoNat.Nat.eqb_eq.
    congruence.
Qed.
