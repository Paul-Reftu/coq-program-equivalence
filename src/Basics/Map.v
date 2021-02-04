(* External import(s). *)
Require Import Coq.Init.Nat.
Require Import Coq.Logic.FunctionalExtensionality.
(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Aux.

Definition NAT_MIN: nat := 0.

Definition map (X:Type) := identifier -> X.
Definition empty_map {X:Type} (d:X): map X :=
  (fun _ => d).
Definition map_id_nat := map nat.
Definition map_id_nat_empty := empty_map NAT_MIN.
Definition update {X:Type} (k:identifier) (v:X) (m:map X): map X :=
  fun k' => if id_eqb k k' then v else m k'.

Definition find {X:Type} (k:identifier) (m:map X): X :=
  m k.

Definition A := Identifier 0.
Definition B := Identifier 1.
Definition C := Identifier 2.
Definition D := Identifier 3.

Notation "k '|->' v 'IN' m" := (update k v m) (at level 60, right associativity).

Lemma map_update_shadow: forall (X:Type) (m:map X) k v v',
  (k |-> v IN k |-> v' IN m) = (k |-> v IN m).
Proof.
  intros. unfold update.
  apply functional_extensionality.
  intro k'. destruct (id_eqb k k'); reflexivity.
Qed.

Lemma map_find_shadow: forall (X:Type) (m:map X) k k' v',
  k <> k' -> find k m = find k (k' |-> v' IN m).
Proof.
  intros. unfold find. unfold update.
  destruct (id_eqb k' k) eqn:Heq.
  - apply id_eqb_refl_converse in H.
    rewrite id_eqb_sym in H.
    rewrite H in Heq.
    discriminate Heq.
  - reflexivity.
Qed.
