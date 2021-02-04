(* External import(s). *)
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import         ListNotations.
(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Aux.
Require Import Basics.Map.
Require Import Languages.Spass.Syntax.
Require Import Languages.Spass.Semantics.
Require Import Programs.Spass.
Require Import ProgramEquivalence.Tactics.Spass.

Fixpoint reduceAux (i n fuel:nat): stack :=
  match fuel with
  | O       =>
    match (Nat.compare i n) with
    | Gt => EmptyStack
    | _  => n + EHole ~> EmptyStack
    end
  | S fuel' => i + EHole ~> reduceAux (S i) n fuel'
  end.

Definition reduce (i n:nat): stack :=
  reduceAux i n (Nat.sub n i).

Lemma lambdaSum0ToN_sim_tailRecLambdaSum0ToN_G3: forall (n i a:nat) e,
  1 <= i /\ i <= n ->
    fullSimulation
      ([a ~> reduce i n | e])
      ([ITE (negb (Nat.ltb i n) && negb (Nat.eqb i n)) THEN
          a
        ELSE
          EApp(EApp(EApp(EFix D(
            EAbs A (EAbs B (EAbs C(
              ITE !(B <? A) & !(B ==? A) THEN
                C
              ELSE
                EApp(EApp(EApp D A) (B + 1)) (C + B) 
              ETI
           ))))) n) (i + 1)) (a + i)
        ETI
        ~> EmptyStack | e])
      baseCaseSet_envsEqual.
Proof.
  intros n i a e [H_1_le_i H_i_le_n].
  remember (Nat.sub n i)
    as   sub_n_i
    eqn: Heq_sub_n_i.
  generalize dependent n;
    generalize dependent i;
    generalize dependent a;
    generalize dependent e;
    generalize dependent sub_n_i.
  induction sub_n_i as [| sub_n_i IH_sub_n_i];
    intros; unfold reduce, reduceAux.
  - assert (H_n_eq_i: n=i) by lia.
    rewrite <- H_n_eq_i,
            PeanoNat.Nat.sub_diag,
            PeanoNat.Nat.compare_refl.
    fullSim baseCaseSet_envsEqual.
    rewrite PeanoNat.Nat.add_comm; reflexivity.
  - assert (H_i_lt_n: i<n) by lia.
    assert (Heq_sub_n_i': sub_n_i = (n - S i)%nat) by lia.
    rewrite <- Heq_sub_n_i,
            Heq_sub_n_i'.
    repeat destAndClearLinIneq H_ineq.
    stepLRUntilDone.
    rewrite PeanoNat.Nat.add_1_r, PeanoNat.Nat.add_comm.
    apply IH_sub_n_i; lia.
Qed.

Lemma lambdaSum0ToN_sim_tailRecLambdaSum0ToN_G2: forall n i,
  i <= (n-1)%nat /\ n>=1 ->
    fullSimulation
      ([EApp (EFix D (
         EAbs A (
           ITE A ==? 0 THEN 
             0
           ELSE
             A + (EApp D (A - 1))
           ETI)
         )) i
        ~> reduce (i+1)%nat n | getEnvOfCfg (prog_tailRecLambdaSum0ToN n 0 0)])
      (prog_tailRecLambdaSum0ToN n 0 0)
      baseCaseSet_envsEqual.
Proof.
  intros n i [H_i_le_predN H_n_ge_1].
  generalize dependent i.
  induction i as [| i IH_i]; intros.
  - stepLRUntilDone.
    repeat destAndClearLinIneq.
    stepLRUntilDone.
    apply lambdaSum0ToN_sim_tailRecLambdaSum0ToN_G3; lia.
  - stepLN 9.
    assert (H_reduce: ((S i + EHole) ~> reduce (S (i+1)) n)=reduce (i+1)%nat n). {
      unfold reduce, reduceAux.
      assert ((n-(i+1))%nat=S (n - S (S i))%nat) by lia.
      rewrite H,
              PeanoNat.Nat.add_1_r; 
      reflexivity.
    }
    rewrite H_reduce,
            PeanoNat.Nat.sub_0_r.
    apply IH_i; lia.
Qed.

Lemma lambdaSum0ToN_sim_tailRecLambdaSum0ToN_G1: forall n,
  fullSimulation (prog_lambdaSum0ToN n) (prog_tailRecLambdaSum0ToN n 0 0) baseCaseSet_envsEqual.
Proof.
  induction n as [| n' IH_n] eqn:H_n.
  - fullSim baseCaseSet_envsEqual.
  - stepLN 6.
    assert (H_reduce: (S n' + EHole ~> EmptyStack)=reduce (S n') (S n')). {
      unfold reduce, reduceAux.
      rewrite PeanoNat.Nat.sub_diag,
              PeanoNat.Nat.compare_refl;
      reflexivity.
    }
    rewrite H_reduce.
    stepLN 3.
    assert (H_Sn'_eq_n'Plus1: S n'=(n'+1)%nat) by lia.
    rewrite PeanoNat.Nat.sub_0_r,
            H_Sn'_eq_n'Plus1.
    apply lambdaSum0ToN_sim_tailRecLambdaSum0ToN_G2; repeat split; lia.
Qed.
