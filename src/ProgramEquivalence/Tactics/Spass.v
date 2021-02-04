(* External import(s). *)
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import         ListNotations.
(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Aux.
Require Import Basics.Map.
Require Import Languages.Spass.Syntax.
Require Import Languages.Spass.Semantics.

Definition path       : Type := list cfg.

Definition baseCaseSet_varsAEqual: cfg -> cfg -> Prop :=
  fun c1 c2 =>
    match (c1, c2) with
    | ([_ | e1], [_ | e2]) => find A e1 = find A e2
    end.

Definition baseCaseSet_envsEqual: cfg -> cfg -> Prop :=
  fun c1 c2 => c1 = c2.

Definition isCompletePath (p: path): Prop := 
  match p with
  | nil         => False
  | _           =>
    match (last p emptyCfg) with
    | [EmptyStack | _] => True
    | _                => False
    end
  end.

Inductive isCompletePath_R: cfg -> cfg -> Prop :=
  | CPR_BaseCase: forall P,
      runStep P = None -> isCompletePath_R P P
  
  | CPR_IndCase : forall P P' P'',
      runStep P = Some P' /\ isCompletePath_R P' P'' ->
        isCompletePath_R P P''.

Definition fullSimulation (P Q: cfg) (baseCaseSet: cfg->cfg->Prop): Prop :=
  forall P', isCompletePath_R P P' -> 
    exists Q', isCompletePath_R Q Q' /\ 
      baseCaseSet P' Q'.

Definition fullEquivalence (P Q:cfg) (baseCaseSet: cfg->cfg->Prop): Prop :=
  fullSimulation P Q baseCaseSet /\ fullSimulation Q P baseCaseSet.

Lemma stepLeft: forall P Q P' baseCaseSet,
  runStep P = Some P' /\ fullSimulation P' Q baseCaseSet  ->
  fullSimulation P Q baseCaseSet.
Proof.
  intros PStart QStart PNext baseCaseSet.
  unfold fullSimulation.
  intros [HStepLeft H] P' H'.
  inversion H'.
  - subst. rewrite HStepLeft in H0.
    inversion H0.
  - subst. destruct H0.
    rewrite HStepLeft in H0.
    injection H0.
    intro HInj.
    rewrite <- HInj in H1.
    specialize (H P').
    specialize (H H1).
    apply H.
Qed.

Lemma stepRight: forall P Q Q' baseCaseSet,
  runStep Q = Some Q' /\ fullSimulation P Q' baseCaseSet ->
  fullSimulation P Q baseCaseSet.
Proof.
  intros PStart QStart QNext baseCaseSet.
  unfold fullSimulation.
  intros [HStepRight H] P' H'.
  specialize (H P').
  apply H in H'.
  destruct H', H0.
  assert (isCompletePath_R QStart x). {
    eapply CPR_IndCase.
    split.
    - apply HStepRight.
    - assumption.
  }
  exists x.
  split; assumption.
Qed.

Lemma stepLeftN (n:nat): forall P Q P' baseCaseSet,
  runNSteps n P = Some P' /\ fullSimulation P' Q baseCaseSet ->
  fullSimulation P Q baseCaseSet.
Proof.
  intros PStart QStart PNext baseCaseSet.
  unfold fullSimulation.
  intros [HStepLeftN H] P' H'.
  inversion H'.
  - subst. 
    unfold runNSteps, ret, bind in HStepLeftN.
    destruct (Nat.eqb n 0) eqn:H_eqb_n_0.
    + Search Nat.eqb.
      apply EqNat.beq_nat_true in H_eqb_n_0.
      rewrite H_eqb_n_0 in HStepLeftN.
      injection HStepLeftN as HInj.
      subst.
      apply H.
      assumption.
    + apply EqNat.beq_nat_false in H_eqb_n_0.
      assert (HAux: exists n', n = S n'). {
        exists (Nat.pred n).
        Search Nat.pred.
        symmetry.
        apply PeanoNat.Nat.succ_pred.
        assumption.
      }
      destruct HAux.
      rewrite H1 in HStepLeftN.
      simpl in HStepLeftN.
      unfold bind in HStepLeftN.
      rewrite H0 in HStepLeftN.
      inversion HStepLeftN.
  - subst. destruct H0.
    generalize dependent PStart.
    generalize dependent QStart.
    generalize dependent PNext.
    generalize dependent P'.
    generalize dependent P'0.
    induction n; intros.
    + unfold runNSteps, ret, bind in HStepLeftN.
      injection HStepLeftN as HInj.
      subst.
      apply H.
      assumption.
    + unfold runNSteps, ret, bind in HStepLeftN.
      rewrite H0 in HStepLeftN.
      inversion H1.
      * subst.
        destruct (Nat.eqb n 0) eqn:H_eqb_n_0.
        -- apply EqNat.beq_nat_true in H_eqb_n_0.
           rewrite H_eqb_n_0 in HStepLeftN.
           injection HStepLeftN as HInj.
           subst.
           apply H.
           assumption.
        -- apply EqNat.beq_nat_false in H_eqb_n_0.
           assert (HAux: exists n', n = S n'). {
            exists (Nat.pred n).
            Search Nat.pred.
            symmetry.
            apply PeanoNat.Nat.succ_pred.
            assumption.
           }
           destruct HAux.
           rewrite H3 in HStepLeftN.
           rewrite H2 in HStepLeftN.
           inversion HStepLeftN.
       * subst.
         destruct H2.
         specialize (IHn P'1).
         specialize (IHn P').
         specialize (IHn H3).
         specialize (IHn PNext).
         specialize (IHn QStart).
         specialize (IHn H).
         specialize (IHn P'0).
         specialize (IHn HStepLeftN).
         specialize (IHn H1).
         specialize (IHn H2).
         apply IHn.
Qed.

Lemma stepRightN (n:nat): forall P Q Q' baseCaseSet,
  runNSteps n Q = Some Q' /\ fullSimulation P Q' baseCaseSet ->
  fullSimulation P Q baseCaseSet.
Proof.
  intros PStart QStart QNext baseCaseSet.
  unfold fullSimulation.
  intros [HStepRightN H] P' H'.
  generalize dependent PStart.
  generalize dependent QStart.
  generalize dependent QNext.
  generalize dependent P'.
  induction n; intros.
  - unfold runNSteps, ret, bind in HStepRightN.
    injection HStepRightN as HInj.
    subst.
    apply H.
    assumption.
  - assert (H'': exists Q' : cfg, isCompletePath_R QNext Q' /\ baseCaseSet P' Q'). {
      apply H.
      apply H'.
    }
    destruct H'', H0.
    unfold runNSteps, bind in HStepRightN.
    destruct (runStep QStart) eqn:H_step_QStart.
    + specialize (IHn P').
      specialize (IHn QNext).
      specialize (IHn c).
      specialize (IHn HStepRightN).
      specialize (IHn PStart).
      specialize (IHn H).
      specialize (IHn H').
      destruct IHn.
      destruct H2.
      exists x0.
      split.
      * eapply CPR_IndCase.
        split.
        -- apply H_step_QStart.
        -- apply H2.
      * apply H3.
    + inversion HStepRightN.
Qed.

Ltac stepLN n :=
  eapply (stepLeftN n); split;
  [reflexivity | unfold find, update, id_eqb];
  simpl.
Ltac stepRN n :=
  eapply (stepRightN n); split;
  [reflexivity | unfold find, update, id_eqb];
  simpl.

Ltac stepLNRM n m :=
  stepLN n; stepRN m.
Ltac stepLRN n :=
  stepLNRM n n.

Ltac stepL :=
  stepLN 1.
Ltac stepR :=
  stepRN 1.
Ltac stepLR :=
  stepLRN 1.

Ltac stepLUntilDone :=
  repeat stepL.
Ltac stepRUntilDone :=
  repeat stepR.
Ltac stepLRUntilDone :=
  stepLUntilDone; stepRUntilDone.

Ltac destLinIneq_native eqName :=
  match goal with
  | [ |- context[Nat.ltb ?x ?y] ] =>
      destruct (Nat.ltb x y) eqn:eqName;
       [(* - *)
        apply PeanoNat.Nat.ltb_lt in eqName;
        try (
         assert (~ x < y) by lia;
         contradiction
        ) |
        (* - *)
        apply PeanoNat.Nat.ltb_ge in eqName;
        try (
          assert (~ y <= x) by lia;
          contradiction
        )]
  | [ |- context[Nat.eqb ?x ?y] ] =>
      destruct (Nat.eqb x y) eqn:eqName;
      [(* - *)
       apply PeanoNat.Nat.eqb_eq in eqName;
       try (
        assert (~ x = y) by lia;
        contradiction
       ) |
       (* - *)
       apply PeanoNat.Nat.eqb_neq in eqName;
       try (
        assert (~ x <> y) by lia;
        contradiction
       )]
  end.

Tactic Notation "destLinIneq" :=
  let H := fresh in destLinIneq_native H.
Tactic Notation "destLinIneq" simple_intropattern(eqName) :=
  destLinIneq_native eqName.

Ltac destAndClearLinIneq_native eqName :=
  destLinIneq eqName; clear eqName.

Tactic Notation "destAndClearLinIneq" :=
  let H := fresh in destAndClearLinIneq_native H.
Tactic Notation "destAndClearLinIneq" simple_intropattern(eqName) :=
  destAndClearLinIneq_native eqName.

Ltac stepLUntilAfterIte :=
  stepLUntilDone;
  repeat destAndClearLinIneq;
  stepL.
Ltac stepRUntilAfterIte :=
  stepRUntilDone;
  repeat destAndClearLinIneq;
  stepR.
Ltac stepLRUntilAfterIte :=
  stepLUntilAfterIte;
  stepRUntilAfterIte.

Ltac fullSim base_case_set :=
  repeat (
    stepLRUntilDone;
    repeat destAndClearLinIneq);
  unfold fullSimulation;
  intros P' H_CPR;
  (exists P'; split;
     [(* - *)
      inversion H_CPR as [| config config' config'' contra];
       [(* + *) 
        apply CPR_BaseCase; compute; reflexivity |
        (* + *)
        destruct contra as [contra]; inversion contra
       ] |
      (* - *)
      unfold base_case_set;
      inversion H_CPR as [| config config' config'' contra];
       [(* + *)
        unfold find; simpl; try (congruence || reflexivity) |
        (* + *)
        destruct contra as [contra]; inversion contra
       ]
     ]
  ) ||
  (eexists; split; simpl;
    [(* - *)
     inversion H_CPR as [| config config' config'' contra];
      [(* + *) 
       apply CPR_BaseCase; compute; reflexivity |
       (* + *)
       destruct contra as [contra]; inversion contra
      ] |
     (* - *)
     unfold base_case_set;
     inversion H_CPR as [| config config' config'' contra];
      [(* + *)
       unfold find; simpl; try (congruence || reflexivity) |
       (* + *)
       destruct contra as [contra]; inversion contra
      ]
    ]
  ).
