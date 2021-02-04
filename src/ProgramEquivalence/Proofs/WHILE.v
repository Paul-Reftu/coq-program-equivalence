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
Require Import Languages.WHILE.Syntax.
Require Import Languages.WHILE.Semantics.
Require Import Programs.WHILE.Other.
Require Import Programs.WHILE.CodeHoisting.
Require Import Programs.WHILE.LICM.
Require Import Programs.WHILE.LoopPeeling.
Require Import Programs.WHILE.SoftwarePipelining.
Require Import ProgramEquivalence.Tactics.WHILE.

Compute runNSteps 97 prog_incr0To5.
Compute runNSteps 115 prog_decr10To5.

Theorem incr0To5_parSim_decr10To5: 
  forall (config config'             : cfg)
         (P Q                        : path)
         (lastOfP lastOfQ            : cfg),
  (  Some config      = runNSteps 97  prog_incr0To5
  /\ Some config'     = runNSteps 115 prog_decr10To5
  /\ P                = cons config nil
  /\ Q                = cons config' nil
  /\ lastOfP          = last P emptyCfg
  /\ lastOfQ          = last Q emptyCfg
  /\ isCompletePath P)
    -> isCompletePath Q /\ baseCaseSet_varsAEqual lastOfP lastOfQ.
Proof.
  intros c c' P Q lastOfP lastOfQ
    [H_someConfig_eq_runIncr0To5   [
     H_someConfig'_eq_runDecr10To5 [
     H_P_eq_listOfConfig           [
     H_Q_eq_listOfConfig'          [
     H_lastOfP_eq_lastP            [
     H_lastOfQ_eq_lastQ H_CP_P
    ]]]]]]; split.
  - rewrite H_Q_eq_listOfConfig'.
    compute.
    compute in H_someConfig'_eq_runDecr10To5.
    injection H_someConfig'_eq_runDecr10To5 as H_inj.
    rewrite H_inj; trivial.
  - rewrite H_lastOfP_eq_lastP,
            H_lastOfQ_eq_lastQ,
            H_P_eq_listOfConfig,
            H_Q_eq_listOfConfig'.
    compute.
    compute in H_someConfig_eq_runIncr0To5,
               H_someConfig'_eq_runDecr10To5.
    injection H_someConfig_eq_runIncr0To5   as H_Inj.
    injection H_someConfig'_eq_runDecr10To5 as H_Inj'.
    rewrite H_Inj, H_Inj'.
    reflexivity.
Qed.

Lemma sum1ToPredN_sim_sum0ToPredN_G2:
  (forall n i e e',
    n >= 2 /\ 1 <= i /\ i <= (n-1)%nat
    /\ e A = e' A
    /\ e B = i /\ e' B = i
    /\ e C = n   /\ e' C = n ->
      fullSimulation
         ([(A ::= A + B; B ::= B + 1);
           WHILE (B <? C) DO 
              A ::= A + B; B ::= B + 1 
           END
           ~> EmptyStack | e])
           
         ([(A ::= A + B; B ::= B + 1);
           WHILE (B <? C) DO
              A ::= A + B; B ::= B + 1 
           END
           ~> EmptyStack | e'])
         baseCaseSet_varsAEqual).
Proof.
  intros n i e e'
    [H_n_ge_2               [
     H_1_le_i               [
     H_i_le_n               [
     H_e_A_eq_e'_A          [
     H_e_B_eq_S_i           [
     H_e'_B_eq_S_i          [
     H_e_C_eq_n H_e'_C_eq_n
    ]]]]]]].
  remember (Nat.sub (n-1)%nat i)
    as   sub_nMinus1_i
    eqn: Heq_sub_nMinus1_i.
  generalize dependent n;
    generalize dependent e;
    generalize dependent e';
    generalize dependent i;
    generalize dependent sub_nMinus1_i.
  induction sub_nMinus1_i as [| sub_nMinus1_i IH_sub_nMinus1_i]; intros.
  
  (* (n - i), base case. *)
  - assert (H_nMinus1_eq_i: (n-1)%nat=i) by lia.
    fullSim baseCaseSet_varsAEqual.
    
  (* (n - i), inductive case. *)
  - stepLRUntilDone.
    assert (H_ite_eq: Nat.ltb (e B + 1) (e C)=Nat.ltb (e' B + 1) (e' C)) by congruence; rewrite H_ite_eq.
    repeat destAndClearLinIneq.
    stepLR.
    apply IH_sub_nMinus1_i with 
      (i  := S i)
      (n  := e C);
      repeat split;
      simpl;
      try (lia || congruence).
Qed.

Lemma sum1ToPredN_sim_sum0ToPredN_G1:
  forall n, fullSimulation (prog_sum1ToPredN n) (prog_sum0ToPredN n) baseCaseSet_varsAEqual.
Proof.
  induction n.
  - fullSim baseCaseSet_varsAEqual.
  - stepLRUntilDone.
    destLinIneq H_ineq_1_Sn.
    + stepLRUntilDone.
      destLinIneq H_ineq_2_Sn.
      * stepLR.
        apply sum1ToPredN_sim_sum0ToPredN_G2 with
          (n := S n)
          (i := 2);
          repeat split;
          lia.
      * fullSim baseCaseSet_varsAEqual.
    + fullSim baseCaseSet_varsAEqual.
Qed.

Lemma augmented_induction (P: nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H_P0 H_P1 H_ind.
  assert (forall n, P n /\ P (S n)). {
    induction n as [| n [P_n P_Sn]].
    - split; assumption.
    - split.
      + assumption.
      + apply H_ind; assumption.
  }
  apply H.
Qed.

Lemma sum1ToPredN_sim_sum1ToPredN_1LoopUnroll_G2:
  forall n i e e',
    n >= 3 /\ 1 <= i /\ i <= (n - 2)%nat
    /\ PeanoNat.Nat.Odd i
    /\ e A = e' A
    /\ e B = i /\ e' B = i
    /\ e C = n /\ e' C = n ->
      fullSimulation
        ([(A ::= A + B; B ::= B + 1);
           WHILE (B <? C) DO
            A ::= A + B; B ::= B + 1
           END
           ~> EmptyStack | e])
        
        ([(A ::= A + B; B ::= B + 1;
           A ::= A + B; B ::= B + 1);
           WHILE (B + 1 <? C) DO
            A ::= A + B; B ::= B + 1;
            A ::= A + B; B ::= B + 1
           END ~>
           EHole;
           ITE !(B + 1 <? C) & (B <? C) THEN
            A ::= A + B; B ::= B + 1
           ELSE SKIP ETI
           ~> EmptyStack | e'])
         baseCaseSet_varsAEqual.
Proof.
  intros n i e e'
    [H_n_ge_3               [
     H_1_le_i               [
     H_i_le_nMinus2         [
     H_i_odd                [
     H_e_A_eq_e'_A          [
     H_e_B_eq_i             [
     H_e'_B_eq_i            [
     H_e_C_eq_n H_e'_C_eq_n
    ]]]]]]]].
  remember (Nat.sub (Nat.sub n 2) i)
    as   sub_nMinus2_i
    eqn: Heq_sub_nMinus2_i.
  generalize dependent n;
    generalize dependent e;
    generalize dependent e';
    generalize dependent i;
    generalize dependent sub_nMinus2_i.
  induction sub_nMinus2_i
    as [| | sub_nMinus2_i IH_sub_nMinus2_i]
    using augmented_induction; intros.
    
  (* (n - 2 - i), base case 0. *)
  - assert (H_nMinus2_eq_i: (n-2)%nat=i) by lia.
    fullSim baseCaseSet_varsAEqual.
    
  (* (n - 2 - i), base case 1. *)
  - assert (H_nMinus3_eq_i: (n-3)%nat=i) by lia.
    fullSim baseCaseSet_varsAEqual.
    
  (* (n - 2 - i), augmented inductive case. *)
  - do 2 stepLUntilAfterIte.
    stepRUntilAfterIte.
    apply IH_sub_nMinus2_i with
      (i := S (S i))
      (n := n);
      simpl;
      try (lia || congruence).
    apply PeanoNat.Nat.Odd_succ_succ.
    assumption.
Qed.

Lemma sum1ToPredN_sim_sum1ToPredN_1LoopUnroll_G1: forall n,
  fullSimulation (prog_sum1ToPredN n) (prog_sum1ToPredN_1LoopUnroll n) baseCaseSet_varsAEqual.
Proof.
  induction n.
  - fullSim baseCaseSet_varsAEqual.
  - stepLRUntilDone.
    destLinIneq H_ineq_1_Sn; destLinIneq H_ineq_2_Sn.
    + stepLR.
      apply sum1ToPredN_sim_sum1ToPredN_1LoopUnroll_G2 with
        (n := S n)
        (i := 1);
        repeat split;
        try (lia || congruence).
      apply PeanoNat.Nat.odd_spec; reflexivity.
    + fullSim baseCaseSet_varsAEqual.
    + fullSim baseCaseSet_varsAEqual.
Qed.

Lemma augmented_induction' (P: nat -> Prop) :
  P 0 ->
  P 1 ->
  P 2 ->
  (forall n, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n)))) ->
  forall n, P n.
Proof.
  intros H_P0 H_P1 H_P2 H_ind.
  assert (forall n, P n /\ P (S n) /\ P (S (S n))). {
    induction n as [| n [P_n [P_Sn P_SSn]]].
    - repeat split; assumption.
    - repeat split.
      + assumption.
      + assumption.
      + apply H_ind; assumption.
  }
  apply H.
Qed.

Lemma sum1ToPredN_sim_sum1ToPredN_2LoopUnrolls_G2:
  forall n i e e',
    n >= 4 /\ 1 <= i /\ i <= (n - 3)%nat
    /\ (exists x, i = (1 + 3*x)%nat)
    /\ e A = e' A
    /\ e B = i /\ e' B = i
    /\ e C = n /\ e' C = n ->
      fullSimulation
        ([(A ::= A + B; B ::= B + 1);
           WHILE (B <? C) DO
            A ::= A + B; B ::= B + 1
           END
           ~> EmptyStack | e])
        
        ([(A ::= A + B; B ::= B + 1;
           A ::= A + B; B ::= B + 1;
           A ::= A + B; B ::= B + 1);
           WHILE (B + 2 <? C) DO
            A ::= A + B; B ::= B + 1;
            A ::= A + B; B ::= B + 1;
            A ::= A + B; B ::= B + 1
           END ~>
           EHole;
           ITE !(B + 2 <? C) & (B + 1 <? C) THEN
            A ::= A + B; B ::= B + 1;
            A ::= A + B; B ::= B + 1
           ELSE ITE !(B + 2 <? C) & !(B + 1 <? C) & (B <? C) THEN
            A ::= A + B; B ::= B + 1
           ELSE SKIP ETI ETI
           ~> EmptyStack | e'])
         baseCaseSet_varsAEqual.
Proof.
  intros n i e e'
    [H_n_ge_4               [
     H_1_le_i               [
     H_i_le_nMinus3         [
     [x H_i_eq_SmultOf3]    [
     H_e_A_eq_e'_A          [
     H_e_B_eq_i             [
     H_e'_B_eq_i            [
     H_e_C_eq_n H_e'_C_eq_n
    ]]]]]]]].
  remember (Nat.sub (Nat.sub n 3) i)
    as   sub_nMinus3_i
    eqn: Heq_sub_nMinus3_i.
  generalize dependent n;
    generalize dependent x;
    generalize dependent e;
    generalize dependent e';
    generalize dependent i;
    generalize dependent sub_nMinus3_i.
  induction sub_nMinus3_i
    as [| | | sub_nMinus3_i IH_sub_nMinus3_i]
    using augmented_induction'; intros.
    
  (* (n - 3), base case 0. *)
  - assert (H_nMinus3_eq_i: (n-3)%nat=i) by lia.
    fullSim baseCaseSet_varsAEqual.
    
  (* (n - 3), base case 1. *)
  - assert (H_nMinus4_eq_i: (n-4)%nat=i) by lia.
    fullSim baseCaseSet_varsAEqual.
    
  (* (n - 3), base case 2. *)
  - assert (H_nMinus5_eq_i: (n-5)%nat=i) by lia.
    fullSim baseCaseSet_varsAEqual.
    
  (* (n - 3), inductive case. *)
  - do 3 stepLUntilAfterIte.
    stepRUntilAfterIte.
    apply IH_sub_nMinus3_i
      with (i := S (S (S i)))
           (n := n)
           (x := (x+1)%nat);
      simpl;
      (lia || congruence).
Qed.

Lemma sum1ToPredN_sim_sum1ToPredN_2LoopUnrolls_G1: forall n,
  fullSimulation (prog_sum1ToPredN n) (prog_sum1ToPredN_2LoopUnrolls n) baseCaseSet_varsAEqual.
Proof.
  destruct n.
  - fullSim baseCaseSet_varsAEqual.
  - stepLRUntilDone.
    destLinIneq H_ineq_1_Sn;
    destLinIneq H_ineq_3_Sn.
    + stepLR.
      apply sum1ToPredN_sim_sum1ToPredN_2LoopUnrolls_G2 
        with (n := S n)
             (i := 1);
        repeat split;
        try (lia || congruence).
      exists 0; reflexivity.
    + stepLRUntilDone.
      destLinIneq H_ineq_2_Sn; fullSim baseCaseSet_varsAEqual.
    + fullSim baseCaseSet_varsAEqual.
Qed.

(****** Code hoisting simulation proofs. ******)
Lemma coincidingIteBranchAssignment_sim_itsOptimizedVariant: forall a,
  fullSimulation (prog_coincidingIteBranchAssignment a) (prog_coincidingIteBranchAssignment_optimized a) baseCaseSet_envsEqual.
Proof.
  induction a; fullSim baseCaseSet_varsAEqual.
Qed.

(****** Loop invariant code motion (LICM) simulation proofs. ******)
Lemma invariantCodeInLoop_sim_itsOptimizedVariant_G2: forall i n (a c:nat) e e',
  S a <= i /\ i <= (n-1)%nat /\
  e A = e' A               /\
  e B = e' B               /\
  e C = e' C               /\
  e A = i /\ e' A = i      /\
  e B = n /\ e' B = n      /\
  e C = c /\ e' C = c      ->
    fullSimulation
      ([(C ::= c; A ::= A + 1);
        WHILE (A <? B) DO
         C ::= c;
         A ::= A + 1
        END
      ~> EmptyStack | e])
      
      ([A ::= A + 1;
        WHILE (A <? B) DO
         A ::= A + 1
        END
      ~> EmptyStack | e'])
      baseCaseSet_varsABCEqual.
Proof.
  intros i n a c e e'
    [H_Sa_le_i      [
     H_i_le_predN  [
     H_e_A_eq_e'_A [
     H_e_B_eq_e'_B [
     H_e_C_eq_e'_C [
     H_e_A_eq_i    [
     H_e'_A_eq_i   [
     H_e_B_eq_n    [
     H_e'_B_eq_n   [
     H_e_C_eq_c
     H_e'_C_eq_c
    ]]]]]]]]]].
  remember (Nat.sub (n-1)%nat i)
    as   sub_nMinus1_i
    eqn: Heq_sub_nMinus1_i.
  generalize dependent i;
    generalize dependent n;
    generalize dependent a;
    generalize dependent c;
    generalize dependent e;
    generalize dependent e'.
  induction sub_nMinus1_i as [| sub_nMinus1_i IH_sub_nMinus1_i]; intros.
  (* (n - i), base case. *)
  - assert (H_nMinus1_eq_i: (n-1)%nat=i) by lia.
    fullSim baseCaseSet_varsABCEqual.
  (* (n - i), inductive case. *)
  - stepLRUntilDone.
    assert (H_ite_eq: Nat.ltb (e A + 1) (e B)=Nat.ltb (e' A + 1) (e' B)) by congruence; rewrite H_ite_eq.
    repeat destAndClearLinIneq.
    stepLR.
    apply IH_sub_nMinus1_i with
      (i  := S i)
      (n  := e B)
      (a  := a);
      repeat split;
      simpl;
      try (lia || congruence).
Qed.

Lemma invariantCodeInLoop_sim_itsOptimizedVariant_G1: forall a b c,
  fullSimulation (prog_invariantCodeInLoop a b c) (prog_invariantCodeInLoop_optimized a b c) baseCaseSet_varsABCEqual.
Proof.
  intros.
  generalize dependent a;
    generalize dependent c.
  induction b as [| b IH_b]; intros.
  (* b, base case. *)
  - fullSim baseCaseSet_varsABCEqual.
  (* b, inductive case. *)
  - destruct (Nat.ltb a (S b)) eqn:H_ltb_a_Sb.
    (* a < S b *)
    + apply PeanoNat.Nat.ltb_lt in H_ltb_a_Sb.
      unfold prog_invariantCodeInLoop, prog_invariantCodeInLoop_optimized.
      stepLRUntilAfterIte.
      stepLRUntilDone.
      destLinIneq H_ltb_Sa_Sb.
      (* S a < S b *)
      * stepL; do 2 stepRUntilAfterIte.
        apply invariantCodeInLoop_sim_itsOptimizedVariant_G2
           with (a := a)
                (i := S a)
                (n := S b);
           repeat split;
           simpl;
           try (lia || congruence).
      (* S a >= S b *)
      * fullSim baseCaseSet_varsABCEqual.
    (* a >= S b *)
    + apply PeanoNat.Nat.ltb_nlt in H_ltb_a_Sb.
      unfold prog_invariantCodeInLoop, prog_invariantCodeInLoop_optimized.
      fullSim baseCaseSet_varsABCEqual.
Qed.

(****** Loop peeling simulation proofs. ******)
Lemma peelableLoopInstruction_sim_optimizedVariant_G2: forall a n c i e e',
  S a <= i /\ i <= (n-1)%nat /\
  e A = e' A /\
  e B = e' B /\
  e C = e' C /\
  e A = i /\ e' A = i /\
  e B = n /\ e' B = n /\
  e C = c /\ e' C = c ->
    fullSimulation
      ([(C ::= C + 10; A ::= A + 1);
        WHILE (A <? B) DO
          C ::= C + 10;
          A ::= A + 1
        END
      ~> EmptyStack | e])
      ([(C ::= C + 10; A ::= A + 1);
        WHILE (A <? B) DO
          C ::= C + 10;
          A ::= A + 1
        END
      ~> EmptyStack | e'])
      baseCaseSet_varsABCEqual.
Proof.
  intros a n c i e e'
    [H_Sa_le_i     [
     H_i_le_predN  [
     H_e_A_eq_e'_A [
     H_e_B_eq_e'_B [
     H_e_C_eq_e'_C [
     H_e_A_eq_i    [
     H_e'_A_eq_i   [
     H_e_B_eq_n    [
     H_e'_B_eq_n   [
     H_e_C_eq_c
     H_e'_C_eq_c
    ]]]]]]]]]].
  remember (Nat.sub (n-1)%nat i)
    as   sub_nMinus1_i
    eqn: Heq_sub_nMinus1_i.
  generalize dependent a;
    generalize dependent n;
    generalize dependent c;
    generalize dependent i;
    generalize dependent e;
    generalize dependent e'.
  induction sub_nMinus1_i as [| sub_nMinus1_i IH_sub_nMinus1_i]; intros.
  (* (n - i), base case. *)
  - assert (H_nMinus1_eq_i: (n-1)%nat=i) by lia.
    fullSim baseCaseSet_varsABCEqual.
  (* (n - i), inductive case. *)
  - stepLRUntilDone.
    assert (H_ite_eq: Nat.ltb (e A + 1) (e B)=Nat.ltb (e' A + 1) (e' B)) by congruence; rewrite H_ite_eq.
    repeat destAndClearLinIneq.
    stepLR.
    apply IH_sub_nMinus1_i with
      (a  := a)
      (n  := e B)
      (i  := S i)
      (c  := (e C + 10)%nat);
      repeat split;
      simpl;
      try (lia || congruence).
Qed.

Lemma peelableLoopInstruction_sim_optimizedVariant_G1: forall a b c,
  fullSimulation (prog_peelableLoopInstruction a b c) (prog_peelableLoopInstruction_optimized a b c) baseCaseSet_varsABCEqual.
Proof.
  intros.
  generalize dependent a;
    generalize dependent c.
  induction b as [| b IH_b]; intros.
  (* b, base case. *)
  - fullSim baseCaseSet_varsABCEqual.
  (* b, inductive case. *)
  - destruct (Nat.ltb a (S b)) eqn:H_ltb_a_Sb.
    (* a < S b *)
    + apply PeanoNat.Nat.ltb_lt in H_ltb_a_Sb.
      unfold prog_peelableLoopInstruction, prog_peelableLoopInstruction_optimized.
      stepLRUntilAfterIte.
      stepLRUntilDone.
      destLinIneq H_ltb_Sa_Sb.
      (* S a < S b *)
      * stepLR.
        apply peelableLoopInstruction_sim_optimizedVariant_G2
           with (a := a)
                (n := S b)
                (c := (c + 10)%nat)
                (i := S a);
           repeat split;
           simpl;
           try (lia || congruence).
      (* S a >= S b *)
      * fullSim baseCaseSet_varsABCEqual.
    (* a >= S b *)
    + apply PeanoNat.Nat.ltb_nlt in H_ltb_a_Sb.
      unfold prog_invariantCodeInLoop, prog_invariantCodeInLoop_optimized.
      fullSim baseCaseSet_varsABCEqual.
Qed.

(****** Software pipelining simulation proofs. ******)
Lemma potentialSoftwarePipeline_sim_optimizedVariant_G2: forall a n c d i e e',
  1 <= n /\
  100 <= c /\
  a <= i /\ i <= (n-1)%nat /\
  e A = e' A /\
  e B = e' B /\
  e C = e' C /\
  e D = e' D /\
  e A = i /\ e' A = i /\
  e B = n /\ e' B = n /\
  e C = c /\ e' C = c /\
  e D = d /\ e' D = d ->
  fullSimulation
    ([D ::= D + 10; A ::= A + 1 ~>
      EHole;
      WHILE (A <? B) DO
        C ::= C + 100;
        D ::= D + 10;
        A ::= A + 1
      END
    
    ~> EmptyStack | e])
    ([WHILE (A <? B-1) DO
        D ::= D + 10;
        A ::= A + 1;
        C ::= C + 100
      END ~>
      
      EHole;
      D ::= D + 10;
      A ::= A + 1
    ~> EmptyStack | e'])
    baseCaseSet_varsABCDEqual.
Proof.
  intros a n c d i e e'
    [H_1_le_n      [
     H_100_le_c    [
     H_a_le_i      [
     H_i_le_predN  [
     H_e_A_eq_e'_A [
     H_e_B_eq_e'_B [
     H_e_C_eq_e'_C [
     H_e_D_eq_e'_D [
     H_e_A_eq_i    [
     H_e'_A_eq_i   [
     H_e_B_eq_n    [
     H_e'_B_eq_n   [
     H_e_C_eq_c    [
     H_e'_C_eq_c   [
     H_e_D_eq_d
     H_e'_D_eq_d
    ]]]]]]]]]]]]]]].
  remember (Nat.sub (n-1)%nat i)
    as   sub_nMinus1_i
    eqn: Heq_sub_nMinus1_i.
  generalize dependent a;
    generalize dependent n;
    generalize dependent c;
    generalize dependent d;
    generalize dependent i;
    generalize dependent e;
    generalize dependent e'.
  induction sub_nMinus1_i as [| sub_nMinus1_i IH_sub_nMinus1_i]; intros.
  (* (n - i), base case. *)
  - assert (H_nMinus1_eq_i: (n-1)%nat=i) by lia.
    fullSim baseCaseSet_varsABCDEqual.
  (* (n - i), inductive case. *)
  - stepLRUntilDone.
    repeat destAndClearLinIneq.
    stepLNRM 11 28.
    apply IH_sub_nMinus1_i with
      (a  := a)
      (n  := e B)
      (i  := S i)
      (c  := (e C+100)%nat)
      (d  := (d+10)%nat);
      repeat split;
      simpl;
      try (lia || congruence).
Qed.

Lemma potentialSoftwarePipeline_sim_optimizedVariant_G1: forall a b c d,
  fullSimulation (prog_potentialSoftwarePipeline a b c d) (prog_potentialSoftwarePipeline_optimized a b c d) baseCaseSet_varsABCDEqual.
Proof.
  intros.
  generalize dependent a;
    generalize dependent c;
    generalize dependent d.
  induction b as [| b IH_b]; intros.
  (* b, base case. *)
  - fullSim baseCaseSet_varsABCDEqual.
  (* b, inductive case. *)
  - destruct (Nat.ltb a (S b)) eqn:H_ltb_a_Sb.
    (* a < S b *)
    + apply PeanoNat.Nat.ltb_lt in H_ltb_a_Sb.
      unfold prog_potentialSoftwarePipeline, prog_potentialSoftwarePipeline_optimized.
      stepLRUntilDone.
      destAndClearLinIneq.
      stepLRUntilDone.
      destLinIneq H_Sa_Sb.
      (* S a < S b *)
      * destLinIneq H_ltb_a_b.
        stepLNRM 11 28.
        apply potentialSoftwarePipeline_sim_optimizedVariant_G2
           with (a := a)
                (n := S b)
                (c := (c + 100 + 100)%nat)
                (d := (d + 10)%nat)
                (i := S a);
           repeat split;
           simpl;
           try (lia || congruence).
      (* S a >= S b *)
      * fullSim baseCaseSet_varsABCDEqual.
    (* a >= S b *)
    + apply PeanoNat.Nat.ltb_nlt in H_ltb_a_Sb.
      unfold prog_potentialSoftwarePipeline, prog_potentialSoftwarePipeline_optimized.
      fullSim baseCaseSet_varsABCDEqual.
Qed.
