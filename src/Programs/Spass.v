(* External import(s). *)
Require Import Coq.Strings.String.
(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Aux.
Require Import Basics.Map.
Require Import Languages.Spass.Syntax.
Require Import Languages.Spass.Semantics.

Example prog_lambdaSum0ToN (n:nat) :=
  [EApp (EFix D (
    EAbs A (
      ITE A ==? 0 THEN 
        0
      ELSE
        A + (EApp D (A - 1))
      ETI)
    )) n
   ~> EmptyStack | map_id_nat_empty].
Compute runNSteps 906 $ prog_lambdaSum0ToN 100.
Compute runNSteps 1105 $ prog_lambdaSum0ToN 100.

Example prog_tailRecLambdaSum0ToN (n i a:nat) :=
  [EApp (EApp (EApp (EFix D (
    EAbs A (EAbs B (EAbs C (
      ITE !(B <? A) & !(B ==? A) THEN
        C
      ELSE
        EApp (EApp (EApp D A) (B+1)) (C+B)
      ETI
   ))))) n) i) a
   ~> EmptyStack | map_id_nat_empty].
Compute runNSteps 1009 $ prog_tailRecLambdaSum0ToN 100 0 0.
Compute runNSteps 2952 $ prog_tailRecLambdaSum0ToN 100 0 0.
