Require Import Basics.Aux.
Require Import Languages.LC.Syntax.
Require Import Languages.LC.Semantics.
Require Import Languages.LC.ChurchEncoding.

Example prog_lambdaSum0ToPredN (n:nat) :=
  sumFromNToM' zero (natToChurch $ n - 1) ~> EmptyStack.
