(* Internal import(s). *)
Require Import Basics.Map.
Require Import Languages.WHILE.Syntax.
Require Import Languages.WHILE.Semantics.

Example prog_coincidingIteBranchAssignment (a:nat) :=
  [ITE true THEN
    A ::= a;
    A ::= A * 10
   ELSE
    A ::= a;
    A ::= A * 100
   ETI
  ~> EmptyStack | map_id_nat_empty].

Example prog_coincidingIteBranchAssignment_optimized (a:nat) :=
  [A ::= a;
  
   ITE true THEN
    A ::= A * 10
   ELSE
    A ::= A * 100
   ETI
  ~> EmptyStack | map_id_nat_empty].
