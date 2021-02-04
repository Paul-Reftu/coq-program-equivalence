(* Internal import(s). *)
Require Import Basics.Map.
Require Import Languages.WHILE.Syntax.
Require Import Languages.WHILE.Semantics.

Example prog_potentialSoftwarePipeline (a b c d:nat) :=
  [A ::= a;
   B ::= b;
   C ::= c;
   D ::= d;
   
   WHILE (A <? B) DO
    C ::= C + 100;
    D ::= D + 10;
    A ::= A + 1
   END
  ~> EmptyStack | map_id_nat_empty].

Example prog_potentialSoftwarePipeline_optimized (a b c d:nat) :=
  [A ::= a;
   B ::= b;
   C ::= c;
   D ::= d;
   
   ITE (A <? B) THEN
    C ::= C + 100;
    
    WHILE (A <? B-1) DO
      D ::= D + 10;
      A ::= A + 1;
      C ::= C + 100
    END;
    
    D ::= D + 10;
    A ::= A + 1
   ELSE SKIP ETI
  ~> EmptyStack | map_id_nat_empty].
