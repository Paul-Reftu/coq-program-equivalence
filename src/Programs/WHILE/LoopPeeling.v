(* Internal import(s). *)
Require Import Basics.Map.
Require Import Languages.WHILE.Syntax.
Require Import Languages.WHILE.Semantics.

Example prog_peelableLoopInstruction (a b c:nat) :=
  [A ::= a;
   B ::= b;
   C ::= c;
   
   WHILE (A <? B) DO
    C ::= C + 10;
    A ::= A + 1
   END
  ~> EmptyStack | map_id_nat_empty].

Example prog_peelableLoopInstruction_optimized (a b c:nat) :=
  [A ::= a;
   B ::= b;
   C ::= c;
   
   ITE (A <? B) THEN
    C ::= C + 10;
    A ::= A + 1;
    
    WHILE (A <? B) DO
      C ::= C + 10;
      A ::= A + 1
    END
   ELSE SKIP ETI
  ~> EmptyStack | map_id_nat_empty].
