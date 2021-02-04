(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Map.
Require Import Languages.WHILE.Syntax.
Require Import Languages.WHILE.Semantics.

Definition E := Identifier 4.

Example prog_twoInterchangeableLoops (b d e:nat) :=
  [B ::= b;
   D ::= d;
   E ::= e;
   
   A ::= 0;
   C ::= 0;
   
   ITE (C <? D) THEN
    WHILE (A <? B) DO
      C ::= 0;
      
      WHILE (C <? D) DO
        E ::= E + 1;
        C ::= C + 1
      END;
      
      A ::= A + 1
    END
   ELSE SKIP ETI
  ~> EmptyStack | map_id_nat_empty].

Example prog_twoInterchangeableLoops_optimized (b d e:nat) :=
  [B ::= b;
   D ::= d;
   E ::= e;
   
   A ::= 0;
   C ::= 0;
   
   ITE (A <? B) THEN
    WHILE (C <? D) DO
      A ::= 0;
      
      WHILE (A <? B) DO
        E ::= E + 1;
        A ::= A + 1
      END;
      
      C ::= C + 1
    END
   ELSE SKIP ETI
  ~> EmptyStack | map_id_nat_empty].
