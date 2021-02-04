(* External import(s). *)
Require Import Coq.Strings.String.
(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Aux.
Require Import Basics.Map.
Require Import Languages.WHILE.Syntax.
Require Import Languages.WHILE.Semantics.

Example prog_incr0To5 :=
  [A ::= 0;
   WHILE A <? 5 DO
     A ::= A + 1
   END
  ~> EmptyStack | map_id_nat_empty].

Example prog_decr10To5 :=
  [A ::= 10;
   WHILE !(A <? 6) DO
     A ::= A - 1
   END
  ~> EmptyStack | map_id_nat_empty].

Example prog_sum1ToPredN (n:nat) :=
  [A ::= 0; 
   B ::= 1;
   C ::= n;
   WHILE B <? C DO
     A ::= A + B;
     B ::= B + 1
   END
  ~> EmptyStack | map_id_nat_empty].

Example prog_sum0ToPredN (n:nat) :=
  [A ::= 0; 
   B ::= 0;
   C ::= n;
   WHILE B <? C DO
     A ::= A + B;
     B ::= B + 1
   END
  ~> EmptyStack | map_id_nat_empty].

Example prog_sum1ToPredN_1LoopUnroll (n:nat) :=
  [A ::= 0;
   B ::= 1;
   C ::= n;
   WHILE (B + 1) <? C DO
     A ::= A + B;
     B ::= B + 1;
     A ::= A + B;
     B ::= B + 1
   END;
   ITE !(B + 1 <? C) & (B <? C) THEN
    A ::= A + B;
    B ::= B + 1
   ELSE SKIP ETI
   ~> EmptyStack | map_id_nat_empty].

Example prog_sum1ToPredN_2LoopUnrolls (n:nat) :=
  [A ::= 0;
   B ::= 1;
   C ::= n;
   WHILE (B + 2) <? C DO
    A ::= A + B; B ::= B + 1;
    A ::= A + B; B ::= B + 1;
    A ::= A + B; B ::= B + 1
   END;
   ITE !(B + 2 <? C) & (B + 1 <? C) THEN
    A ::= A + B; B ::= B + 1;
    A ::= A + B; B ::= B + 1
   ELSE ITE !(B + 2 <? C) & !(B + 1 <? C) & (B <? C) THEN
    A ::= A + B; B ::= B + 1
   ELSE SKIP ETI ETI
  ~> EmptyStack | map_id_nat_empty].

Example prog_sumPredNTo1 (n:nat) :=
  [A ::= 0; 
   B ::= n - 1;
   C ::= n;
   WHILE !(B <? 1) DO
     A ::= A + B;
     B ::= B - 1
   END
  ~> EmptyStack | map_id_nat_empty].
