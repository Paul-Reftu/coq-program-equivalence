(* Internal import(s). *)
Require Import Basics.Map.
Require Import Languages.WHILE.Syntax.
Require Import Languages.WHILE.Semantics.

(****** Loop invariant code motion (LICM) programs. ******)
Example prog_invariantCodeInLoop (a b c:nat) :=
  [A ::= a;
   B ::= b;
   
   WHILE (A <? B) DO
    C ::= c;
    A ::= A + 1
   END
  ~> EmptyStack | map_id_nat_empty].

Example prog_invariantCodeInLoop_optimized (a b c:nat) :=
  [A ::= a;
   B ::= b;
   
   ITE (A <? B) THEN
    C ::= c;
    
    WHILE (A <? B) DO
      A ::= A + 1
    END
   ELSE SKIP ETI
  ~> EmptyStack | map_id_nat_empty].
