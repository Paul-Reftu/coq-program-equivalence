(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Map.

Inductive exp: Type :=
  | EId  (x   : identifier)
  | EAbs (x   : identifier) (e: exp)
  | EApp (e e': exp)
  | EHole.

Inductive stack: Type :=
  | EmptyStack
  | Stack      (e: exp) (s:stack).

Inductive cfg: Type :=
  Cfg (s: stack) (m: map_id_nat).
Definition emptyCfg := Cfg EmptyStack map_id_nat_empty.

Coercion EId  : identifier >-> exp.
Notation "e '~>' st" := (Stack e st) (at level 80, right associativity).
Notation "[ s | m ]" := (Cfg s m)    (at level 90).
