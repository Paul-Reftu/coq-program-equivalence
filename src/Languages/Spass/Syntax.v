(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Map.

Inductive exp: Type :=
  (* Primitives. *)
  | ENat  (x: nat)
  | EBool (x: bool)
  | EId   (x: identifier)
  (* Arithmetic operators. *)
  | EAdd (e e': exp)
  | ESub (e e': exp)
  | EMul (e e': exp)
  | EDiv (e e': exp)
  (* Logical operators. *)
  | EEq  (e e': exp)
  | ELt  (e e': exp)
  | ENot (e   : exp)
  | EAnd (e e': exp)
  (* Imperative commands. *)
  | ESkip 
  | ESeq   (e e'    : exp)
  | EAss   (x       : identifier) (e: exp)
  | EWhile (e e'    : exp)
  | EIte   (e e' e'': exp)
  (* Lambdas. *)
  | EAbs (x   : identifier) (e: exp)
  | EFix (x   : identifier) (e: exp)
  | EApp (e e': exp)
  (* Hole. *)
  | EHole.

(* Stack type. *)
Inductive stack: Type :=
  | EmptyStack
  | Stack      (e: exp) (s:stack).

(* Configuration/env type. *)
Inductive cfg: Type := 
  Cfg (s: stack) (m: map_id_nat).
Definition emptyCfg := Cfg EmptyStack map_id_nat_empty.
Definition getStackOfCfg (config:cfg): stack :=
  match config with
  | Cfg s _ => s
  end.
Definition getEnvOfCfg (config:cfg): map_id_nat :=
  match config with
  | Cfg _ e => e
  end.

(* Notations and whatnot. *)
Coercion ENat : nat        >-> exp.
Coercion EBool: bool       >-> exp.
Coercion EId  : identifier >-> exp.
Infix "+"      := EAdd (at level 50, left associativity).
Infix "-"      := ESub (at level 50, left associativity).
Infix "*"      := EMul (at level 40, left associativity).
Infix "/"      := EDiv (at level 40, left associativity).
Infix "==?"    := EEq  (at level 55, left associativity).
Infix "<?"     := ELt  (at level 54, left associativity).
Infix "&"      := EAnd (at level 56, left associativity).
Notation "! b" := (ENot b)   (at level 30, right associativity).

Notation "'SKIP'"    :=
  (ESkip).
Notation "c1 ; c2"   :=
  (ESeq c1 c2)
  (at level 70, right associativity).
Notation "x '::=' e" := 
  (EAss x e)
  (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (EWhile b c)
  (at level 70, right associativity).
Notation "'ITE' b 'THEN' c1 'ELSE' c2 'ETI'" :=
  (EIte b c1 c2)
  (at level 70, right associativity).

Notation "e '~>' st" := (Stack e st) (at level 80, right associativity).
Notation "[ s | m ]" := (Cfg s m)    (at level 90).
