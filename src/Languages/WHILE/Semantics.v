(* External import(s). *)
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import         ListNotations.
(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Aux.
Require Import Basics.Map.
Require Import Languages.WHILE.Syntax.

Definition isval (e:exp): bool :=
  match e with
    | ENat  _ => true
    | EBool _ => true
    | _       => false
  end.

Definition runStep (config:cfg): option cfg :=
  match config with
  | [EmptyStack | env] => None

  | [SKIP ~> s | env]  => Some $ [s | env]

    (* Assignments *)
  | [x ::= e ~> s | env] =>
      if (isval e) then
        match e with
        | ENat i => Some $ [s | x |-> i IN env]
        | _      => None
        end
      else 
        Some $ [e ~> x ::= EHole ~> s | env]
  | [ENat i ~> x ::= EHole ~> s | env] =>
      Some $ [x ::= i ~> s | env]

  (* Identifier lookup. *)
  | [EId k ~> s | env] =>
      Some $ [find k env ~> s | env]

  (* Addition. *)
  | [e1 + e2 ~> s | env] =>
      if (isval e1 && isval e2) then
        match (e1, e2) with
        | (ENat i1, ENat i2) => Some $ [ENat (plus i1 i2) ~> s | env]
        | _                  => Some $ [s | env]
        end
      else if (isval e1) then
        match e1 with
        | ENat _  => Some $ [e2 ~> e1 + EHole ~> s | env]
        | _       => Some $ [s | env]
        end
      else
        Some $ [e1 ~> EHole + e2 ~> s | env]
  | [ENat i1 ~> EHole + e2 ~> s | env] =>
      Some $ [i1 + e2 ~> s | env]
  | [ENat i2 ~> e1 + EHole ~> s | env] =>
      Some $ [e1 + i2 ~> s | env]

  (* Subtraction. *)
  | [e1 - e2 ~> s | env] =>
      if (isval e1 && isval e2) then
        match (e1, e2) with
        | (ENat i1, ENat i2) => Some $ [ENat (minus i1 i2) ~> s | env]
        | _                  => Some $ [s | env]
        end
      else if (isval e1) then
        match e1 with
        | ENat _  => Some $ [e2 ~> e1 - EHole ~> s | env]
        | _       => Some $ [s | env]
        end
      else
        Some $ [e1 ~> EHole - e2 ~> s | env]
  | [ENat i1 ~> EHole - e2 ~> s | env] =>
      Some $ [i1 - e2 ~> s | env]
  | [ENat i2 ~> e1 - EHole ~> s | env] =>
      Some $ [e1 - i2 ~> s | env]

  (* Multiplication. *)
  | [e1 * e2 ~> s | env] =>
      if (isval e1 && isval e2) then
        match (e1, e2) with
        | (ENat i1, ENat i2) => Some $ [ENat (mult i1 i2) ~> s | env]
        | _                  => Some $ [s | env]
        end
      else if (isval e1) then
        match e1 with
        | ENat i1 => Some $ [e2 ~> e1 * EHole ~> s | env]
        | _       => Some $ [s | env]
        end
      else
        Some $ [e1 ~> EHole * e2 ~> s | env]
  | [ENat i1 ~> EHole * e2 ~> s | env] =>
      Some $ [i1 * e2 ~> s | env]
  | [ENat i2 ~> e1 * EHole ~> s | env] =>
      Some $ [e1 * i2 ~> s | env]

  (* Division. *)
  | [e1 / e2 ~> s | env] =>
      if (isval e1 && isval e2) then
        match (e1, e2) with
        | (ENat i1, ENat i2) => Some $ [ENat (Nat.div i1 i2) ~> s | env]
        | _                  => Some $ [s | env]
        end
      else if (isval e1) then
        match e1 with
        | ENat _ => Some $ [e2 ~> e1 / EHole ~> s | env]
        | _      => Some $ [s | env]
        end
      else
        Some $ [e1 ~> EHole / e2 ~> s | env]
  | [ENat i1 ~> EHole / e2 ~> s | env] =>
      Some $ [i1 / e2 ~> s | env]
  | [ENat i2 ~> e1 / EHole ~> s | env] =>
      Some $ [e1 / i2 ~> s | env]

  (* Logical negation. *)
  | [!e1 ~> s | env] =>
      if (isval e1) then
        match e1 with
        | EBool b1 => Some $ [EBool (negb b1) ~> s | env]
        | _        => Some $ [s | env]
        end
      else
        Some $ [e1 ~> !EHole ~> s | env]
  | [EBool e1 ~> !EHole ~> s | env] =>
      Some $ [!e1 ~> s | env]

  (* Equality. *)
  | [e1 ==? e2 ~> s | env] =>
      if (isval e1 && isval e2) then
        match (e1, e2) with
        | (ENat i1, ENat i2) => Some $ [EBool (Nat.eqb i1 i2) ~> s | env]
        | _                  => Some $ [s | env]
        end
      else if (isval e1) then
        match e1 with
        | ENat _ => Some $ [e2 ~> e1 ==? EHole ~> s | env]
        | _      => Some $ [s | env]
        end
      else
        Some $ [e1 ~> EHole ==? e2 ~> s | env]
  | [ENat e1 ~> EHole ==? e2 ~> s | env] =>
      Some $ [e1 ==? e2 ~> s | env]
  | [ENat e2 ~> e1 ==? EHole ~> s | env] =>
      Some $ [e1 ==? e2 ~> s | env]
  
  (* Less-than. *)
  | [e1 <? e2 ~> s | env] =>
      if (isval e1 && isval e2) then
        match (e1, e2) with
        | (ENat i1, ENat i2) => Some $ [EBool (Nat.ltb i1 i2) ~> s | env]
        | _                  => Some $ [s | env]
        end
      else if (isval e1) then
        match e1 with
        | ENat _  => Some $ [e2 ~> e1 <? EHole ~> s | env]
        | _       => Some $ [s | env]
        end
      else
        Some $ [e1 ~> EHole <? e2 ~> s | env]
  | [ENat e1 ~> EHole <? e2 ~> s | env] =>
      Some $ [e1 <? e2 ~> s | env]
  | [ENat e2 ~> e1 <? EHole ~> s | env] =>
      Some $ [e1 <? e2 ~> s | env]

  (* Logical and. *)
  | [e1 & e2 ~> s | env] =>
      if (isval e1 && isval e2) then
        match (e1, e2) with
        | (EBool b1, EBool b2) => Some $ [EBool (andb b1 b2) ~> s | env]
        | _                    => Some $ [s | env]
        end
      else if (isval e1) then
        match e1 with
        | EBool _ => Some $ [e2 ~> e1 & EHole ~> s | env]
        | _       => Some $ [s | env]
        end
      else
        Some $ [e1 ~> EHole & e2 ~> s | env]
  | [EBool b1 ~> EHole & e2 ~> s | env] =>
      Some $ [(EBool b1) & e2 ~> s | env]
  | [EBool b2 ~> e1 & EHole ~> s | env] =>
      Some $ [e1 & (EBool b2) ~> s | env]

  (* If-then-else. *)
  | [ITE e1 THEN e2 ELSE e3 ETI ~> s | env] =>
      if (isval e1) then
        match e1 with
        | EBool true  => Some $ [e2 ~> s | env]
        | EBool false => Some $ [e3 ~> s | env]
        | _           => Some $ [s | env]
        end
      else
        Some $ [e1 ~> ITE EHole THEN e2 ELSE e3 ETI ~> s | env]
  | [EBool b1 ~> ITE EHole THEN e2 ELSE e3 ETI ~> s | env] =>
      Some $ [ITE (EBool b1) THEN e2 ELSE e3 ETI ~> s | env]

  (* While loop. *)
  | [WHILE e1 DO e2 END ~> s | env] =>
      Some $ [ITE e1 THEN (e2; WHILE e1 DO e2 END) ELSE SKIP ETI ~> s | env]

  (* Sequence. *)
  | [e1;e2 ~> s | env] =>
      if (isval e1) then
        Some $ [e2 ~> s | env]
      else
         match e1 with
         | EHole => Some $ [e2 ~> s | env]
         | _     => Some $ [e1 ~> EHole;e2 ~> s | env]
         end
  | [ENat e1 ~> EHole;e2 ~> s | env] =>
      Some $ [(ENat e1);e2 ~> s | env]
  | [EBool b1 ~> EHole;e2 ~> s | env] =>
      Some $ [(EBool b1);e2 ~> s | env]

  | [EHole ~> s | env] => Some $ [s | env]
  
  | cfg => None
  end.

Fixpoint runNSteps (n:nat) (config:cfg): option cfg :=
  match n with
  | O    => ret config
  | S n' => runStep config >>=
      fun config' => runNSteps n' config'
  end.
