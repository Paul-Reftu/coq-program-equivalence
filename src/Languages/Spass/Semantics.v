(* External import(s). *)
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import         ListNotations.
(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Aux.
Require Import Basics.Map.
Require Import Languages.Spass.Syntax.

Definition isval (e:exp): bool :=
  match e with
    | ENat  _   => true
    | EBool _   => true
    | EAbs  _ _ => true
    | EFix _ _  => true
    | _         => false
  end.

Definition isval' (e:exp): bool :=
  isval e ||
    match e with
      | EId _  => true
      | _      => false
    end.

Fixpoint remove (id:identifier) (l:list identifier): list identifier :=
  match l with
  | nil => nil
  | cons x l' =>
      if id_eqb x id then
        remove id l'
      else
        cons x (remove id l')
  end.

Fixpoint free (e:exp): list identifier :=
  match e with
  | EId x         => cons x $ nil
  
  | EApp e1 e2    => List.app (free e1) (free e2)
  | EAbs x e'     => remove x (free e')
  | EFix x e'     => remove x (free e')
  
  | ENat _        => nil
  | EBool _       => nil
  
  | EAdd e1 e2    => List.app (free e1) (free e2)
  | ESub e1 e2    => List.app (free e1) (free e2)
  | EMul e1 e2    => List.app (free e1) (free e2)
  | EDiv e1 e2    => List.app (free e1) (free e2)
  
  | EEq e1 e2     => List.app (free e1) (free e2)
  | ELt e1 e2     => List.app (free e1) (free e2)
  | ENot e'       => free e'
  | EAnd e1 e2    => List.app (free e1) (free e2)
  
  | ESkip         => nil
  | ESeq e1 e2    => List.app (free e1) (free e2)
  | EAss x e'     => List.app (cons x $ nil) (free e')
  | EWhile e1 e2  => List.app (free e1) (free e2)
  | EIte e1 e2 e3 => List.app (List.app (free e1) (free e2)) (free e3)
  
  | EHole         => nil
  end.

Fixpoint elem (id:identifier) (l:list identifier): bool :=
  match l with
  | nil       => false
  | cons x l' => orb (id_eqb id x) (elem id l')
  end.

Fixpoint freshAux (avoid:list identifier) (startIndex:nat) (fuel:nat): identifier :=
  match fuel with
  | O       => Identifier startIndex
  | S fuel' =>
      if elem (Identifier startIndex) avoid then
        freshAux avoid (startIndex + 1) fuel'
      else
        Identifier startIndex
  end.

Definition fresh (avoid:list identifier) :=
  freshAux avoid 0 1000.

(* Substitute x with e' in e. *)
Fixpoint casubst (x:identifier) (e' e:exp) (avoid:list identifier) (fuel:nat): option exp :=
  match fuel with
  | O => None
  | S fuel' =>
      if (isval' e') then
        match e with
        | EId x'        => Some $ 
            if (id_eqb x x') then e' else EId x'
        
        | EApp e1 e2    =>
            EApp <$> casubst x e' e1 avoid fuel' <*> casubst x e' e2 avoid fuel'
        
        | EAbs x' e''   =>
            if (id_eqb x x') then
              Some $ EAbs x' e''
            else if elem x' (free e') then
              let x''            := fresh avoid in 
              let optReplacedAbs := casubst x' x'' e'' (cons x'' avoid) fuel'
              in  EAbs x'' <$> (optReplacedAbs >>= fun replacedAbs => casubst x e' replacedAbs avoid fuel')
            else
              EAbs x' <$> casubst x e' e'' (cons x' avoid) fuel'
        
        | EFix x' e''   =>
            if (id_eqb x x') then
              Some $ EFix x' e''
            else if elem x' (free e') then
              let x'' := fresh avoid in
              let optReplacedAbs := casubst x' x'' e'' (cons x'' avoid) fuel'
              in  EFix x'' <$> (optReplacedAbs >>= fun replacedAbs => casubst x e' replacedAbs avoid fuel')
            else
              EFix x' <$> casubst x e' e'' (cons x' avoid) fuel'
        
        | ENat i        =>
            Some $ ENat i
        | EBool b       =>
            Some $ EBool b
        
        | EAdd e1 e2    =>
            EAdd <$> casubst x e' e1 avoid fuel' <*> casubst x e' e2 avoid fuel'
        | ESub e1 e2    =>
            ESub <$> casubst x e' e1 avoid fuel' <*> casubst x e' e2 avoid fuel'
        | EMul e1 e2    =>
            EMul <$> casubst x e' e1 avoid fuel' <*> casubst x e' e2 avoid fuel'
        | EDiv e1 e2    =>
            EDiv <$> casubst x e' e1 avoid fuel' <*> casubst x e' e2 avoid fuel'
        
        | EEq e1 e2     =>
            EEq  <$> casubst x e' e1  avoid fuel' <*> casubst x e' e2 avoid fuel'
        | ELt e1 e2     =>
            ELt  <$> casubst x e' e1  avoid fuel' <*> casubst x e' e2 avoid fuel'
        | ENot e''      =>
            ENot <$> casubst x e' e'' avoid fuel'
        | EAnd e1 e2    =>
            EAnd <$> casubst x e' e1  avoid fuel' <*> casubst x e' e2 avoid fuel'
        
        | ESkip         =>
            Some ESkip
        | ESeq e1 e2    =>
            ESeq <$> casubst x e' e1 avoid fuel' <*> casubst x e' e2 avoid fuel'
        | EAss x' e''   =>
            match e' with
            | EId x'' =>
                if (id_eqb x x') then
                  EAss x'' <$> casubst x e' e'' avoid fuel'
                else EAss x' <$> casubst x e' e'' avoid fuel'
            | _       => EAss x' <$> casubst x e' e'' avoid fuel'
            end
        | EWhile e1 e2  => 
            EWhile <$> casubst x e' e1 avoid fuel' <*> casubst x e' e2 avoid fuel'
        | EIte e1 e2 e3 => 
            EIte <$> casubst x e' e1 avoid fuel' <*> casubst x e' e2 avoid fuel' <*> casubst x e' e3 avoid fuel'
        
        | EHole         => 
            Some EHole
        end
      else None
  end.

Definition casubst_default_fuel:nat := 1000.

Definition runStep (config:cfg): option cfg :=
  match config with
  | [EmptyStack | env] => None

  | [SKIP ~> s | env]  => Some $ [s | env]

    (* Assignments *)
  | [x ::= e ~> s | env] =>
      if (isval e) then
        match e with
        | ENat i => Some $ [s | x |-> i IN env]
        | _      => Some $ [s | env]
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
  | [EAbs x e ~> EHole;e2 ~> s | env] =>
      Some $ [(EAbs x e);e2 ~> s | env]

  (* Function application. *)
  | [EApp e1 e2 ~> s | env] =>
      if (negb $ isval e1) then
        Some $ [e1 ~> EApp EHole e2 ~> s | env]
      else if (negb $ isval e2) then
        Some $ [e2 ~> EApp e1 EHole ~> s | env]
      else
        match e1 with
        | EAbs x e           =>
            flip Cfg env <$> (flip Stack s <$> casubst x e2 e nil casubst_default_fuel)
        | EFix x (EAbs x' e) =>
            match (casubst x' e2 e nil casubst_default_fuel) with
            | Some res =>
                flip Cfg env <$> (flip Stack s <$> casubst x (EFix x $ EAbs x' e) res nil casubst_default_fuel)
            | _        => None
            end
        | _                  => None
        end
  | [ENat i1 ~> EApp EHole e2 ~> s | env] =>
      Some $ [EApp (ENat i1) e2 ~> s | env]
  | [EBool b1 ~> EApp EHole e2 ~> s | env] =>
      Some $ [EApp (EBool b1) e2 ~> s | env]
  | [EAbs x e ~> EApp EHole e2 ~> s | env] =>
      Some $ [EApp (EAbs x e) e2 ~> s | env]
  | [EFix x e1 ~> EApp EHole e2 ~> s | env] =>
      Some $ [EApp (EFix x e1) e2 ~> s | env]
  | [ENat i2 ~> EApp e1 EHole ~> s | env] =>
      Some $ [EApp e1 (ENat i2) ~> s | env]
  | [EBool b2 ~> EApp e1 EHole ~> s | env] =>
      Some $ [EApp e1 (EBool b2) ~> s | env]
  | [EAbs x' e2 ~> EApp e1 EHole ~> s | env] =>
      Some $ [EApp e1 (EAbs x' e2) ~> s | env]
  | [EFix x' e2 ~> EApp e1 EHole ~> s | env] =>
      Some $ [EApp e1 (EFix x' e2) ~> s | env]

  | [EFix x e ~> s | env] =>
      flip Cfg env <$> (flip Stack s <$> casubst x (EFix x e) e nil casubst_default_fuel)

  
  | [EHole ~> s | env] => Some $ [s | env]
  | cfg => None
  end.

Fixpoint runNSteps (n:nat) (config:cfg): option cfg :=
  match n with
  | O       => ret config
  | S n' => runStep config >>=
      fun config' => runNSteps n' config'
  end.

Definition lookUpEnvOfOptCfg (k:identifier) (config:option cfg): option nat :=
  config >>= 
    fun config => ret $ getEnvOfCfg config k.

(* spassBeispiel, spassBeispiel' and spassBeispiel'' are
  ground program configurations, because A, B and C are identifiers,
  not program variables, like we see in spassBeispiel'''. *)
Example spassBeispiel :=
  [A ::= 10 ~> EmptyStack | map_id_nat_empty].
Compute lookUpEnvOfOptCfg A $ runNSteps 100 spassBeispiel.

Example spassBeispiel' :=
  [A ::= 0; 
   WHILE A<?10 DO 
     A ::= A + A + 1
   END 
   ~> EmptyStack | map_id_nat_empty].
Compute lookUpEnvOfOptCfg A $ runNSteps 1000 spassBeispiel'.

Example spassBeispiel'' :=
  [A ::= 10;
   B ::= A * 10; (* 100 *)
   C ::= B * 10; (* 1000 *)

   WHILE (A <? B & A <? C) DO (* 10 < 100 /\ 10 < 1000 *)
    A ::= A + 1
   END
  ~> EmptyStack | map_id_nat_empty].
Compute lookUpEnvOfOptCfg A $ runNSteps 10000 spassBeispiel''.
Compute lookUpEnvOfOptCfg B $ runNSteps 10000 spassBeispiel''.
Compute lookUpEnvOfOptCfg C $ runNSteps 10000 spassBeispiel''.

Fixpoint runNStepsAndGetPath (n:nat) (config:cfg): option (list cfg) :=
  match n with
  | O       => ret $ cons config $ nil
  | S n' => runStep config >>=
      fun config' => runNStepsAndGetPath n' config' >>=
        fun path => ret $ cons config' path
  end.

(* A symbolic program configuration (since x is a variable). *)
Example spassBeispiel''' (x:nat) :=
  [A ::= x ~> EmptyStack | map_id_nat_empty].
Compute lookUpEnvOfOptCfg A $ runNSteps 100 $ spassBeispiel''' 20.
