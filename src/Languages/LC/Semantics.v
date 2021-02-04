(* External import(s). *)
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import         ListNotations.
(* Internal import(s). *)
Require Import Basics.Identifier.
Require Import Basics.Aux.
Require Import Languages.LC.Syntax.

Definition isval (e:exp): bool :=
  match e with
    | EAbs _ _  => true
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
        
        | EHole         => 
            Some EHole
        end
      else None
  end.

Definition casubst_default_fuel:nat := 1000.

Definition runStep (config:cfg): option cfg :=
  match config with
  | [EmptyStack | env] => None

  | [EApp e1 e2 ~> s | env]  =>
      if (negb $ isval e1) then
        Some $ [e1 ~> EApp EHole e2 ~> s | env]
      else if (negb $ isval e2) then
        Some $ [e2 ~> EApp e1 EHole ~> s | env]
      else
        match e1 with
        | EAbs x e           =>
            flip Cfg env <$> (flip Stack s <$> casubst x e2 e nil casubst_default_fuel)
        | _                  => None
        end
  | [EAbs x e ~> EApp EHole e2 ~> s | env] =>
      Some $ [EApp (EAbs x e) e2 ~> s | env]
  | [EAbs x' e2 ~> EApp e1 EHole ~> s | env] =>
      Some $ [EApp e1 (EAbs x' e2) ~> s | env]

  | [EHole ~> s | env] => Some $ [s | env]

  | _ => None
  end.

Fixpoint runNSteps (n:nat) (config:cfg): option cfg :=
  match n with
  | O    => ret config
  | S n' => runStep config >>=
      fun config' => runNSteps n' config'
  end.
