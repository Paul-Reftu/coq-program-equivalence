Require Import Basics.Aux.
Require Import Basics.Identifier.
Require Import Languages.LC.Syntax.
Require Import Languages.LC.Semantics.

(* Variables. *)
Definition A := Identifier 0.
Definition B := Identifier 1.

Definition F := Identifier 2.
Definition G := Identifier 3.
Definition H := Identifier 4.

Definition M := Identifier 5.
Definition N := Identifier 6.

Definition P := Identifier 7.
Definition Q := Identifier 8.

Definition T := Identifier 9.
Definition U := Identifier 10.

Definition X := Identifier 11.
Definition Y := Identifier 12.
Definition Z := Identifier 13.


(* Church numerals. *)
Fixpoint natToChurch_aux (n:nat): exp :=
  match n with
  | O    => X
  | S n' => EApp F $ natToChurch_aux n'
  end.
Definition natToChurch (n:nat) :=
  EAbs F $ EAbs X $ natToChurch_aux n.

Definition zero  := natToChurch 0.
Definition one   := natToChurch 1.
Definition two   := natToChurch 2.
Definition three := natToChurch 3.


(* Church numeral arithmetic. *)
Definition add := EAbs M $ EAbs N $ EAbs F $ EAbs X $
  EApp (EApp M F) $ EApp (EApp N F) X.
Definition add' (m n:exp) :=
  EApp (EApp add m) n.

Definition succ := EAbs N $ EAbs F $ EAbs X $
  EApp F $ EApp (EApp N F) X.
Definition succ' (n:exp) :=
  EApp succ n.

Definition pred := EAbs N $ EAbs F $ EAbs X $
  EApp
    (EApp
      (EApp N $ EAbs G $ EAbs H $ EApp H (EApp G F))
      (EAbs U X))
    (EAbs U U).
Definition pred' (n:exp) :=
  EApp pred n.

Definition sub := EAbs M $ EAbs N $
  EApp (EApp N pred) M.
Definition sub' (m n:exp) :=
  EApp (EApp sub m) n.


(* Church predicates. *)
Definition true  := EAbs A $ EAbs B A.
Definition false := EAbs A $ EAbs B B.

Definition and := EAbs P $ EAbs Q $
  EApp (EApp P Q) P.
Definition and' (p q:exp) :=
  EApp (EApp and p) q.

Definition isZero := EAbs N $
  EApp (EApp N $ EAbs X false) true.
Definition isZero' (n:exp) :=
  EApp isZero n.

Definition leq := EAbs M $ EAbs N $
  isZero' $ sub' M N.
Definition leq' (m n:exp) :=
  EApp (EApp leq m) n.

Definition eq := EAbs M $ EAbs N $
  and' (leq' M N) (leq' N M).
Definition eq' (m n:exp) :=
  EApp (EApp eq m) n.

Definition ite := EAbs P $ EAbs A $ EAbs B $
  EApp (EApp P A) B.
Definition ite' (p a b:exp) :=
  EApp (EApp (EApp ite p) a) b.


(* Church pairs. *)
Definition pair := EAbs X $ EAbs Y $ EAbs Z $
  EApp (EApp Z X) Y.
Definition pair' (x y: exp) :=
  EApp (EApp pair x) y.

Definition fst := EAbs P $
  EApp P (EAbs X $ EAbs Y X).
Definition fst' (p:exp) :=
  EApp fst p.

Definition snd := EAbs P $
  EApp P (EAbs X $ EAbs Y Y).
Definition snd' (p:exp) :=
  EApp snd p.


(* Church lists. *)
Definition nil :=
  pair' true true.

Definition isNil :=
  fst.

Definition cons := EAbs H $ EAbs T $ 
  pair' false (pair' H T).
Definition cons' (h t:exp) :=
  EApp (EApp cons h) t.

Definition head := EAbs Z $
  fst' (snd' Z).
Definition head' (z:exp) :=
  EApp head z.

Definition tail := EAbs Z $
  snd' (snd' Z).
Definition tail' (z:exp) :=
  EApp tail z.

(* Auxiliary Church functions. *)
Definition listFromNToM_aux := EAbs F $ EAbs N $ EAbs M $
  ite' (leq' N M)
    (cons' N $ EApp (EApp F $ succ' N) M)
     nil.
Definition listFromNToM :=
  EApp listFromNToM_aux listFromNToM_aux.
Definition listFromNToM' (n m:exp) :=
  EApp (EApp listFromNToM n) m.

Definition sumFromNToM_aux := EAbs F $ EAbs N $ EAbs M $
  ite' (leq' N M)
    (add' N $ EApp (EApp F $ succ' N) M)
     zero.
Definition sumFromNToM :=
  EApp sumFromNToM_aux sumFromNToM_aux.
Definition sumFromNToM' (n m:exp) :=
  EApp (EApp sumFromNToM n) m.
