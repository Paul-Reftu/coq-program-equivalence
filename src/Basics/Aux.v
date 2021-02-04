(* External import(s). *)
Require Import Coq.ZArith.BinIntDef.

Definition funApp {A B: Type} (f: A -> B) (x: A): B := f x.
Infix "$" := funApp (at level 100, right associativity).

Definition flip {A B C: Type} (f: A -> B -> C) (y:B) (x:A): C := f x y.
Compute flip Nat.sub 10 20.

(* Functor option. *)
Definition fmap {A B} (f:A -> B) (a:option A): option B :=
  match a with
  | Some a' => Some $ f a'
  | _       => None
  end.
Infix "<$>" := fmap (at level 90, left associativity).

(* Applicative option. *)
Definition app {A B} (f:option (A -> B)) (a:option A): option B :=
  match f with
  | Some f' => fmap f' a
  | _       => None
  end.
Infix "<*>" := app (at level 90, left associativity).

(* Monad option. *)
Definition bind {A B} (m: option A) (a: A -> option B): option B :=
  match m with
  | Some m' => a m'
  | _       => None
  end.
Infix ">>=" := bind (at level 90, left associativity).

(* `return` is a reserved keyword in Coq - hence, we use `ret` instead. *)
Definition ret {A} (a:A): option A :=
  Some a.

Open Scope Z.
Example fmapExample :=
  Z.add 10 <$> Some 10.
Compute fmapExample.

Example appExample :=
  Some (Z.add 5) <*> Some 5.
Compute appExample.

Example bindExample :=
  Some 5 >>= (fun x => Some $ Z.add x 10).
Compute bindExample.
