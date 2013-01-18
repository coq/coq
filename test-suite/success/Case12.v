(* This example was proposed by Cuihtlauac ALVARADO *)

Require Import List.

Fixpoint mult2 (n : nat) : nat :=
  match n with
  | O => 0
  | S n => S (S (mult2 n))
  end.

Inductive list : nat -> Set :=
  | nil : list 0
  | cons : forall n : nat, list (mult2 n) -> list (S (S (mult2 n))).

Type
  (fun (P : forall n : nat, list n -> Prop) (f : P 0 nil)
     (f0 : forall (n : nat) (l : list (mult2 n)),
           P (mult2 n) l -> P (S (S (mult2 n))) (cons n l)) =>
   fix F (n : nat) (l : list n) {struct l} : P n l :=
     match l as x0 in (list x) return (P x x0) with
     | nil => f
     | cons n0 l0 => f0 n0 l0 (F (mult2 n0) l0)
     end).

Inductive list' : nat -> Set :=
  | nil' : list' 0
  | cons' : forall n : nat, let m := mult2 n in list' m -> list' (S (S m)).

Fixpoint length n (l : list' n) {struct l} : nat :=
  match l with
  | nil' => 0
  | cons' _ m l0 => S (length m l0)
  end.

Type
  (fun (P : forall n : nat, list' n -> Prop) (f : P 0 nil')
     (f0 : forall n : nat,
           let m := mult2 n in
           forall l : list' m, P m l -> P (S (S m)) (cons' n l)) =>
   fix F (n : nat) (l : list' n) {struct l} : P n l :=
     match l as x0 in (list' x) return (P x x0) with
     | nil' => f
     | cons' n0 m l0 => f0 n0 l0 (F m l0)
     end).

(* Check on-the-fly insertion of let-in patterns for compatibility *)

Inductive list'' : nat -> Set :=
  | nil'' : list'' 0
  | cons'' :
      forall n : nat,
      let m := mult2 n in list'' m -> let p := S (S m) in list'' p.

Check
  (fix length n (l : list'' n) {struct l} : nat :=
     match l with
     | nil'' => 0
     | cons'' n l0 => S (length (mult2 n) l0)
     end).

(* Check let-in in both parameters and in constructors *)

Inductive list''' (A:Set) (B:=(A*A)%type) (a:A) : B -> Set :=
  | nil''' : list''' A a (a,a)
  | cons''' :
     forall a' : A, let m := (a',a) in list''' A a m -> list''' A a (a,a).

Fixpoint length''' (A:Set) (B:=(A*A)%type) (a:A) (m:B) (l:list''' A a m)
  {struct l} : nat :=
  match l with
  | nil''' _ _ => 0
  | @cons''' _ _ _ _ m l0 => S (length''' A a m l0)
  end.
