Require Import Ltac2.Ltac2 Ltac2.Notations.

Ltac2 mutable foo () := constructor.

Goal True.
Proof.
foo ().
Qed.

Ltac2 Set foo := fun _ => fail.

Goal True.
Proof.
Fail foo ().
constructor.
Qed.


(** Bindings are dynamic *)

Ltac2 Type rec nat := [O | S (nat)].

Ltac2 rec nat_eq n m :=
  match n with
  | O => match m with | O => true | S _ => false end
  | S n => match m with | O => false | S m => nat_eq n m end
  end.

Ltac2 assert_eq n m :=
  match nat_eq n m with
  | true => ()
  | false => Control.throw Assertion_failure end.

Ltac2 mutable x := O.
Ltac2 y () := x.
Ltac2 Eval (assert_eq (y()) O).
Ltac2 Set x := (S O).
Ltac2 Eval (assert_eq (y()) (S O)).

Ltac2 mutable quw := fun (n : nat) => O.
Ltac2 Set quw := fun n =>
  match n with
  | O => O
  | S n => S (S (quw n))
  end.

Ltac2 Eval (quw (S (S O))).

(** Not the right type *)
Fail Ltac2 Set foo := 0.

Ltac2 bar () := ().

(** Cannot redefine non-mutable tactics *)
Fail Ltac2 Set bar := fun _ => ().

(** Subtype check *)

Ltac2 rec h x := h x.

Ltac2 mutable f x := h x.
Fail Ltac2 Set f := fun x => x.

Ltac2 mutable g x := x.
Ltac2 Set g := h.

(** Rebinding with old values *)



Ltac2 mutable qux n := S n.

Ltac2 Set qux as self := fun n => self (self n).

Ltac2 Eval assert_eq (qux O) (S (S O)).

Ltac2 mutable quz := O.

Ltac2 Set quz as self := S self.

Ltac2 Eval (assert_eq quz (S O)).

Ltac2 rec addn n :=
  match n with
  | O => fun m => m
  | S n => fun m => S (addn n m)

  end.
Ltac2 mutable rec quy n :=
  match n with
  | O => S O
  | S n => S (quy n)
  end.

Ltac2 Set quy as self := fun n =>
                           match n with
                           | O => O
                           | S n => addn (self n) (quy n)
                           end.
Ltac2 Eval (assert_eq (quy (S (S O))) (S (S (S O)))).
Ltac2 Eval (assert_eq (quy (S (S (S O)))) (S (S (S (S (S (S O))))))).
