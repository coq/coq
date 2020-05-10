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

(** Not the right type *)
Fail Ltac2 Set foo := 0.

Ltac2 bar () := ().

(** Cannot redefine non-mutable tactics *)
Fail Ltac2 Set bar := fun _ => ().

(** Subtype check *)

Ltac2 mutable rec f x := f x.

Fail Ltac2 Set f := fun x => x.

Ltac2 mutable g x := x.

Ltac2 Set g := f.

(* Rebinding with old values *)

Ltac2 Type rec nat := [O | S (nat)].

Ltac2 rec nat_eq n m :=
  match n with
  | O => match m with | O => true | S _ => false end
  | S n => match m with | O => false | S m => nat_eq n m end
  end.

Ltac2 Type exn ::= [ Assertion_failed ].

Ltac2 assert_eq n m :=
  match nat_eq n m with
  | true => ()
  | false => Control.throw Assertion_failed end.


Ltac2 mutable qux n := S n.

Ltac2 Set qux as self := fun n => self (self n).

Ltac2 Eval assert_eq (qux O) (S (S O)).


Ltac2 mutable quz := O.

Ltac2 Set quz as self := S self.

Ltac2 Eval (assert_eq quz (S O)).
