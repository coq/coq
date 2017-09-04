Require Import Ltac2.Ltac2.

Import Ltac2.Notations.

(** Test calls to Ltac1 from Ltac2 *)

Ltac2 foo () := ltac1:(discriminate).

Goal true = false -> False.
Proof.
foo ().
Qed.

Goal true = false -> false = true.
Proof.
intros H; ltac1:(match goal with [ H : ?P |- _ ] => rewrite H end); reflexivity.
Qed.

Goal true = false -> false = true.
Proof.
intros H; ltac1:(rewrite H); reflexivity.
Abort.

(** Variables do not cross the compatibility layer boundary. *)
Fail Ltac2 bar nay := ltac1:(discriminate nay).

Fail Ltac2 pose1 (v : constr) :=
  ltac1:(pose $v).

(** Test calls to Ltac2 from Ltac1 *)

Set Default Proof Mode "Classic".

Ltac foo := ltac2:(foo ()).

Goal true = false -> False.
Proof.
ltac2:(foo ()).
Qed.

Goal true = false -> False.
Proof.
foo.
Qed.

(** Variables do not cross the compatibility layer boundary. *)
Fail Ltac bar x := ltac2:(foo x).

Ltac mytac tac := idtac "wow".

Goal True.
Proof.
(** Fails because quotation is evaluated eagerly *)
Fail mytac ltac2:(fail).
(** One has to thunk thanks to the idtac trick *)
let t := idtac; ltac2:(fail) in mytac t.
constructor.
Qed.
