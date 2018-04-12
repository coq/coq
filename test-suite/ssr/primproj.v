(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)



Require Import Setoid.
Set Primitive Projections.


Module CoqBug.
Record foo A := Foo { foo_car : A }.

Definition bar : foo _ := Foo nat 10.

Variable alias : forall A, foo A -> A.

Parameter e : @foo_car = alias.

Goal foo_car _ bar = alias _ bar.
Proof.
(* Coq equally fails *)
Fail rewrite -> e.
Fail rewrite e at 1.
Fail setoid_rewrite e.
Fail setoid_rewrite e at 1.
Set Keyed Unification.
Fail rewrite -> e.
Fail rewrite e at 1.
Fail setoid_rewrite e.
Fail setoid_rewrite e at 1.
Admitted.

End CoqBug.

(* ----------------------------------------------- *)
Require Import ssreflect.

Set Primitive Projections.

Module T1.

Record foo A := Foo { foo_car : A }.

Definition bar : foo _ := Foo nat 10.

Goal foo_car _ bar = 10.
Proof.
match goal with
| |- foo_car _ bar = 10 => idtac
end.
rewrite /foo_car.
(*
Fail match goal with
| |- foo_car _ bar = 10 => idtac
end.
*)
Admitted.

End T1.


Module T2.

Record foo {A} := Foo { foo_car : A }.

Definition bar : foo := Foo nat 10.

Goal foo_car bar = 10.
match goal with
| |- foo_car bar = 10 => idtac
end.
rewrite /foo_car.
(*
Fail match goal with
| |- foo_car bar = 10 => idtac
end.
*)
Admitted.

End T2.


Module T3.

Record foo {A} := Foo { foo_car : A }.

Definition bar : foo := Foo nat 10.

Goal foo_car bar = 10.
Proof.
rewrite -[foo_car _]/(id _).
match goal with |- id _ = 10 => idtac end.
Admitted.

Goal foo_car bar = 10.
Proof.
set x := foo_car _.
match goal with |- x = 10 => idtac end.
Admitted.

End T3.

Module T4.

Inductive seal {A} (f : A) := { unseal : A; seal_eq : unseal = f }.
Arguments unseal {_ _} _.
Arguments seal_eq {_ _} _.

Record uPred : Type := IProp { uPred_holds :> Prop }.

Definition uPred_or_def (P Q : uPred) : uPred :=
  {| uPred_holds := P \/ Q |}.
Definition uPred_or_aux : seal (@uPred_or_def). by eexists. Qed.
Definition uPred_or := unseal uPred_or_aux.
Definition uPred_or_eq: @uPred_or = @uPred_or_def := seal_eq uPred_or_aux.

Lemma foobar (P1 P2 Q : uPred) :
  (P1 <-> P2) -> (uPred_or P1 Q) <-> (uPred_or P2 Q).
Proof.
  rewrite uPred_or_eq. (* This fails. *)
Admitted.

End T4.


Module DesignFlaw.

Record foo A := Foo { foo_car : A }.
Definition bar : foo _ := Foo nat 10.

Definition app (f : foo nat -> nat) x := f x.

Goal app (foo_car _) bar = 10.
Proof.
unfold app.  (* mkApp should produce a Proj *)
Fail set x := (foo_car _ _).
Admitted.

End DesignFlaw.


Module Bug.

Record foo A := Foo { foo_car : A }.

Definition bar : foo _ := Foo nat 10.

Variable alias : forall A, foo A -> A.

Parameter e : @foo_car = alias.

Goal foo_car _ bar = alias _ bar.
Proof.
Fail rewrite e.  (* Issue: #86 *)
Admitted.

End Bug.
