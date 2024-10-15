(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(* Test le Hint Unfold sur des var locales *)

Section toto.
Let EQ := @eq.
Goal EQ nat 0 0.
Hint Unfold EQ.
auto.
Qed.
End toto.

(* Check regular failure when statically existing ref does not exist
   any longer at run time *)

Goal let x := 0 in True.
intro x.
Fail (clear x; unfold x).
Abort.

(* Static analysis of unfold *)

Module A.

Opaque id.
Ltac f := unfold id.
Goal id 0 = 0.
Fail f.
Transparent id.
f.
Abort.

End A.

Module B.

Module Type T. Axiom n : nat. End T.

Module F(X:T).
Ltac f := unfold X.n.
End F.

Module M. Definition n := 0. End M.
Module N := F M.
Goal match M.n with 0 => 0 | S _ => 1 end = 0.
N.f.
match goal with |- 0=0 => idtac end.
Abort.

End B.

Module C.

(* We reject inductive types and constructors *)

Fail Ltac g := unfold nat.
Fail Ltac g := unfold S.

End C.

Module D.

(* In interactive mode, we delay the interpretation of short names *)

Notation x := Nat.add.

Goal let x := 0 in x = 0+0.
unfold x.
match goal with |- 0 = 0 => idtac end.
Abort.

Goal let x := 0 in x = 0+0.
intro; unfold x. (* dynamic binding (but is it really the most natural?) *)
match goal with |- 0 = 0+0 => idtac end.
Abort.

Goal let fst := 0 in fst = Datatypes.fst (0,0).
unfold fst.
match goal with |- 0 = 0 => idtac end.
Abort.

Goal let fst := 0 in fst = Datatypes.fst (0,0).
intro; unfold fst. (* dynamic binding *)
match goal with |- 0 = Datatypes.fst (0,0) => idtac end.
Abort.

End D.
