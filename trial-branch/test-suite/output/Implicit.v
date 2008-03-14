Set Implicit Arguments.
Unset Strict Implicit.

(* Suggested by Pierre Casteran (bug #169) *)
(* Argument 3 is needed to typecheck and should be printed *)
Definition compose (A B C : Set) (f : A -> B) (g : B -> C) (x : A) := g (f x).
Check (compose (C:=nat) S).

(* Better to explicitly display the arguments inferable from a
   position that could disappear after reduction *)
Inductive ex (A : Set) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P.
Check (ex_intro (P:=fun _ => True) (x:=0) I).

(* Test for V8 printing of implicit by names *)
Definition d1 y x (h : x = y :>nat) := h.
Definition d2 x := d1 (y:=x).

Print d2.

(* Check maximal insertion of implicit *)

Require Import List.

Open Scope list_scope.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Definition id (A:Type) (x:A) := x.

Check map id (1::nil).

Definition id' (A:Type) (x:A) := x.

Implicit Arguments id' [[A]].

Check map id' (1::nil).
