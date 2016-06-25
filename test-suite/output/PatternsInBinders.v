(** The purpose of this file is to test printing of the destructive
    patterns used in binders ([fun] and [forall]). *)

Parameters (A B : Type) (P:A->Prop).

Definition swap '((x,y) : A*B) := (y,x).
Print swap.

Check fun '((x,y) : A*B) => (y,x).

Check forall '(x,y), swap (x,y) = (y,x).

Definition proj_informative '(exist _ x _ : { x:A | P x }) : A := x.
Print proj_informative.

Inductive Foo := Bar : nat -> bool -> unit -> nat -> Foo.
Definition foo '(Bar n b tt p) :=
  if b then n+p else n-p.
Print foo.

Definition baz '(Bar n1 b1 tt p1) '(Bar n2 b2 tt p2) := n1+p1.
Print baz.

(** Some test involving unicode noations. *)
Module WithUnicode.

  Require Import Coq.Unicode.Utf8.

  Check λ '((x,y) : A*B),  (y,x).
  Check ∀ '(x,y), swap (x,y) = (y,x).

End WithUnicode.


(** * Suboptimal printing *)

(** These tests show examples which expose the [let] introduced by
    the pattern notation in binders. *)

Module Suboptimal.

Definition swap {A B} '((x,y) : A*B) := (y,x).
Print swap.

Check forall (A B:Type) '((x,y) : A*B), swap (x,y) = (y,x).

Check exists '((x,y):A*A), swap (x,y) = (y,x).

Inductive Fin (n:nat) := Z : Fin n.
Definition F '(n,p) : Type := (Fin n * Fin p)%type.
Definition both_z '(n,p) : F (n,p) := (Z _,Z _).
Print both_z.

End Suboptimal.
