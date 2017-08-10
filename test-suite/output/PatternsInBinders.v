Require Coq.Unicode.Utf8.

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

Module WithParameters.

Definition swap {A B} '((x,y) : A*B) := (y,x).
Print swap.

Check fun (A B:Type) '((x,y) : A*B) => swap (x,y) = (y,x).
Check forall (A B:Type) '((x,y) : A*B), swap (x,y) = (y,x).

Check exists '((x,y):A*A), swap (x,y) = (y,x).
Check exists '((x,y):A*A) '(z,w), swap (x,y) = (z,w).

End WithParameters.

(** Some test involving unicode notations. *)
Module WithUnicode.

  Import Coq.Unicode.Utf8.

  Check λ '((x,y) : A*B),  (y,x).
  Check ∀ '(x,y), swap (x,y) = (y,x).

End WithUnicode.

(** * Suboptimal printing *)

Module Suboptimal.

(** This test shows an example which exposes the [let] introduced by
    the pattern notation in binders. *)

Inductive Fin (n:nat) := Z : Fin n.
Definition F '(n,p) : Type := (Fin n * Fin p)%type.
Definition both_z '(n,p) : F (n,p) := (Z _,Z _).
Print both_z.

(** Test factorization of binders *)

Check fun '((x,y) : A*B) '(z,t) => swap (x,y) = (z,t).
Check forall '(x,y) '((z,t) : B*A), swap (x,y) = (z,t).

End Suboptimal.

(** Test risk of collision for internal name *)
Check fun pat => fun '(x,y) => x+y = pat.

(** Test name in degenerate case *)
Definition f 'x := x+x.
Print f.
Check fun 'x => x+x.
