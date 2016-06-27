(** The purpose of this file is to test functional properties of the
    destructive patterns used in binders ([fun] and [forall]). *)


Definition swap {A B} '((x,y) : A*B) := (y,x).

(** Tests the use of patterns in [fun] and [Definition] *)
Section TestFun.

  Variables A B : Type.

  Goal forall (x:A) (y:B), swap (x,y) = (y,x).
  Proof. reflexivity. Qed.

  Goal forall u:A*B, swap (swap u) = u.
  Proof. destruct u. reflexivity. Qed.

  Goal @swap A B = fun '(x,y) => (y,x).
  Proof. reflexivity. Qed.

End TestFun.


(** Tests the use of patterns in [forall] *)
Section TestForall.

  Variables A B : Type.

  Goal forall '((x,y) : A*B), swap (x,y) = (y,x).
  Proof. intros [x y]. reflexivity. Qed.

  Goal forall x0:A, exists '((x,y) : A*A), swap (x,y) = (x,y).
  Proof.
    intros x0.
    exists (x0,x0).
    reflexivity.
  Qed.

End TestForall.



(** Tests the use of patterns in dependent definitions. *)

Section TestDependent.

  Inductive Fin (n:nat) := Z : Fin n.

  Definition F '(n,p) : Type := (Fin n * Fin p)%type.

  Definition both_z '(n,p) : F (n,p) := (Z _,Z _).

End TestDependent.


(** Tests with a few other types just to make sure parsing is
    robust. *)
Section TestExtra.

  Definition proj_informative {A P} '(exist _ x _ : { x:A | P x }) : A := x.

  Inductive Foo := Bar : nat -> bool -> unit -> nat -> Foo.

  Definition foo '(Bar n b tt p) :=
    if b then n+p else n-p.

End TestExtra.
