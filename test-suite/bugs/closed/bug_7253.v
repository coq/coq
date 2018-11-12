
Inductive foo (A : Set) (a : A) : Set := sup : foo _ 3 -> foo _ a.

(* Used to fail *)
Inductive foo' {A : Set} (a : A) : Set := sup' : foo' 3 -> foo' a.

Inductive I' {A} : A -> Type := C' a : I' a.
Inductive I {A} : A -> Type := C a : @I _ a. (* Used to fail *)

Inductive I1 := C1 : _.
Inductive I2 := C2 : id I2.
Inductive I3 := C3 : id _. (* Used to fail *)

Section extra_universes.
Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Inductive A : Set := X | Y.
Check A@{}.
End extra_universes.

Axiom list : Type -> Type.
Axiom inj : forall T, T -> list T.
Section unification_failure.
Inductive exp_match T : list T -> list _ -> Type :=
| MChar : forall x : _, exp_match _ (inj _ x) (inj _ x)
.
End unification_failure.

Section bad_type.
Local Set Uniform Inductive Parameters.
Inductive exp_match2 T : list T -> list T -> Type :=
| MChar2 : forall x : T, exp_match2 (inj T x) (inj T x)
.
End bad_type.
