Require Import Axioms.
Require Import Plus.
Require Import Times.

(* Here we allow dependent recursion only for domains with Libniz
equality. The reason is that, if the domain is A : nat -> Set, then (A
n) must coincide with (A n') whenever n == n'. However, it is possible
to try to use arbitrary domain and require that n == n' -> A n = A n'. *)

Module Type DepRecSignature.
Declare Module DomainModule : DomainEqSignature.
Declare Module Export NatModule : NatSignature with
  Module DomainModule := DomainModule.
(* Instead of these two lines, I would like to say
Declare Module Export Nat : NatSignature with Module Domain : NatDomainEq. *)

Parameter dep_recursion :
  forall A : N -> Set, A 0 -> (forall n, A n -> A (S n)) -> forall n, A n.

Axiom dep_recursion_0 :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)),
    dep_recursion A a f 0 = a.

Axiom dep_recursion_S :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)) (n : N),
    dep_recursion A a f (S n) = f n (dep_recursion A a f n).

End DepRecSignature.

Module DepRecTimesProperties (Export DepRecModule : DepRecSignature)
                             (Export TimesModule : TimesSignature
                                with Module PlusModule.NatModule := DepRecModule.NatModule).

Module Export TimesPropertiesModule := TimesProperties TimesModule.

Theorem not_0_implies_S_dep : forall n, n # O -> {m : N | n == S m}.
Proof.
intro n; pattern n; apply dep_recursion; clear n;
[intro H; now elim H | intros n _ _; now exists n].
Qed.

Theorem plus_eq_1_dep :
  forall m n : N, m + n == 1 -> {m == 0 /\ n == 1} + {m == 1 /\ n == 0}.
(* Why do we write == here instead of just = ? "x == y" is a notation
for (E x y) declared in NatDomainEq signature. In this case, E is
Plus.Nat.Domain.E. If we want to rewrite, e.g., plus_comm, which
contains E, in a formula with =, setoid rewrite signals an error,
because E is not declared a morphism w.r.t. = even though E is defined
to be =. Thus, we need to use E instead of = in our formulas. *)
Proof.
intros m n; pattern m; apply dep_recursion; clear m.
intro H.
rewrite plus_0_n in H. left; now split.
intros m IH H. rewrite plus_Sn_m in H. apply S_inj in H.
apply plus_eq_0 in H. destruct H as [H1 H2].
right; now split; [rewrite H1 |].
Qed.

Theorem times_eq_0_dep :
  forall n m, n * m == 0 -> {n == 0} + {m == 0}.
Proof.
intros n m; pattern n; apply dep_recursion; pattern m; apply dep_recursion;
clear n m.
intros; left; reflexivity.
intros; left; reflexivity.
intros; right; reflexivity.
intros n _ m _ H.
rewrite times_Sn_m in H; rewrite plus_Sn_m in H; now apply S_0 in H.
Qed.

End DepRecTimesProperties.
