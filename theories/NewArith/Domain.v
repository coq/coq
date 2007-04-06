Require Export Prelude.

Module Type DomainSignature.

Parameter N : Set.
Parameter E : relation N.
Parameter e : N -> N -> bool.

(* Theoretically, we it is enough to have decidable equality e only.
If necessary, E could be defined using a coercion. However, after we
prove properties of natural numbers, we would like them to eventually
use ordinary Leibniz equality. E.g., we would like the commutativity
theorem, instantiated to nat, to say forall x y : nat, x + y = y + x,
and not forall x y : nat, eq_true (e (x + y) (y + x))

In fact, if we wanted to have decidable equality e only, we would have
some trouble doing rewriting. If there is a hypothesis H : e x y, this
means more precisely that H : eq_true (e x y). Such hypothesis is not
recognized as equality by setoid rewrite because it does not have the
form R x y where R is an identifier. *)

Axiom E_equiv_e : forall x y : N, E x y <-> e x y.
Axiom E_equiv : equiv N E.

Add Relation N E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

Notation "x == y" := (E x y) (at level 70).
Notation "x # y" := (~ E x y) (at level 70).

End DomainSignature.

(* Now we give DomainSignature, but with E being Leibniz equality. If
an implementation uses this signature, then more facts may be proved
about it. *)
Module Type DomainEqSignature.

Parameter N : Set.
Definition E := (@eq N).
Parameter e : N -> N -> bool.

Axiom E_equiv_e : forall x y : N, E x y <-> e x y.
Definition E_equiv : equiv N E := eq_equiv N.

Add Relation N E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

Notation "x == y" := (E x y) (at level 70).
Notation "x # y" := ((E x y) -> False) (at level 70).
(* Why do we need a new notation for Leibniz equality? See DepRec.v *)

End DomainEqSignature.

Module DomainProperties (Export DomainModule : DomainSignature).
(* It also accepts module of type NatDomainEq *)

(* The following easily follows from transitivity of e and E, but
we need to deal with the coercion *)
Add Morphism e with signature E ==> E ==> eq_bool as e_wd.
Proof.
intros x x' Exx' y y' Eyy'.
case_eq (e x y); case_eq (e x' y'); intros H1 H2; trivial.
assert (x == y); [apply <- E_equiv_e; now rewrite H2 |
assert (x' == y'); [rewrite <- Exx'; now rewrite <- Eyy' |
rewrite <- H1; assert (H3 : e x' y'); [now apply -> E_equiv_e | now inversion H3]]].
assert (x' == y'); [apply <- E_equiv_e; now rewrite H1 |
assert (x == y); [rewrite Exx'; now rewrite Eyy' |
rewrite <- H2; assert (H3 : e x y); [now apply -> E_equiv_e | now inversion H3]]].
Qed.

End DomainProperties.
