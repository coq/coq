Require Export NumPrelude.
Require Import NZBase.

Module Type ZBaseSig.

Parameter Z : Set.
Parameter ZE : Z -> Z -> Prop.

Delimit Scope IntScope with Int.
Bind Scope IntScope with Z.
Open Local Scope IntScope.

Notation "x == y"  := (ZE x y) (at level 70) : IntScope.
Notation "x ~= y" := (~ ZE x y) (at level 70) : IntScope.

Axiom ZE_equiv : equiv Z ZE.

Add Relation Z ZE
 reflexivity proved by (proj1 ZE_equiv)
 symmetry proved by (proj2 (proj2 ZE_equiv))
 transitivity proved by (proj1 (proj2 ZE_equiv))
as ZE_rel.

Parameter Z0 : Z.
Parameter Zsucc : Z -> Z.

Add Morphism Zsucc with signature ZE ==> ZE as Zsucc_wd.

Notation "0" := Z0 : IntScope.
Notation "'S'" := Zsucc : IntScope.
Notation "1" := (S 0) : IntScope.
(* Note: if we put the line declaring 1 before the line declaring 'S' and
change (S 0) to (Zsucc 0), then 1 will be parsed but not printed ((S 0)
will be printed instead of 1) *)

Axiom Zsucc_inj : forall x y : Z, S x == S y -> x == y.

Axiom Zinduction :
  forall A : predicate Z, predicate_wd ZE A ->
    A 0 -> (forall x, A x <-> A (S x)) -> forall x, A x.

End ZBaseSig.

Module ZBasePropFunct (Import ZBaseMod : ZBaseSig).
Open Local Scope IntScope.

Module NZBaseMod <: NZBaseSig.

Definition NZ := Z.
Definition NZE := ZE.
Definition NZ0 := Z0.
Definition NZsucc := Zsucc.

(* Axioms *)
Definition NZE_equiv := ZE_equiv.

Add Relation NZ NZE
 reflexivity proved by (proj1 NZE_equiv)
 symmetry proved by (proj2 (proj2 NZE_equiv))
 transitivity proved by (proj1 (proj2 NZE_equiv))
as NZE_rel.

Add Morphism NZsucc with signature NZE ==> NZE as NZsucc_wd.
Proof Zsucc_wd.

Definition NZsucc_inj := Zsucc_inj.
Definition NZinduction := Zinduction.

End NZBaseMod.

Module Export NZBasePropMod := NZBasePropFunct NZBaseMod.

Theorem Zneq_symm : forall n m : Z, n ~= m -> m ~= n.
Proof NZneq_symm.

Theorem Zcentral_induction :
  forall A : Z -> Prop, predicate_wd ZE A ->
    forall z : Z, A z ->
      (forall n : Z, A n <-> A (S n)) ->
        forall n : Z, A n.
Proof NZcentral_induction.

Theorem Zsucc_inj_wd : forall n m, S n == S m <-> n == m.
Proof NZsucc_inj_wd.

Theorem Zsucc_inj_neg : forall n m, S n ~= S m <-> n ~= m.
Proof NZsucc_inj_wd_neg.

Tactic Notation "Zinduct" ident(n) :=
  induction_maker n ltac:(apply Zinduction).
(* FIXME: Zinduction probably has to be redeclared in the functor because
the parameters like Zsucc are not unfolded for Zinduction in the signature *)

Tactic Notation "Zinduct" ident(n) constr(z) :=
  induction_maker n ltac:(apply Zcentral_induction with z).

End ZBasePropFunct.

(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
