
(** Examples of extraction with manually-declared implicit arguments *)

(** NB: we should someday check the produced code instead of
    extracting and just compiling. *)

Require Coq.extraction.Extraction.

(** Bug #4243, part 1 *)

Inductive dnat : nat -> Type :=
| d0 : dnat 0
| ds : forall n m, n = m -> dnat n ->  dnat (S n).

Extraction Implicit ds [m].

Lemma dnat_nat: forall n, dnat n -> nat.
Proof.
  intros n d.
  induction d as [| n m Heq d IHn].
  exact 0. exact (S IHn).
Defined.

Recursive Extraction dnat_nat.
Extraction TestCompile dnat_nat.

Extraction Implicit dnat_nat [n].
Recursive Extraction dnat_nat.
Extraction TestCompile dnat_nat.

(** Same, with a Fixpoint *)

Fixpoint dnat_nat' n (d:dnat n) :=
 match d with
 | d0 => 0
 | ds n m _ d => S (dnat_nat' n d)
 end.

Recursive Extraction dnat_nat'.
Extraction TestCompile dnat_nat'.

Extraction Implicit dnat_nat' [n].
Recursive Extraction dnat_nat'.
Extraction TestCompile dnat_nat'.

(** Bug #4243, part 2 *)

Inductive enat: nat -> Type :=
  e0: enat 0
| es: forall n, enat n -> enat (S n).

Lemma enat_nat: forall n, enat n -> nat.
Proof.
  intros n e.
  induction e as [| n e IHe].
  exact (O).
  exact (S IHe).
Defined.

Extraction Implicit es [n].
Extraction Implicit enat_nat [n].
Recursive Extraction enat_nat.
Extraction TestCompile enat_nat.

(** Same, with a Fixpoint *)

Fixpoint enat_nat' n (e:enat n) : nat :=
 match e with
 | e0 => 0
 | es n e => S (enat_nat' n e)
 end.

Extraction Implicit enat_nat' [n].
Recursive Extraction enat_nat'.
Extraction TestCompile enat_nat'.

(** Bug #4228 *)

Module Food.
Inductive Course :=
| main:    nat -> Course
| dessert: nat -> Course.

Inductive Meal : Course -> Type :=
| one_course : forall n:nat, Meal (main n)
| two_course : forall n m, Meal (main n) -> Meal (dessert m).
Extraction Implicit two_course [n].
End Food.

Recursive Extraction Food.Meal.
Extraction TestCompile Food.Meal.
