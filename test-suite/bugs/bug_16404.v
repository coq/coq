From Coq Require Import Program.Basics.
From Coq Require Import Vectors.Vector.

Require Import Lia.
Require Import ZArith.
Import ZifyClasses.

Definition Vec (n : nat) (a : Type) : Type := VectorDef.t a n.
Notation bitvector n := (Vec n bool).

Definition bvToInt : forall w, bitvector w -> Z. Admitted.
Definition bvAdd : forall w, bitvector w -> bitvector w -> bitvector w. Admitted.

Class Modulus (n:nat) (m:Z) := ismodulus : m = Z.pow 2 (Z.of_nat n).

Global Instance mod_64 : Modulus 64 (Z.pow 2 64) := eq_refl.

Section Generic.

  Context (w:nat) {modulus:Z} {IsMod:Modulus w modulus}.

  (* Proof using to ensure that the instances depend on IsMod *)
  Lemma inj_lemma x : (0 <= bvToInt w x < modulus)%Z.
  Proof using IsMod.
  Admitted.

  Global Instance Inj_bv_Z : InjTyp (bitvector w) Z :=
    { inj := bvToInt w
    ; pred := fun x => Z.le 0 x /\ Z.lt x modulus
    ; cstr := inj_lemma
    }.

  Global Program Instance Rel_eq_bv : BinRel (@eq (bitvector w)) :=
    { TR := @eq Z
    }.
  Next Obligation.
  Admitted.

  Global Program Instance Op_bvAdd : BinOp (bvAdd w : bitvector w -> bitvector w -> bitvector w) :=
    { TBOp := fun x y => Z.modulo (Z.add x y) modulus
    }.
  Next Obligation.
  Admitted.

End Generic.

Section UseGeneric.

  Context (w:nat) {modulus:Z} {IsMod:Modulus w modulus}.

  Add Zify InjTyp (Inj_bv_Z w).
  Add Zify BinRel (Rel_eq_bv w).

  Lemma test_refl :
    forall (x : bitvector w), x = x.
  Proof. lia. Qed.

End UseGeneric.

Notation w := 64.

Add Zify InjTyp (Inj_bv_Z w).
Add Zify BinRel (Rel_eq_bv w).
Add Zify BinOp (Op_bvAdd w).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* NB: out of scope for lia with generic w, see #16882 *)
Lemma test_bvAdd_comm :
  forall (x y : bitvector w),
  bvAdd w x y = bvAdd w y x.
Proof.
  lia.
Qed.
