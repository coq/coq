Require Import Setoid Ring Ring_theory.

Module abs_ring.

Parameters (Coef:Set)(c0 c1 : Coef)
(cadd cmul csub: Coef -> Coef -> Coef)
(copp : Coef -> Coef)
(ceq : Coef -> Coef -> Prop)
(ceq_sym : forall x y, ceq x y -> ceq y x)
(ceq_trans : forall x y z, ceq x y -> ceq y z -> ceq x z)
(ceq_refl : forall x, ceq x x).


Add Relation Coef ceq
  reflexivity proved by ceq_refl symmetry proved by ceq_sym
  transitivity proved by ceq_trans
  as ceq_relation.

Add Morphism cadd with signature ceq ==> ceq ==> ceq as cadd_Morphism.
Admitted.

Add Morphism cmul with signature ceq ==> ceq ==> ceq as cmul_Morphism.
Admitted.

Add Morphism copp with signature ceq ==> ceq as copp_Morphism.
Admitted.

Definition cRth : ring_theory c0 c1 cadd cmul csub copp ceq.
Admitted.

Add Ring CoefRing : cRth.

End abs_ring.
Import abs_ring.

Theorem check_setoid_ring_modules :
  forall a b, ceq (cadd a b) (cadd b a).
intros.
ring.
Qed.

(* Check that an Add Ring definition in a section is really local *)

Module Ring_in_section.

Section S.
Add Ring CoefRing1 : cRth.
End S.

Add Ring CoefRing1 : cRth.

End Ring_in_section.

(** Test parametric ring *)

Require Import Field_theory Field_tac.

Module ParametricRing.

Record IsField Coef := {
  c0: Coef;
  c1 : Coef;
  cadd : Coef -> Coef -> Coef;
  cmul : Coef -> Coef -> Coef;
  csub : Coef -> Coef -> Coef;
  cdiv : Coef -> Coef -> Coef;
  copp : Coef -> Coef;
  cinv : Coef -> Coef;
  field_th : field_theory c0 c1 cadd cmul csub copp cdiv cinv eq
}.

Lemma isfield_is_ring A (K:IsField A) :
  ring_theory K.(c0 A) K.(c1 A) K.(cadd A) K.(cmul A) K.(csub A) K.(copp A) eq.
Admitted.

(* Check that the carrier comes with enough structure *)

Fail Add Ring Ring_of_field A (K:IsField A) : (isfield_is_ring A K).

Record Field := { carrier : Type; isfield :> IsField carrier }.

Lemma field_is_ring (K:Field) :
  ring_theory K.(c0 (carrier K)) K.(c1 (carrier K)) K.(cadd (carrier K)) K.(cmul (carrier K)) K.(csub (carrier K)) K.(copp (carrier K)) eq.
Admitted.

Add Ring Ring_of_field K : (field_is_ring K).

Theorem check_ring_of_field (K : Field) x y :
  K.(cadd (carrier K)) x y = K.(cadd (carrier K)) y x.
Proof.
ring.
Qed.

(* Test with two parameters *)

Parameter mf : forall A, IsField A -> Field.
Axiom mf_is_field : forall A K,
  field_theory (mf A K).(c0 _) (mf A K).(c1 _)
    (mf A K).(cadd _) (mf A K).(cmul _)
    (mf A K).(csub _) (mf A K).(copp _)
    (mf A K).(cdiv _) (mf A K).(cinv _) eq.

Add Field Combined_field A K : (mf_is_field A K).

Theorem check_mf A K x y :
  (mf A K).(cadd _) x y = (mf A K).(cadd _) y x.
Proof.
field.
Qed.

End ParametricRing.
