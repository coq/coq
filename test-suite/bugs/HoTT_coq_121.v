Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 8249 lines to 907 lines, then from 843 lines to 357 lines, then from 351 lines to 260 lines, then from 208 lines to 162 lines, then from 167 lines to 154 lines, then from 146 lines to 72 lines, then from 82 lines to 70 lines, then from 79 lines to 49 lines, then from 59 lines to 16 lines *)

Set Universe Polymorphism.
Generalizable All Variables.
Record hSet := BuildhSet {setT:> Type}.
Axiom minus1Trunc : Type -> Type.
Definition hexists {X} (P:X->Type):Type:= minus1Trunc (sigT  P).
Definition issurj {X Y} (f:X->Y) := forall y:Y, hexists (fun x => (f x) = y).
Lemma isepi_issurj {X Y} (f:X->Y): issurj f.
Proof.
  intros y.
  admit.
Defined. (* Toplevel input, characters 15-23:
Error: Unsatisfied constraints:
Top.38 <= Coq.Init.Specif.7
Top.43 <= Top.38
Top.43 <= Coq.Init.Specif.8
 (maybe a bugged tactic). *)
