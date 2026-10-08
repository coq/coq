Require Import Corelib.Array.PrimArray.
Axiom P : forall A t i (a:A), get t i = a.
Universe glob.
Axiom Q : forall A a i, @length@{glob} A a = i.
Lemma test : forall A a i, @length@{P.u0} A a = i.
Proof.
  intros A a i.
  Succeed refine (Q _ _ _).
Abort.


Definition foo@{u v|} : length@{u} [| | 0 |] = length@{v} [| | 0 |]
  := eq_refl.
