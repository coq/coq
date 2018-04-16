
Require Extraction.
Require Import List.

Section Test.
Variable A : Type.
Variable decA : forall (x y:A), {x=y}+{x<>y}.

(** Should fail when no proofs are started *)
Fail Show Extraction.

Lemma decListA : forall (xs ys : list A), {xs=ys}+{xs<>ys}.
Proof.
Show Extraction.
fix decListA 1.
destruct xs as [|x xs], ys as [|y ys].
Show Extraction.
- now left.
- now right.
- now right.
- Show Extraction.
  destruct (decA x y).
  + destruct (decListA xs ys).
    * left; now f_equal.
    * Show Extraction.
      right. congruence.
  + right. congruence.
Show Extraction.
Defined.

End Test.
