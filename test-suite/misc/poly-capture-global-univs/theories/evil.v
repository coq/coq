
Declare ML Module "evil_plugin".

Evil T f. (* <- if this doesn't fail then the rest goes through *)

Definition g : Type -> Set := f.

Require Import Hurkens.

Lemma absurd : False.
Proof.
  exact (TypeNeqSmallType.paradox (g Type) eq_refl).
Qed.
