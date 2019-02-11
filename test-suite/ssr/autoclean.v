Require Import ssreflect.

Lemma view_disappears A B (AB : A -> B) : A -> False.
Proof. move=> {}/(AB). have := AB. Abort.
