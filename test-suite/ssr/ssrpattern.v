Require Import ssrmatching.

Goal forall n, match n with 0 => 0 | _ => 0 end = 0.
Proof.
  intro n.
  ssrpattern (match _ with 0 => _ | S n' => _ end).
Abort.
