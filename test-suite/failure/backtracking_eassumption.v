(* -*- coq-prog-args: ("-emacs" "-compat" "8.6") -*- *)
(* Cf pull request #287 *)

Require Import Arith.

Goal forall n m p, p <> 0 -> n <> 0 -> m <> 0 -> n * p = m * p -> n = m.
  intros.
  Fail eapply Nat.mul_cancel_r; eassumption.
