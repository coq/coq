
Require Import ZArith ROmega.
Local Open Scope Z_scope.

(** Benchmark provided by Chantal Keller, that romega used to
    solve far too slowly (compared to omega or lia). *)

Parameter v4 : Z.
Parameter v3 : Z.
Parameter o4 : Z.
Parameter s5 : Z.
Parameter v2 : Z.
Parameter o5 : Z.
Parameter s6 : Z.
Parameter v1 : Z.
Parameter o6 : Z.
Parameter s7 : Z.
Parameter v0 : Z.
Parameter o7 : Z.

Lemma lemma_5833 :
 ~ 16 * v4 + (8 * v3 + (-8192 * o4 + (-4096 * s5 + (4 * v2 +
      (-4096 * o5 + (-2048 * s6 + (2 * v1 + (-2048 * o6 +
         (-1024 * s7 + (v0 + -1024 * o7)))))))))) >= 8192
\/
  16 * v4 + (8 * v3 + (-8192 * o4 + (-4096 * s5 + (4 * v2 +
      (-4096 * o5 + (-2048 * s6 + (2 * v1 + (-2048 * o6 +
         (-1024 * s7 + (v0 + -1024 * o7)))))))))) >= 1024.
Proof.
Timeout 1 romega. (* should take a few milliseconds, not seconds *)
Timeout 1 Qed. (* ditto *)
