From Stdlib Require Import BinInt.

Class decoder (n : Z) W :=
  { decode : W -> Z }.
Coercion decode : decoder >-> Funclass.

Axiom W : Type.

Definition tuple_decoder {n} {decode : decoder n W} (k : nat) : decoder (Z.of_nat k * n) W.
Admitted.


Lemma tuple_decoder_1 {n:Z} {decode : decoder n W}
  (P : forall n, decoder n W -> Type)
  : P (Z.of_nat 1 * n)%Z (tuple_decoder 1).
Admitted.


Axiom Q : forall (n : Z) (Wdecoder : decoder n W), Type.

Lemma is_Q {n decode }
  : Q (1 * n) (@tuple_decoder n decode 1).
Proof.
  Fail apply tuple_decoder_1.
  refine (tuple_decoder_1 _).
(* master: no goals remain
this PR: Error: Found no subterm matching "(Z.of_nat 1 * n)%Z" in the current goal. *)
Qed.

(*
If not using `unsafe_occur_meta_or_existential`,
matching the `tuple_decoder` argument of P/Q instantiated
the `n` argument of `tuple_decoder_1`,
but then when matching `(Z.of_nat 1 * n)%Z`
the unsafe occur check would not realize that `n` is instantiated
so would continue unification with delta on.

If using the `unsafe_occur_meta_or_existential`,
if we `apply (@tuple_decoder_1 n).`
(so there is no evar to be mistaken about)
we get the same `Found no subterm matching "(Z.of_nat 1 * n)%Z"` error.
I don't know if we should consider that the error is legitimate
given that the goal contains `1 * n` (no `Z.of_nat`).
*)
