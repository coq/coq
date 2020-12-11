
(** Print Assumption: not available when loading vos files *)

Axiom foo : nat.

Module Type T.
 Parameter bar : nat.
End T.

Module M : T.
  Module Hide. (* An entire sub-module could be hidden *)
  Definition x := foo.
  End Hide.
  Definition bar := Hide.x.
End M.

Module N (X:T) : T.
  Definition y := X.bar. (* A non-exported field *)
  Definition bar := y.
End N.

Module P := N M.

Print Assumptions M.bar. (* Should answer: print assumptions not available *)


Require Import A C.

Lemma R : False /\ False.
Proof.
  split. apply AxiomA. apply AxiomC.
Qed.

Print Assumptions R. (* Should answer: print assumptions not available *)
