(* -*- mode: coq; coq-prog-args: ("-vok") -*- *)
(* Print Assumptions reuses traversals across queries in one environment.
   In -vok mode, a Qed lemma from a library loaded without its proofs has no
   readable body, and it is reported as such, with its warning, on every
   path: directly, and through constants an earlier query walked. *)

Require Import TestSuite.for_vos.

Definition use_foo := foo.
Definition use_both := foo + bar.

Print Assumptions use_both.
Print Assumptions use_both.
Print Assumptions foo.
Print Assumptions use_foo.
Print Assumptions bar.
Print Assumptions use_both.
