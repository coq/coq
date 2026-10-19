(* -*- mode: coq; coq-prog-args: ("-vok") -*- *)
(* In -vok mode, the Qed body of [foo], from a library loaded without its
   proofs, cannot be read. A walk that meets such a body is not recorded, so
   [use_foo] and [use_both], whose walks meet it, are never replayed; [bar]
   and what it uses are. *)

Require Import TestSuite.for_vos.

Set Debug "assumptions-cache".

Definition use_foo := foo.
Definition use_both := foo + bar.

Print Assumptions use_both.
Print Assumptions use_both.
Print Assumptions use_foo.
Print Assumptions use_foo.
Print Assumptions bar.
