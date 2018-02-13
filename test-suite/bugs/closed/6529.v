Require Import Vector Program.

Program Definition append_nil_def :=
  forall A n (ls: t A n), append ls (nil A) = ls. (* Works *)

Lemma append_nil : append_nil_def. (* Works *)
Proof.
Admitted.

Program Lemma append_nil' :
  forall A n (ls: t A n), append ls (nil A) = ls.
Abort.

Fail Program Lemma append_nil'' :
  forall A B n (ls: t A n), append ls (nil A) = ls.
(* Error: Anomaly "Evar ?X25 was not declared." Please report at http://coq.inria.fr/bugs/. *)
