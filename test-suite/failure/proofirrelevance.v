(* This was working in version 8.1beta (bug in template polymorphism),
   but this is inconsistent with classical logic in Prop *)

Inductive bool_in_prop : Type := hide : bool -> bool_in_prop
with bool : Type := true : bool | false : bool.

Lemma not_proof_irrelevance : ~ forall (P:Prop) (p p':P), p=p'.
intro H.
Fail pose proof (H bool_in_prop (hide true) (hide false)).
Abort.
(*discriminate.
Qed.*)

