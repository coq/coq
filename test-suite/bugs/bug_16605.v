Inductive test : unit -> Prop :=.
Definition test2 := forall x, test x.
Lemma t (H : test2) : True.
edestruct H using test_rect.
Abort.

(* Testcase derived from an earlier coq-corn failure *)
Definition existsC :=
 fun P : unit -> Prop => False.

Lemma ex_ind2 : forall (P : unit -> Prop) (Q:Prop), existsC P -> Q.
Proof.
intros. destruct H.
Qed.

Goal (existsC (fun x => True)) -> True.
Proof.
intros.
destruct (H) using ex_ind2. (* parenthesis around (H) are intentional *)
Qed.
