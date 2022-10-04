Inductive test : unit -> Prop :=.
Definition test2 := forall x, test x.
Lemma t (H : test2) : True.
edestruct H using test_rect.
Abort.
