(* Check that metas are whd-normalized before trying 2nd-order unification *)
Lemma test : 
  forall (D:Type) (T : forall C, option C) (Q:forall D, option D -> Prop),
  (forall (A : Type) (P : forall B:Type, option B -> Prop), P A (T A))
  -> Q D (T D).
Proof.
  intros D T Q H.
  pattern (T D). apply H.
Qed.
