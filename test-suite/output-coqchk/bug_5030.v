Module Type testt.
Parameter proof : True.
End testt.

Module Export test : testt.
Definition proof := I.
End test.

Lemma true : True.
Proof. apply proof. Qed.
