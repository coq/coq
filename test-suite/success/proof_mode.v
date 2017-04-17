Declare ML Module "proof_mode_plugin".


Lemma foo : True.
	Proof.
	idtac.
	Proof Mode "test".
	test.
	Proof Mode "Classic".
	idtac.
	trivial.
Qed.

Lemma bar : True.
	Proof.
	idtac.
	Proof Mode "test".
	test.
         Lemma baz : True.
         idtac.
         idtac.
         trivial.
         Qed.
  test.
	Proof Mode "Classic".
	idtac.
	trivial.
Qed.