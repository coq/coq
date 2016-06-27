Axiom T : Type.

Lemma foo : True * Type.
Proof.
  split.
  par: abstract (exact I || exact T).
Defined.

(* Yes, these names are generated hence
   the test is fragile.  I want to assert
   that abstract was correctly handled
   by par: *)
Check foo_subproof.
Check foo_subproof0.
Check (refl_equal _ :
  foo =
  pair foo_subproof foo_subproof0).

Lemma bar : True * Type.
Proof.
  split.
  par: (exact I || exact T).
Defined.
Check (refl_equal _ :
  bar = pair I T).
