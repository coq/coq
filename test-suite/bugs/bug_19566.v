
Universes u v.
Lemma foo : Type@{v}.
  exact Type@{u}.
Admitted.

Check Type@{v} : Type@{u}.
