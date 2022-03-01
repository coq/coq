Fail #[deprecated(note="not deprecable")]
Lemma foo : True.

Fail #[deprecated(note="not deprecable")]
Theorem foo' : True.

Fail #[deprecated(note="not deprecable")]
Axiom foo'' : True.

Fail #[deprecated(note="not deprecable")]
Definition foo''' := True.

Fail #[deprecated(note="not deprecable")]
Fixpoint foo'''' n := match n with S n => foo''' n | 0 => 1 end.
