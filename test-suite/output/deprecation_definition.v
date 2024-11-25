Require Import Corelib.Program.Tactics.

#[deprecated(note="deprecable")]
Lemma depr1 : True.
Proof.
exact I.
Qed.

#[deprecated(note="deprecable")]
Theorem depr2 : True.
Proof.
exact I.
Qed.

#[deprecated(note="deprecable")]
Axiom depr3 : True.

#[deprecated(note="deprecable")]
Definition depr4 := True.

#[deprecated(note="deprecable")]
Program Definition depr5 := True.

#[deprecated(note="deprecable")]
Fixpoint depr6 n := match n with S n => depr6 n | 0 => 1 end.

Check depr1.
Check depr2.
Check depr3.
Check depr4.
Check depr5.
Check depr6.

#[deprecated(note="deprecable"),
  warn(note="be careful", cats="careful, be careful"),
  warn(note="also about bla", cats="careful, careful bla")]
Definition depr7 := True.
Check depr7.
