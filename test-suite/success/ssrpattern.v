Require Import ssrmatching.

(*Set Debug SsrMatching.*)

Tactic Notation "at" "[" ssrpatternarg(pat) "]" tactic(t) :=
  let name := fresh in
  let def_name := fresh in
  ssrpattern pat;
  intro name;
  pose proof (refl_equal name) as def_name;
  unfold name at 1 in def_name;
  t def_name;
  [ rewrite <- def_name | idtac.. ];
  clear name def_name.

Lemma test (H : True -> True -> 3 = 7) : 28 = 3 * 4.
Proof.
at [ X in X * 4 ] ltac:(fun place => rewrite -> H in place).
- reflexivity.
- trivial.
- trivial.
Qed.
