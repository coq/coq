Require Import ZArith.
Require Import ZAux.

Open Local Scope Z_scope.
Notation "x == y '[' 'mod' z ']'" := ((x mod z) = (y mod z))
  (at level 70, no associativity) : Z_scope.

Theorem Zeqmod_refl : forall p n : Z, n == n [mod p].
Proof.
reflexivity.
Qed.

Theorem Zeqmod_symm : forall p n m : Z, n == m [mod p] -> m == n [mod p].
Proof.
now symmetry.
Qed.

Theorem Zeqmod_trans :
  forall p n m k : Z, n == m [mod p] -> m == k [mod p] -> n == k [mod p].
Proof.
intros p n m k H1 H2; now transitivity (m mod p).
Qed.

Theorem Zplus_eqmod_compat_l :
  forall p n m k : Z, 0 < p -> (n == m [mod p] <-> k + n == k + m [mod p]).
intros p n m k H1.
assert (LR : forall n' m' k' : Z, n' == m' [mod p] -> k' + n' == k' + m' [mod p]).
intros n' m' k' H2.
pattern ((k' + n') mod p); rewrite Zmod_plus; [| assumption].
pattern ((k' + m') mod p); rewrite Zmod_plus; [| assumption].
rewrite H2. apply Zeqmod_refl.
split; [apply LR |].
intro H2. apply (LR (k + n) (k + m) (-k)) in H2.
do 2 rewrite Zplus_assoc in H2. rewrite Zplus_opp_l in H2.
now do 2 rewrite Zplus_0_l in H2.
Qed.

Theorem Zplus_eqmod_compat_r :
  forall p n m k : Z, 0 < p -> (n == m [mod p] <-> n + k == m + k [mod p]).
intros p n m k; rewrite (Zplus_comm n k); rewrite (Zplus_comm m k);
apply Zplus_eqmod_compat_l.
Qed.

(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
