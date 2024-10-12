Module numbers.
  From Stdlib Require Export EqdepFacts PArith NArith ZArith.
End numbers.

Import numbers.
Open Scope Z_scope.
(* Make sure Z_scope is open. *)
Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. reflexivity. Qed.

Import numbers.

(* Make sure Z_scope is still open. *)
Local Lemma Z_scope_test2 : (0%Z) + (0%Z) = 0%Z.
Proof. reflexivity. Qed.
