Require Import PrimInt63.
Open Scope int63_scope.

Module Type T.
  Primitive bar := #int63_sub.

  Axiom bar_land : bar = land.
End T.

Module F(X:T).
  Definition foo : X.bar 1 1 = 0 := eq_refl.
End F.

Module M.
  Definition bar := land.
  Definition bar_land : bar = land := eq_refl.
End M.

Fail Module N : T := M.

(*
Module A := F N.

Lemma bad : False.
Proof.
  pose (f := fun x => eqb x 1).
  assert (H:f 1 = f 0).
  { f_equal. change 1 with (land 1 1).
    rewrite <-N.bar_land.
    exact A.foo. }
  change (true = false) in H.
  inversion H.
Qed.

Print Assumptions bad.
(* Axioms:
land : int -> int -> int
int : Set
eqb : int -> int -> bool
*)
*)
