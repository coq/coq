Require Import Coq.Setoids.Setoid.
Goal forall (T : nat -> Set -> Set) (U : Set)
            (H : forall n : nat, T n (match n with
                                      | 0 => fun x => x
                                      | S _ => fun x => x
                                      end (nat = nat)) = U),
    T 0 (nat = nat) = U.
Proof.
  intros.
  let H := match goal with H : forall _, eq _ _ |- _ => H end in
  rewrite H || fail 0 "too early".
  Undo.
  let H := match goal with H : forall _, eq _ _ |- _ => H end in
  setoid_rewrite (H 0) || fail 0 "too early".
  Undo.
  setoid_rewrite H. (* Error: Tactic failure: setoid rewrite failed: Nothing to rewrite. *)
  reflexivity.
Qed.
