(* Trailing let-ins were dropped in specialize. *)

Module ShortExample.

Lemma test (H : forall x, let y := 1 in x=y) : True.
specialize H with (x:=0).
let t := type of H in let _ := type of t in idtac.
Abort.

End ShortExample.

Module OriginalReport.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
From Stdlib Require Psatz.
From Stdlib Require Utf8.

Import Arith.
Import Psatz.
Import Stdlib.Unicode.Utf8.

Fixpoint log3_iter down_counter log_up_counter up_counter dist_next :=
    match down_counter with
    | O => log_up_counter
    | S down_counter' => match dist_next with
                            | O => log3_iter down_counter' (S log_up_counter) (S up_counter) (2 * up_counter + 1)
                            | S dist_next' => log3_iter down_counter' log_up_counter (S up_counter) dist_next'
                            end
    end.

Definition log3_nat (n: nat) : nat := log3_iter (Nat.pred n) 0 1 1.

Lemma log3_iter_spec : ∀ down_counter log_up_counter up_counter dist_next,
    3^(S log_up_counter) = dist_next + up_counter + 1 →
    dist_next < 2*3^log_up_counter →
    let s := log3_iter down_counter log_up_counter up_counter dist_next in
    3^s <= down_counter + up_counter < 3^(S s).
admit.
Defined.

Lemma log3_nat_mono : ∀ n m, n <= m -> log3_nat n <= log3_nat m.
Proof.
    intros n m LT.
    destruct n.
    replace (log3_nat 0) with 0.
    lia.
    compute.
    lia.
    rewrite -> (Nat.pow_le_mono_r_iff 3); try lia.
    unfold log3_nat.

    pose proof log3_iter_spec as Spec1.
    specialize Spec1 with (down_counter := Nat.pred (S n)).
    specialize Spec1 with (up_counter := 1).
    specialize Spec1 with (log_up_counter := 0).
    specialize Spec1 with (dist_next := 1).
    destruct Spec1.
Abort.

End OriginalReport.
