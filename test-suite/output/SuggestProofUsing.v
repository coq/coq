Require Program.Tactics.

Set Suggest Proof Using.
Set Warnings "-opaque-let".

Lemma nosec : nat. Proof. exact 0. Qed.

Lemma nosec_exactproof : bool. Proof false.

Program Definition nosec_program : nat := _.
Next Obligation. exact 1. Qed.

Lemma nosec_abstract : nat.
Proof. abstract exact 3. Defined.

Section Sec.
  Variables A B : Type.

  (* Some normal lemma. *)
  Lemma Nat : Set.
  Proof.
    exact nat.
  Qed.

  (* Make sure All is suggested even though we add an unused variable
  to the context. *)
  Let foo : Type.
  Proof.
    exact (A -> B).
  Qed.

  (* Having a [Proof using] disables the suggestion message. *)
  Definition bar : Type.
  Proof using A.
    exact A.
  Qed.

  (* Transparent definitions don't get a suggestion message. *)
  Definition baz : Type.
  Proof.
    exact A.
  Defined.

  (* No suggest, is this OK? There's nowhere to put it anyway. *)
  Program Definition program : nat := _.
  Next Obligation. exact 1. Qed.

  (* Must not suggest *)
  Lemma sec_abstract : nat.
  Proof. abstract exact 3. Defined.

  (* Suggests even though there's nowhere to put it, bug? *)
  Lemma sec_exactproof : bool. Proof true.

End Sec.
