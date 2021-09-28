(* NB: using Qed for t_X_refl breaks the async proofs mode *)

Cumulative Polymorphic Class t@{+s} (S : Type@{s}) (A B : Prop) :=
  T {
      prf : S -> A -> B;
    }.
Monomorphic Inductive X@{s | Set < s} : Type@{s} := x.

#[refine]
 Instance t_X_refl {A} : t X A A := {|prf := _|}.
Proof. auto. Defined.

Module A.
  (* Note universe constraint! *)
  Lemma foo@{s|X.s < s} : forall A, t@{s} X A A.
  Proof.
    assert_succeeds typeclasses eauto.
    intros; typeclasses eauto. (* fails but should succeed, I think *)
  Defined.
End A.


Module B.
  (* No universe constraint this time! *)
  Lemma foo@{s} : forall A, t@{s} X A A.
  Proof.
    assert_succeeds (intros; typeclasses eauto). (* succeeds now *)
    typeclasses eauto.                   (* succeeds as before *)
  Defined.
End B.
