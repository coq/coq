(* coq-prog-args: ("-async-proofs" "off") *)

#[universes(cumulative=yes)]
 Polymorphic Class t@{-s} (S : Type@{s}) (A B : Prop) :=
  T {
      prf : S -> A -> B;
    }.
Monomorphic Inductive X@{s | Set < s} : Type@{s} := x.

#[refine, export]
 Instance t_X_refl {A} : t X A A := {|prf := _|}.
Proof. auto. Qed.

Module A.
  (* Note universe constraint! *)
  Lemma foo@{s|X.s < s} : forall A, t@{s} X A A.
  Proof.
    assert_succeeds typeclasses eauto.
    intros; typeclasses eauto. (* fails but should succeed, I think *)
  Qed.
End A.


Module B.
  (* No universe constraint this time! *)
  Lemma foo@{s} : forall A, t@{s} X A A.
  Proof.
    assert_succeeds (intros; typeclasses eauto). (* succeeds now *)
    typeclasses eauto.                   (* succeeds as before *)
  Qed.
End B.
