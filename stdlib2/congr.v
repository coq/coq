From stdlib Require Import prelude ssreflect equality nat abstract.

(* Internal N-ary congruence lemmas for the congr tactic.                     *)

Fixpoint nary_congruence_statement (n : nat)
         : (forall B, (B -> B -> Prop) -> Prop) -> Prop :=
  match n with
  | O => fun k => forall B, k B (fun x1 x2 : B => x1 = x2)
  | S n' =>
    let k' A B e (f1 f2 : A -> B) :=
      forall x1 x2, x1 = x2 -> (e (f1 x1) (f2 x2) : Prop) in
    fun k => forall A, nary_congruence_statement n' (fun B e => k _ (k' A B e))
  end.

Lemma nary_congruence n (k := fun B e => forall y : B, (e y y : Prop)) :
  nary_congruence_statement n k.
Proof.
have: k _ _ := _; rewrite {1}/k.
elim: n k  => [|n IHn] k k_P /= A; first exact: k_P.
by apply: IHn => B e He; apply: k_P => f x1 x2 <-.
Qed.

Lemma ssr_congr_arrow Plemma Pgoal : Plemma = Pgoal -> Plemma -> Pgoal.
Proof. by move->. Qed.
Arguments ssr_congr_arrow : clear implicits.

Register nary_congruence as plugins.ssreflect.nary_congruence.
Register ssr_congr_arrow as plugins.ssreflect.ssr_congr_arrow.
