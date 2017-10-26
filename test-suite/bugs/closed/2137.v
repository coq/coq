(* Bug #2137

The fsetdec tactic is sensitive to which way round the arguments to <> are.
In the small, self-contained example below, it is able to solve the goal
if it knows that "b <> a", but not if it knows that "a <> b". I would expect
it to be able to solve hte goal in either case.

I have coq r12238.


Thanks
Ian

*)

Require Import Arith FSets FSetWeakList.

Module DecidableNat.
Definition t := nat.
Definition eq := @eq nat.
Definition eq_refl := @refl_equal nat.
Definition eq_sym := @sym_eq nat.
Definition eq_trans := @trans_eq nat.
Definition eq_dec := eq_nat_dec.
End DecidableNat.

Module NatSet := Make(DecidableNat).

Module Export NameSetDec := WDecide (NatSet).

Lemma ThisLemmaWorks : forall ( s0 : NatSet.t )
                              ( a b : nat ),
                       b <> a
                    -> ~(NatSet.In a s0)
                    -> ~(NatSet.In a (NatSet.add b s0)).
Proof.
intros.
fsetdec.
Qed.

Lemma ThisLemmaWasFailing : forall ( s0 : NatSet.t )
                              ( a b : nat ),
                       a <> b
                    -> ~(NatSet.In a s0)
                    -> ~(NatSet.In a (NatSet.add b s0)).
Proof.
intros.
fsetdec.
(*
Error: Tactic failure: because the goal is beyond the scope of this tactic.
*)
Qed.
