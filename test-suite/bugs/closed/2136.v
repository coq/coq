(* Bug #2136

The fsetdec tactic seems to get confused by hypotheses like
    HeqH1 : H1 = MkEquality s0 s1 b
If I clear them then it is able to solve my goal; otherwise it is not.
I would expect it to be able to solve the goal even without this hypothesis
being cleared. A small, self-contained example is below.

I have coq r12238.


Thanks
Ian
*)


Require Import FSets.
Require Import Arith.
Require Import FSetWeakList.

Module DecidableNat.
Definition t := nat.
Definition eq := @eq nat.
Definition eq_refl := @refl_equal nat.
Definition eq_sym := @sym_eq nat.
Definition eq_trans := @trans_eq nat.
Definition eq_dec := eq_nat_dec.
End DecidableNat.

Module NatSet := Make(DecidableNat).

Module Export Dec := WDecide (NatSet).
Import FSetDecideAuxiliary.

Parameter MkEquality : forall ( s0 s1 : NatSet.t )
                              ( x : nat ),
                       NatSet.Equal s1 (NatSet.add x s0).

Lemma ThisLemmaWorks : forall ( s0 s1 : NatSet.t )
                              ( a b : nat ),
                       NatSet.In a s0
                    -> NatSet.In a s1.
Proof.
intros.
remember (MkEquality s0 s1 b) as H1.
clear HeqH1.
fsetdec.
Qed.

Lemma ThisLemmaWasFailing : forall ( s0 s1 : NatSet.t )
                              ( a b : nat ),
                       NatSet.In a s0
                    -> NatSet.In a s1.
Proof.
intros.
remember (MkEquality s0 s1 b) as H1.
fsetdec.
(*
Error: Tactic failure: because the goal is beyond the scope of this tactic.
*)
Qed.
