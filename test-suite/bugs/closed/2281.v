(** Bug #2281

In the code below, coq is confused by an equality unless it is first 'subst'ed
away, yet http://coq.inria.fr/stdlib/Coq.FSets.FSetDecide.html says

    fsetdec will first perform any necessary zeta and beta reductions and will
invoke subst to eliminate any Coq equalities between finite sets or their
elements.

I have coq r12851.

*)

Require Import Arith.
Require Import FSets.
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

Module Export NameSetDec := WDecide (NatSet).

Lemma ThisLemmaWorks : forall ( s1 s2 : NatSet.t )
                              ( H : s1 = s2 ),
                       NatSet.Equal s1 s2.
Proof.
intros.
subst.
fsetdec.
Qed.

Import FSetDecideAuxiliary.

Lemma ThisLemmaWasFailing : forall ( s1 s2 : NatSet.t )
                              ( H : s1 = s2 ),
                       NatSet.Equal s1 s2.
Proof.
intros.
fsetdec.
(* Error: Tactic failure: because the goal is beyond the scope of this tactic.
*)
Qed.
