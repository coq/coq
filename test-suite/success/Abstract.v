(* Cf BZ#546 *)

Require Import Lia.

Section S.

Variables n m : nat.
Variable H : n<m.

Inductive Dummy : nat -> Set :=
| Dummy0 : Dummy 0
| Dummy2 : Dummy 2
| DummyApp : forall i j, Dummy i -> Dummy j -> Dummy (i+j).

Definition Bug : Dummy (2*n).
Proof.
induction n.
 simpl ; apply Dummy0.
 replace (2 * S n0) with (2*n0 + 2) ; auto with arith.
  apply DummyApp.
   2:exact Dummy2.
   apply IHn0 ; abstract lia.
Defined.

End S.

(* Check visibility *)

Module A.
Definition a : nat.
Proof. abstract (exact 0) using afoo.
Defined.
Print afoo. (* afoo = 0 *)
End A.

Require Import Program.

Module B.
Program Definition b : nat := _.
Next Obligation. abstract (exact 1) using bfoo.
Defined.
Print bfoo. (* bfoo = 1 *)
End B.

Require Import Program.

Module C.
#[local] Obligation Tactic := try abstract (exact 2) using cfoo.
Program Definition c : nat * bool * bool := (_, _, _).
Next Obligation. abstract (exact true) using dfoo. Defined.
Next Obligation. abstract (exact true) using efoo. Qed.
Print cfoo. (* *** [ cfoo : nat ] *)
Print dfoo. (* Check that dfoo exists (dcfoo = true) *)
Fail Check eq_refl : dfoo = true. (* Check that dfoo is opaque *)
Check eq_refl : c_obligation_1 = cfoo. (* Check that dfoo is not inlined *)
Check eq_refl : c_obligation_2 = dfoo. (* Check that dfoo is not inlined *)
Fail Print efoo. (* opaque obligation, efoo not in environment *)
End C.
