Require Import Coq.Arith.Arith.
Require Import Lt.
Require Import Omega.

Axiom lt_ge_dec : forall x y : nat, { x < y } + { x >= y }.
(*Proof.
  intros.
  elim (le_lt_dec y x) ; intros ; auto with arith.
Defined.
*)
Require Import Coq.subtac.FixSub.
Require Import Wf_nat.

Lemma preda_lt_a : forall a, 0 < a -> pred a < a.
auto with arith.
Qed.

Program Fixpoint id_struct (a : nat) : nat :=
  match a with
  0 => 0
  | S n => S (id_struct n)
  end.

Check struct_rec.

  if (lt_ge_dec O a)
  then S (wfrec (pred a))
  else O.

Program Fixpoint wfrec (a : nat) { wf a lt } : nat :=
  if (lt_ge_dec O a)
  then S (wfrec (pred a))
  else O.
intros.
apply preda_lt_a ; auto.

Defined.

Extraction wfrec.
Extraction Inline proj1_sig.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inlined Constant lt_ge_dec => "<".

Extraction wfrec.
Extraction Inline lt_ge_dec le_lt_dec.
Extraction wfrec.


Program Fixpoint structrec (a : nat) { wf a lt } : nat :=
  match a with
   S n => S (structrec n)
   | 0 => 0
   end.
intros.
unfold n0.
omega.
Defined.

Print structrec.
Extraction structrec.
Extraction structrec.

Definition structrec_fun (a : nat) : nat := structrec a (lt_wf a).
Print structrec_fun.
