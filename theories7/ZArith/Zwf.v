(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require ZArith_base.
Require Export Wf_nat.
Require Omega.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

(** Well-founded relations on Z. *)

(** We define the following family of relations on [Z x Z]: 

    [x (Zwf c) y]   iff   [x < y & c <= y]
 *)

Definition Zwf := [c:Z][x,y:Z] `c <= y` /\ `x < y`.

(** and we prove that [(Zwf c)] is well founded *)

Section wf_proof.

Variable c : Z.

(** The proof of well-foundness is classic: we do the proof by induction
    on a measure in nat, which is here [|x-c|] *)

Local f := [z:Z](absolu (Zminus z c)).

Lemma Zwf_well_founded : (well_founded Z (Zwf c)).
Red; Intros.
Assert (n:nat)(a:Z)(lt (f a) n)\/(`a<c`) -> (Acc Z (Zwf c) a).
Clear a; Induction n; Intros.
(** n= 0 *)
Case H; Intros.
Case (lt_n_O (f a)); Auto.
Apply Acc_intro; Unfold Zwf; Intros.
Assert False;Omega Orelse Contradiction.
(** inductive case *)
Case H0; Clear H0; Intro; Auto.
Apply Acc_intro; Intros.
Apply H.
Unfold Zwf in H1.
Case (Zle_or_lt c y); Intro; Auto with zarith.
Left.
Red in H0.
Apply lt_le_trans with (f a); Auto with arith.
Unfold f.
Apply absolu_lt; Omega.
Apply (H (S (f a))); Auto.
Save.

End wf_proof.

Hints Resolve Zwf_well_founded : datatypes v62.


(** We also define the other family of relations:

    [x (Zwf_up c) y]   iff   [y < x <= c]
 *)

Definition Zwf_up := [c:Z][x,y:Z] `y < x <= c`.

(** and we prove that [(Zwf_up c)] is well founded *)

Section wf_proof_up.

Variable c : Z.

(** The proof of well-foundness is classic: we do the proof by induction
    on a measure in nat, which is here [|c-x|] *)

Local f := [z:Z](absolu (Zminus c z)).

Lemma Zwf_up_well_founded : (well_founded Z (Zwf_up c)).
Proof.
Apply well_founded_lt_compat with f:=f.
Unfold Zwf_up f.
Intros.
Apply absolu_lt.
Unfold Zminus. Split.
Apply Zle_left; Intuition.
Apply Zlt_reg_l; Unfold Zlt; Rewrite <- Zcompare_Zopp; Intuition.
Save.

End wf_proof_up.

Hints Resolve Zwf_up_well_founded : datatypes v62.
