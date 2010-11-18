(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt Zorder Zpow_def.

Local Open Scope Z_scope.

(** Definition of Zlog2 *)

Definition Zlog2 z :=
  match z with
    | Zpos (p~1) => Zpos (Psize_pos p)
    | Zpos (p~0) => Zpos (Psize_pos p)
    | _ => 0
  end.

Lemma Zlog2_spec : forall n, 0 < n ->
 2^(Zlog2 n) <= n < 2^(Zsucc (Zlog2 n)).
Proof.
 intros [|[p|p|]|] Hn; split; try easy; unfold Zlog2;
  rewrite <- ?Zpos_succ_morphism, Zpower_Ppow.
 eapply Zle_trans with (Zpos (p~0)).
 apply Psize_pos_le.
 apply Zlt_le_weak. exact (Pcompare_p_Sp (p~0)).
 apply Psize_pos_gt.
 apply Psize_pos_le.
 apply Psize_pos_gt.
Qed.

Lemma Zlog2_nonpos : forall n, n<=0 -> Zlog2 n = 0.
Proof.
 intros [|p|p] H; trivial; now destruct H.
Qed.
