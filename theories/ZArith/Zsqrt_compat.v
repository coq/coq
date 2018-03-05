(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArithRing.
Require Import Omega.
Require Export ZArith_base.
Local Open Scope Z_scope.

(**  THIS FILE IS DEPRECATED

    Instead of the various [Zsqrt] defined here, please use rather
    [Z.sqrt] (or [Z.sqrtrem]). The latter are pure functions without
    proof parts, and more results are available about them.
    Some equivalence proofs between the old and the new versions
    can be found below. Importing ZArith will provides by default
    the new versions.

*)

(**********************************************************************)
(** Definition and properties of square root on Z *)

(** The following tactic replaces all instances of (POS (xI ...)) by
    `2*(POS ...)+1`, but only when ... is not made only with xO, XI, or xH. *)
Ltac compute_POS :=
  match goal with
    |  |- context [(Zpos (xI ?X1))] =>
      match constr:(X1) with
	| context [1%positive] => fail 1
	| _ => rewrite (Pos2Z.inj_xI X1)
      end
    |  |- context [(Zpos (xO ?X1))] =>
      match constr:(X1) with
	| context [1%positive] => fail 1
	| _ => rewrite (Pos2Z.inj_xO X1)
      end
  end.

Inductive sqrt_data (n:Z) : Set :=
  c_sqrt : forall s r:Z, n = s * s + r -> 0 <= r <= 2 * s -> sqrt_data n.

Definition sqrtrempos : forall p:positive, sqrt_data (Zpos p).
  refine
    (fix sqrtrempos (p:positive) : sqrt_data (Zpos p) :=
      match p return sqrt_data (Zpos p) with
	| xH => c_sqrt 1 1 0 _ _
	| xO xH => c_sqrt 2 1 1 _ _
	| xI xH => c_sqrt 3 1 2 _ _
	| xO (xO p') =>
          match sqrtrempos p' with
            | c_sqrt _ s' r' Heq Hint =>
              match Z_le_gt_dec (4 * s' + 1) (4 * r') with
		| left Hle =>
                  c_sqrt (Zpos (xO (xO p'))) (2 * s' + 1)
                  (4 * r' - (4 * s' + 1)) _ _
		| right Hgt => c_sqrt (Zpos (xO (xO p'))) (2 * s') (4 * r') _ _
              end
          end
	| xO (xI p') =>
          match sqrtrempos p' with
            | c_sqrt _ s' r' Heq Hint =>
              match Z_le_gt_dec (4 * s' + 1) (4 * r' + 2) with
		| left Hle =>
                  c_sqrt (Zpos (xO (xI p'))) (2 * s' + 1)
                  (4 * r' + 2 - (4 * s' + 1)) _ _
		| right Hgt =>
                  c_sqrt (Zpos (xO (xI p'))) (2 * s') (4 * r' + 2) _ _
              end
          end
	| xI (xO p') =>
          match sqrtrempos p' with
            | c_sqrt _ s' r' Heq Hint =>
              match Z_le_gt_dec (4 * s' + 1) (4 * r' + 1) with
		| left Hle =>
                  c_sqrt (Zpos (xI (xO p'))) (2 * s' + 1)
                  (4 * r' + 1 - (4 * s' + 1)) _ _
		| right Hgt =>
                  c_sqrt (Zpos (xI (xO p'))) (2 * s') (4 * r' + 1) _ _
              end
          end
	| xI (xI p') =>
          match sqrtrempos p' with
            | c_sqrt _ s' r' Heq Hint =>
              match Z_le_gt_dec (4 * s' + 1) (4 * r' + 3) with
		| left Hle =>
                  c_sqrt (Zpos (xI (xI p'))) (2 * s' + 1)
                  (4 * r' + 3 - (4 * s' + 1)) _ _
            | right Hgt =>
                c_sqrt (Zpos (xI (xI p'))) (2 * s') (4 * r' + 3) _ _
            end
        end
    end); clear sqrtrempos; repeat compute_POS;
 try (try rewrite Heq; ring); try omega.
Defined.

(** Define with integer input, but with a strong (readable) specification. *)
Definition Zsqrt :
  forall x:Z,
    0 <= x ->
    {s : Z &  {r : Z | x = s * s + r /\ s * s <= x < (s + 1) * (s + 1)}}.
  refine
    (fun x =>
      match
	x
	return
        0 <= x ->
        {s : Z &  {r : Z | x = s * s + r /\ s * s <= x < (s + 1) * (s + 1)}}
	with
	| Zpos p =>
          fun h =>
            match sqrtrempos p with
              | c_sqrt _ s r Heq Hint =>
		existT
                (fun s:Z =>
                  {r : Z |
                    Zpos p = s * s + r /\ s * s <= Zpos p < (s + 1) * (s + 1)})
                s
                (exist
                  (fun r:Z =>
                    Zpos p = s * s + r /\
                    s * s <= Zpos p < (s + 1) * (s + 1)) r _)
            end
	| Zneg p =>
          fun h =>
            False_rec
            {s : Z &
              {r : Z |
		Zneg p = s * s + r /\ s * s <= Zneg p < (s + 1) * (s + 1)}}
            (h (eq_refl Datatypes.Gt))
	| Z0 =>
          fun h =>
            existT
            (fun s:Z =>
              {r : Z | 0 = s * s + r /\ s * s <= 0 < (s + 1) * (s + 1)}) 0
            (exist
               (fun r:Z => 0 = 0 * 0 + r /\ 0 * 0 <= 0 < (0 + 1) * (0 + 1)) 0
               _)
    end); try omega.
 split; [ omega | rewrite Heq; ring_simplify (s*s) ((s + 1) * (s + 1)); omega ].
Defined.

(** Define a function of type Z->Z that computes the integer square root,
    but only for positive numbers, and 0 for others. *)
Definition Zsqrt_plain (x:Z) : Z :=
  match x with
    | Zpos p =>
      match Zsqrt (Zpos p) (Pos2Z.is_nonneg p) with
	| existT _ s _ => s
      end
    | Zneg p => 0
    | Z0 => 0
  end.

(** A basic theorem about Zsqrt_plain *)

Theorem Zsqrt_interval :
  forall n:Z,
    0 <= n ->
    Zsqrt_plain n * Zsqrt_plain n <= n <
    (Zsqrt_plain n + 1) * (Zsqrt_plain n + 1).
Proof.
  intros [|p|p] Hp.
  - now compute.
  - unfold Zsqrt_plain.
    now destruct Zsqrt as (s & r & Heq & Hint).
  - now elim Hp.
Qed.

(** Positivity *)

Theorem Zsqrt_plain_is_pos: forall n, 0 <= n ->  0 <= Zsqrt_plain n.
Proof.
  intros n m; case (Zsqrt_interval n); auto with zarith.
  intros H1 H2; case (Z.le_gt_cases 0 (Zsqrt_plain n)); auto.
  intros H3; contradict H2; auto; apply Z.le_ngt.
  apply Z.le_trans with ( 2 := H1 ).
  replace ((Zsqrt_plain n + 1) * (Zsqrt_plain n + 1))
     with (Zsqrt_plain n * Zsqrt_plain n + (2 * Zsqrt_plain n + 1));
  auto with zarith.
  ring.
Qed.

(** Direct correctness on squares. *)

Theorem Zsqrt_square_id: forall a, 0 <= a ->  Zsqrt_plain (a * a) = a.
Proof.
  intros a H.
  generalize (Zsqrt_plain_is_pos (a * a)); auto with zarith; intros Haa.
  case (Zsqrt_interval (a * a)); auto with zarith.
  intros H1 H2.
  case (Z.le_gt_cases a (Zsqrt_plain (a * a))); intros H3.
  - Z.le_elim H3; auto.
    contradict H1; auto; apply Z.lt_nge; auto with zarith.
    apply Z.le_lt_trans with (a * Zsqrt_plain (a * a)); auto with zarith.
    apply Z.mul_lt_mono_pos_r; auto with zarith.
  - contradict H2; auto; apply Z.le_ngt; auto with zarith.
    apply Z.mul_le_mono_nonneg; auto with zarith.
Qed.

(** [Zsqrt_plain] is increasing *)

Theorem Zsqrt_le:
 forall p q, 0 <= p <= q  ->  Zsqrt_plain p <= Zsqrt_plain q.
Proof.
  intros p q [H1 H2].
  Z.le_elim H2; [ | subst q; auto with zarith].
  case (Z.le_gt_cases (Zsqrt_plain p) (Zsqrt_plain q)); auto; intros H3.
  assert (Hp: (0 <= Zsqrt_plain q)).
  { apply Zsqrt_plain_is_pos; auto with zarith. }
  absurd (q <= p); auto with zarith.
  apply Z.le_trans with ((Zsqrt_plain q + 1) * (Zsqrt_plain q + 1)).
  case (Zsqrt_interval q); auto with zarith.
  apply Z.le_trans with (Zsqrt_plain p * Zsqrt_plain p); auto with zarith.
  apply Z.mul_le_mono_nonneg; auto with zarith.
  case (Zsqrt_interval p); auto with zarith.
Qed.


(** Equivalence between Zsqrt_plain and [Z.sqrt] *)

Lemma Zsqrt_equiv : forall n, Zsqrt_plain n = Z.sqrt n.
Proof.
 intros. destruct (Z_le_gt_dec 0 n).
 symmetry. apply Z.sqrt_unique; trivial.
 now apply Zsqrt_interval.
 now destruct n.
Qed.
