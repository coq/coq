(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Import Omega.
Require Export ZArith_base.
Require Export ZArithRing.
Open Local Scope Z_scope.

(**********************************************************************)
(** Definition and properties of square root on Z *)

(** The following tactic replaces all instances of (POS (xI ...)) by
    `2*(POS ...)+1`, but only when ... is not made only with xO, XI, or xH. *)
Ltac compute_POS :=
  match goal with
  |  |- context [(Zpos (xI ?X1))] =>
      match constr:X1 with
      | context [1%positive] => fail
      | _ => rewrite (BinInt.Zpos_xI X1)
      end
  |  |- context [(Zpos (xO ?X1))] =>
      match constr:X1 with
      | context [1%positive] => fail
      | _ => rewrite (BinInt.Zpos_xO X1)
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
        | c_sqrt s' r' Heq Hint =>
            match Z_le_gt_dec (4 * s' + 1) (4 * r') with
            | left Hle =>
                c_sqrt (Zpos (xO (xO p'))) (2 * s' + 1)
                  (4 * r' - (4 * s' + 1)) _ _
            | right Hgt => c_sqrt (Zpos (xO (xO p'))) (2 * s') (4 * r') _ _
            end
        end
    | xO (xI p') =>
        match sqrtrempos p' with
        | c_sqrt s' r' Heq Hint =>
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
        | c_sqrt s' r' Heq Hint =>
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
        | c_sqrt s' r' Heq Hint =>
            match Z_le_gt_dec (4 * s' + 1) (4 * r' + 3) with
            | left Hle =>
                c_sqrt (Zpos (xI (xI p'))) (2 * s' + 1)
                  (4 * r' + 3 - (4 * s' + 1)) _ _
            | right Hgt =>
                c_sqrt (Zpos (xI (xI p'))) (2 * s') (4 * r' + 3) _ _
            end
        end
    end); clear sqrtrempos; repeat compute_POS;
 try (try rewrite Heq; ring; fail); try omega.
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
          | c_sqrt s r Heq Hint =>
              existS
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
            (h (refl_equal Datatypes.Gt))
    | Z0 =>
        fun h =>
          existS
            (fun s:Z =>
               {r : Z | 0 = s * s + r /\ s * s <= 0 < (s + 1) * (s + 1)}) 0
            (exist
               (fun r:Z => 0 = 0 * 0 + r /\ 0 * 0 <= 0 < (0 + 1) * (0 + 1)) 0
               _)
    end); try omega.
split; [ omega | rewrite Heq; ring ((s + 1) * (s + 1)); omega ].
Defined.

(** Define a function of type Z->Z that computes the integer square root,
    but only for positive numbers, and 0 for others. *)
Definition Zsqrt_plain (x:Z) : Z :=
  match x with
  | Zpos p =>
      match Zsqrt (Zpos p) (Zorder.Zle_0_pos p) with
      | existS s _ => s
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
intros x; case x.
unfold Zsqrt_plain in |- *; omega.
intros p; unfold Zsqrt_plain in |- *;
 case (Zsqrt (Zpos p) (Zorder.Zle_0_pos p)).
intros s [r [Heq Hint]] Hle; assumption.
intros p Hle; elim Hle; auto.
Qed.

