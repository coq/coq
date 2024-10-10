(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import BinNums IntDef Uint63Axioms.
From Stdlib Require Import SpecFloat PrimFloat FloatOps.

(** * Properties of the primitive operators for the Binary64 format *)

Notation valid_binary := (valid_binary prec emax).

Definition SF64classify := SFclassify prec.
Definition SF64mul := SFmul prec emax.
Definition SF64add := SFadd prec emax.
Definition SF64sub := SFsub prec emax.
Definition SF64div := SFdiv prec emax.
Definition SF64sqrt := SFsqrt prec emax.
Definition SF64succ := SFsucc prec emax.
Definition SF64pred := SFpred prec emax.

Axiom Prim2SF_valid : forall x, valid_binary (Prim2SF x) = true.
Axiom SF2Prim_Prim2SF : forall x, SF2Prim (Prim2SF x) = x.
Axiom Prim2SF_SF2Prim : forall x, valid_binary x = true -> Prim2SF (SF2Prim x) = x.

Theorem Prim2SF_inj : forall x y, Prim2SF x = Prim2SF y -> x = y.
  intros. rewrite <- SF2Prim_Prim2SF. symmetry. rewrite <- SF2Prim_Prim2SF. now rewrite H.
Qed.

Theorem SF2Prim_inj : forall x y, SF2Prim x = SF2Prim y -> valid_binary x = true -> valid_binary y = true -> x = y.
  intros. rewrite <- Prim2SF_SF2Prim by assumption. symmetry. rewrite <- Prim2SF_SF2Prim by assumption. rewrite H. reflexivity.
Qed.

Axiom opp_spec : forall x, Prim2SF (-x)%float = SFopp (Prim2SF x).
Axiom abs_spec : forall x, Prim2SF (abs x) = SFabs (Prim2SF x).

Axiom eqb_spec : forall x y, (x =? y)%float = SFeqb (Prim2SF x) (Prim2SF y).
Axiom ltb_spec : forall x y, (x <? y)%float = SFltb (Prim2SF x) (Prim2SF y).
Axiom leb_spec : forall x y, (x <=? y)%float = SFleb (Prim2SF x) (Prim2SF y).

Definition flatten_cmp_opt c :=
  match c with
  | None => FNotComparable
  | Some Eq => FEq
  | Some Lt => FLt
  | Some Gt => FGt
  end.
Axiom compare_spec : forall x y, (x ?= y)%float = flatten_cmp_opt (SFcompare (Prim2SF x) (Prim2SF y)).

Module Leibniz.
Axiom eqb_spec : forall x y, Leibniz.eqb x y = true <-> x = y.
End Leibniz.

Axiom classify_spec : forall x, classify x = SF64classify (Prim2SF x).
Axiom mul_spec : forall x y, Prim2SF (x * y)%float = SF64mul (Prim2SF x) (Prim2SF y).
Axiom add_spec : forall x y, Prim2SF (x + y)%float = SF64add (Prim2SF x) (Prim2SF y).
Axiom sub_spec : forall x y, Prim2SF (x - y)%float = SF64sub (Prim2SF x) (Prim2SF y).
Axiom div_spec : forall x y, Prim2SF (x / y)%float = SF64div (Prim2SF x) (Prim2SF y).
Axiom sqrt_spec : forall x, Prim2SF (sqrt x) = SF64sqrt (Prim2SF x).

Axiom of_uint63_spec : forall n, Prim2SF (of_uint63 n) = binary_normalize prec emax (to_Z n) Z0 false.
Axiom normfr_mantissa_spec : forall f, to_Z (normfr_mantissa f) = Z.of_N (SFnormfr_mantissa prec (Prim2SF f)).

Axiom frshiftexp_spec : forall f,
  let (m,e) := frshiftexp f in
  (Prim2SF m, Z.sub (to_Z e) shift) = SFfrexp prec emax (Prim2SF f).
Axiom ldshiftexp_spec : forall f e,
  Prim2SF (ldshiftexp f e) = SFldexp prec emax (Prim2SF f) (Z.sub (to_Z e) shift).

Axiom next_up_spec : forall x, Prim2SF (next_up x) = SF64succ (Prim2SF x).
Axiom next_down_spec : forall x, Prim2SF (next_down x) = SF64pred (Prim2SF x).
