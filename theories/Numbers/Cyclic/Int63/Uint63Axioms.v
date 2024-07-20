(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

From Stdlib Require Import BinNums PosDef IntDef.
From Stdlib Require Export PrimInt63.

Local Open Scope Z_scope.

Local Notation "0" := Z0 : Z_scope.
Local Notation "1" := (Zpos 1) : Z_scope.
Local Notation "2" := (Zpos 2) : Z_scope.
Local Infix "+" := Z.add : Z_scope.
Local Infix "-" := Z.sub : Z_scope.
Local Infix "*" := Z.mul : Z_scope.
Local Infix "^" := Z.pow : Z_scope.
Local Infix "<=" := Z.le : Z_scope.
Local Infix "<" := Z.lt : Z_scope.
Local Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.

Definition size := 63%nat.

(** The number of digits as an int *)
Definition digits := 63%uint63.

(** The biggest int *)
Definition max_int := Eval vm_compute in sub 0 1.

(** Access to the nth digits *)
Definition get_digit x p := ltb 0 (land x (lsl 1 p)).

Definition set_digit x p (b:bool) :=
  if if leb 0 p then ltb p digits else false then
    if b then lor x (lsl 1 p)
    else land x (lxor max_int (lsl 1 p))
  else x.

(** Translation to Z *)
Definition is_zero (i:int) := eqb i 0.
Definition is_even (i:int) := is_zero (land i 1).
Fixpoint to_Z_rec (n:nat) (i:int) :=
  match n with
  | O => 0
  | S n =>
      (if is_even i then Z.double else Z.succ_double) (to_Z_rec n (lsr i 1))
  end.

Definition to_Z := to_Z_rec size.

Fixpoint of_pos_rec (n:nat) (p:positive) {struct p} :=
  match n, p with
  | O, _ => 0%uint63
  | S n, xH => 1%uint63
  | S n, xO p => lsl (of_pos_rec n p) 1
  | S n, xI p => lor (lsl (of_pos_rec n p) 1) 1
  end.

Definition of_pos := of_pos_rec size.

Definition of_Z z :=
  match z with
  | Zpos p => of_pos p
  | 0 => 0%uint63
  | Zneg p => sub 0 (of_pos p)
  end.

Definition wB := 2 ^ (Z.of_nat size).

(* Bijection : uint63 <-> Bvector size *)

Axiom of_to_Z : forall x, of_Z (to_Z x) = x.

(** Specification of logical operations *)

Axiom lsl_spec : forall x p, to_Z (lsl x p) = Z.modulo (to_Z x * 2 ^ to_Z p) wB.

Axiom lsr_spec : forall x p, to_Z (lsr x p) = Z.div (to_Z x) (2 ^ to_Z p).

Definition bit i n := negb (is_zero (lsl (lsr i n) (sub digits 1))).

Axiom land_spec : forall x y i, bit (land x y) i = andb (bit x i) (bit y i).

Axiom lor_spec : forall x y i, bit (lor x y) i = orb (bit x i) (bit y i).

Axiom lxor_spec : forall x y i, bit (lxor x y) i = xorb (bit x i) (bit y i).

(** Specification of basic opetations *)

(* Arithmetic modulo operations *)

(* Note: axioms would be simpler if we were using of_Z instead:
   example: add_spec : forall x y, of_Z (x + y) = of_Z x + of_Z y. *)

Axiom add_spec : forall x y, to_Z (add x y) = Z.modulo (to_Z x + to_Z y) wB.

Axiom sub_spec : forall x y, to_Z (sub x y) = Z.modulo (to_Z x - to_Z y) wB.

Axiom mul_spec : forall x y, to_Z (mul x y) = Z.modulo (to_Z x * to_Z y) wB.

Axiom mulc_spec : forall x y,
  to_Z x * to_Z y = to_Z (fst (mulc x y)) * wB + to_Z (snd (mulc x y)).

Axiom div_spec : forall x y, to_Z (div x y) = Z.div (to_Z x) (to_Z y).

Axiom mod_spec : forall x y,
  to_Z (PrimInt63.mod x y) = Z.modulo (to_Z x) (to_Z y).

(* Comparisons *)
Axiom eqb_correct : forall i j, eqb i j = true -> i = j.

Axiom eqb_refl : forall x, eqb x x = true.

Axiom ltb_spec : forall x y, ltb x y = true <-> to_Z x < to_Z y.

Axiom leb_spec : forall x y, leb x y = true <-> to_Z x <= to_Z y.

(** Exotic operations *)

(** Axioms on operations which are just short cut *)

Definition compare_def x y :=
  if ltb x y then Lt else if eqb x y then Eq else Gt.

Axiom compare_def_spec : forall x y, compare x y = compare_def x y.

Axiom head0_spec : forall x, 0 < to_Z x ->
  Z.div wB 2 <= 2 ^ (to_Z (head0 x)) * to_Z x < wB.

Axiom tail0_spec : forall x, 0 < to_Z x ->
  exists y, Z0 <= y /\ to_Z x = (2 * y + 1) * (2 ^ to_Z (tail0 x)).

Definition addc_def x y :=
  let r := add x y in
  if ltb r x then C1 r else C0 r.

Axiom addc_def_spec : forall x y, addc x y = addc_def x y.

Definition addcarry i j := add (add i j) 1.
Definition addcarryc_def x y :=
  let r := addcarry x y in
  if leb r x then C1 r else C0 r.

Axiom addcarryc_def_spec : forall x y, addcarryc x y = addcarryc_def x y.

Definition subc_def x y := if leb y x then C0 (sub x y) else C1 (sub x y).

Axiom subc_def_spec : forall x y, subc x y = subc_def x y.

Definition subcarryc_def x y :=
  if ltb y x then C0 (sub (sub x y) 1) else C1 (sub (sub x y) 1).

Axiom subcarryc_def_spec : forall x y, subcarryc x y = subcarryc_def x y.

Definition diveucl_def x y := (div x y, PrimInt63.mod x y).

Axiom diveucl_def_spec : forall x y, diveucl x y = diveucl_def x y.

Axiom diveucl_21_spec : forall a1 a2 b,
  let (q,r) := diveucl_21 a1 a2 b in
  let (q',r') := Z.div_eucl (to_Z a1 * wB + to_Z a2) (to_Z b) in
  to_Z a1 < to_Z b -> to_Z q = q' /\ to_Z r = r'.

Definition addmuldiv_def p x y :=
  lor (lsl x p) (lsr y (sub digits p)).

Axiom addmuldiv_def_spec : forall p x y,
  addmuldiv p x y = addmuldiv_def p x y.
