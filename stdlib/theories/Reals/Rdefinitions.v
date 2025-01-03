(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Abstraction of classical Dedekind reals behind an opaque module,
   for backward compatibility.

   This file also contains the proof that classical reals are a
   quotient of constructive Cauchy reals. *)

Require Export PeanoNat.
Require Export BinInt.
Require Import QArith_base.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsMult.
Require Import ConstructiveRcomplete.
Require Import ClassicalDedekindReals.


(* Declare primitive number notations for Scope R_scope *)
Declare Scope hex_R_scope.
Declare Scope R_scope.

(* Declare Scope R_scope with Key R *)
Delimit Scope hex_R_scope with xR.
Delimit Scope R_scope with R.

Local Open Scope R_scope.


(* Those symbols must be kept opaque, for backward compatibility. *)
Module Type RbaseSymbolsSig.
  Parameter R : Set.
  Bind Scope R_scope with R.
  Axiom Rabst : CReal -> R.
  Axiom Rrepr : R -> CReal.
  Axiom Rquot1 : forall x y:R, CRealEq (Rrepr x) (Rrepr y) -> x = y.
  Axiom Rquot2 : forall x:CReal, CRealEq (Rrepr (Rabst x)) x.

  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rlt : R -> R -> Prop.

  Parameter R0_def : R0 = Rabst (inject_Q 0).
  Parameter R1_def : R1 = Rabst (inject_Q 1).
  Parameter Rplus_def : forall x y : R,
      Rplus x y = Rabst (CReal_plus (Rrepr x) (Rrepr y)).
  Parameter Rmult_def : forall x y : R,
      Rmult x y = Rabst (CReal_mult (Rrepr x) (Rrepr y)).
  Parameter Ropp_def : forall x : R,
      Ropp x = Rabst (CReal_opp (Rrepr x)).
  Parameter Rlt_def : forall x y : R,
      Rlt x y = CRealLtProp (Rrepr x) (Rrepr y).
End RbaseSymbolsSig.

Module RbaseSymbolsImpl : RbaseSymbolsSig.
  Definition R := DReal.
  Definition Rabst := DRealAbstr.
  Definition Rrepr := DRealRepr.
  Definition Rquot1 := DRealQuot1.
  Definition Rquot2 := DRealQuot2.
  Definition R0 : R := Rabst (inject_Q 0).
  Definition R1 : R := Rabst (inject_Q 1).
  Definition Rplus : R -> R -> R
    := fun x y : R => Rabst (CReal_plus (Rrepr x) (Rrepr y)).
  Definition Rmult : R -> R -> R
    := fun x y : R => Rabst (CReal_mult (Rrepr x) (Rrepr y)).
  Definition Ropp : R -> R
    := fun x : R => Rabst (CReal_opp (Rrepr x)).
  Definition Rlt : R -> R -> Prop
    := fun x y : R => CRealLtProp (Rrepr x) (Rrepr y).

  Definition R0_def := eq_refl R0.
  Definition R1_def := eq_refl R1.
  Definition Rplus_def := fun x y => eq_refl (Rplus x y).
  Definition Rmult_def := fun x y => eq_refl (Rmult x y).
  Definition Ropp_def := fun x => eq_refl (Ropp x).
  Definition Rlt_def := fun x y => eq_refl (Rlt x y).
End RbaseSymbolsImpl.
Export RbaseSymbolsImpl.

(* Keep the same names as before *)
Notation R := RbaseSymbolsImpl.R (only parsing).
Notation R0 := RbaseSymbolsImpl.R0 (only parsing).
Notation R1 := RbaseSymbolsImpl.R1 (only parsing).
Notation Rplus := RbaseSymbolsImpl.Rplus (only parsing).
Notation Rmult := RbaseSymbolsImpl.Rmult (only parsing).
Notation Ropp := RbaseSymbolsImpl.Ropp (only parsing).
Notation Rlt := RbaseSymbolsImpl.Rlt (only parsing).

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope R_scope with R.

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.

Infix "<" := Rlt : R_scope.

(***********************************************************)

(**********)
Definition Rgt (r1 r2:R) : Prop := r2 < r1.

(**********)
Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.

(**********)
Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.

(**********)
Definition Rminus (r1 r2:R) : R := r1 + - r2.


(**********)

Infix "-" := Rminus : R_scope.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">"  := Rgt : R_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : R_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : R_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : R_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : R_scope.

(**********************************************************)
(** *    Injection from [Z] to [R]                        *)
(**********************************************************)

(* compact representation for 2*p *)
Fixpoint IPR_2 (p:positive) : R :=
  match p with
  | xH => R1 + R1
  | xO p => (R1 + R1) * IPR_2 p
  | xI p => (R1 + R1) * (R1 + IPR_2 p)
  end.

Definition IPR (p:positive) : R :=
  match p with
  | xH => R1
  | xO p => IPR_2 p
  | xI p => R1 + IPR_2 p
  end.
Arguments IPR p%_positive : simpl never.

(**********)
Definition IZR (z:Z) : R :=
  match z with
  | Z0 => R0
  | Zpos n => IPR n
  | Zneg n => - IPR n
  end.
Arguments IZR z%_Z : simpl never.

Lemma total_order_T : forall r1 r2:R, {Rlt r1 r2} + {r1 = r2} + {Rlt r2 r1}.
Proof.
  intros. destruct (CRealLt_lpo_dec (Rrepr r1) (Rrepr r2) sig_forall_dec).
  - left. left. rewrite RbaseSymbolsImpl.Rlt_def.
    apply CRealLtForget. exact c.
  - destruct (CRealLt_lpo_dec (Rrepr r2) (Rrepr r1) sig_forall_dec).
    + right. rewrite RbaseSymbolsImpl.Rlt_def. apply CRealLtForget. exact c.
    + left. right. apply Rquot1. split; assumption.
Qed.

Lemma Req_appart_dec : forall x y : R,
    { x = y } + { x < y \/ y < x }.
Proof.
  intros. destruct (total_order_T x y). 1:destruct s.
  - right. left. exact r.
  - left. exact e.
  - right. right. exact r.
Qed.

Lemma Rrepr_appart_0 : forall x:R,
    (x < R0 \/ R0 < x) -> CReal_appart (Rrepr x) (inject_Q 0).
Proof.
  intros. apply CRealLtDisjunctEpsilon. destruct H.
  - left. rewrite RbaseSymbolsImpl.Rlt_def, RbaseSymbolsImpl.R0_def, Rquot2 in H.
    exact H.
  - right. rewrite RbaseSymbolsImpl.Rlt_def, RbaseSymbolsImpl.R0_def, Rquot2 in H.
    exact H.
Qed.

Module Type RinvSig.
  Parameter Rinv : R -> R.
  Parameter Rinv_def : forall x : R,
      Rinv x = match Req_appart_dec x R0 with
               | left _ => R0 (* / 0 is undefined, we take 0 arbitrarily *)
               | right r => Rabst ((CReal_inv (Rrepr x) (Rrepr_appart_0 x r)))
               end.
End RinvSig.

Module RinvImpl : RinvSig.
  Definition Rinv : R -> R
    := fun x => match Req_appart_dec x R0 with
             | left _ => R0 (* / 0 is undefined, we take 0 arbitrarily *)
             | right r => Rabst ((CReal_inv (Rrepr x) (Rrepr_appart_0 x r)))
             end.
  Definition Rinv_def := fun x => eq_refl (Rinv x).
End RinvImpl.
Notation Rinv := RinvImpl.Rinv (only parsing).

Notation "/ x" := (Rinv x) : R_scope.

(**********)
Definition Rdiv (r1 r2:R) : R := r1 * / r2.
Infix "/" := Rdiv   : R_scope.

(* First integer strictly above x *)
Definition up (x : R) : Z.
Proof.
  destruct (CRealArchimedean (Rrepr x)) as [n nmaj], (total_order_T (IZR n - x) R1).
  1:destruct s.
  - exact n.
  - (* x = n-1 *) exact n.
  - exact (Z.pred n).
Defined.

(** Injection of rational numbers into real numbers. *)

Definition Q2R (x : Q) : R := (IZR (Qnum x) * / IZR (QDen x))%R.

(**********************************************************)
(** *    Number notation for constants                    *)
(**********************************************************)

Inductive IR :=
  | IRZ : IZ -> IR
  | IRQ : Q -> IR
  | IRmult : IR -> IR -> IR
  | IRdiv : IR -> IR -> IR.

Definition of_decimal (d : Decimal.decimal) : IR :=
  let '(i, f, e) :=
    match d with
    | Decimal.Decimal i f => (i, f, Decimal.Pos Decimal.Nil)
    | Decimal.DecimalExp i f e => (i, f, e)
    end in
  let zq := match f with
    | Decimal.Nil => IRZ (IZ_of_Z (Z.of_int i))
    | _ =>
      let num := Z.of_int (Decimal.app_int i f) in
      let den := Nat.iter (Decimal.nb_digits f) (Pos.mul 10) 1%positive in
      IRQ (Qmake num den) end in
  let e := Z.of_int e in
  match e with
  | Z0 => zq
  | Zpos e => IRmult zq (IRZ (IZpow_pos 10 e))
  | Zneg e => IRdiv zq (IRZ (IZpow_pos 10 e))
  end.

Definition of_hexadecimal (d : Hexadecimal.hexadecimal) : IR :=
  let '(i, f, e) :=
    match d with
    | Hexadecimal.Hexadecimal i f => (i, f, Decimal.Pos Decimal.Nil)
    | Hexadecimal.HexadecimalExp i f e => (i, f, e)
    end in
  let zq := match f with
    | Hexadecimal.Nil => IRZ (IZ_of_Z (Z.of_hex_int i))
    | _ =>
      let num := Z.of_hex_int (Hexadecimal.app_int i f) in
      let den := Nat.iter (Hexadecimal.nb_digits f) (Pos.mul 16) 1%positive in
      IRQ (Qmake num den) end in
  let e := Z.of_int e in
  match e with
  | Z0 => zq
  | Zpos e => IRmult zq (IRZ (IZpow_pos 2 e))
  | Zneg e => IRdiv zq (IRZ (IZpow_pos 2 e))
  end.

Definition of_number (n : Number.number) : IR :=
  match n with
  | Number.Decimal d => of_decimal d
  | Number.Hexadecimal h => of_hexadecimal h
  end.

Definition IQmake_to_decimal num den :=
  match den with
  | 1%positive => None  (* this should be encoded as IRZ *)
  | _ => IQmake_to_decimal num den
  end.

Definition to_decimal (n : IR) : option Decimal.decimal :=
  match n with
  | IRZ z =>
    match IZ_to_Z z with
    | Some z => Some (Decimal.Decimal (Z.to_int z) Decimal.Nil)
    | None => None
    end
  | IRQ (Qmake num den) => IQmake_to_decimal num den
  | IRmult (IRZ z) (IRZ (IZpow_pos 10 e)) =>
    match IZ_to_Z z with
    | Some z =>
      Some (Decimal.DecimalExp (Z.to_int z) Decimal.Nil (Pos.to_int e))
    | None => None
    end
  | IRmult (IRQ (Qmake num den)) (IRZ (IZpow_pos 10 e)) =>
    match IQmake_to_decimal num den with
    | Some (Decimal.Decimal i f) =>
      Some (Decimal.DecimalExp i f (Pos.to_int e))
    | _ => None
    end
  | IRdiv (IRZ z) (IRZ (IZpow_pos 10 e)) =>
    match IZ_to_Z z with
    | Some z =>
      Some (Decimal.DecimalExp (Z.to_int z) Decimal.Nil (Decimal.Neg (Pos.to_uint e)))
    | None => None
    end
  | IRdiv (IRQ (Qmake num den)) (IRZ (IZpow_pos 10 e)) =>
    match IQmake_to_decimal num den with
    | Some (Decimal.Decimal i f) =>
      Some (Decimal.DecimalExp i f (Decimal.Neg (Pos.to_uint e)))
    | _ => None
    end
  | _ => None
  end.

Definition IQmake_to_hexadecimal num den :=
  match den with
  | 1%positive => None  (* this should be encoded as IRZ *)
  | _ => IQmake_to_hexadecimal num den
  end.

Definition to_hexadecimal (n : IR) : option Hexadecimal.hexadecimal :=
  match n with
  | IRZ z =>
    match IZ_to_Z z with
    | Some z => Some (Hexadecimal.Hexadecimal (Z.to_hex_int z) Hexadecimal.Nil)
    | None => None
    end
  | IRQ (Qmake num den) => IQmake_to_hexadecimal num den
  | IRmult (IRZ z) (IRZ (IZpow_pos 2 e)) =>
    match IZ_to_Z z with
    | Some z =>
      Some (Hexadecimal.HexadecimalExp (Z.to_hex_int z) Hexadecimal.Nil (Pos.to_int e))
    | None => None
    end
  | IRmult (IRQ (Qmake num den)) (IRZ (IZpow_pos 2 e)) =>
    match IQmake_to_hexadecimal num den with
    | Some (Hexadecimal.Hexadecimal i f) =>
      Some (Hexadecimal.HexadecimalExp i f (Pos.to_int e))
    | _ => None
    end
  | IRdiv (IRZ z) (IRZ (IZpow_pos 2 e)) =>
    match IZ_to_Z z with
    | Some z =>
      Some (Hexadecimal.HexadecimalExp (Z.to_hex_int z) Hexadecimal.Nil (Decimal.Neg (Pos.to_uint e)))
    | None => None
    end
  | IRdiv (IRQ (Qmake num den)) (IRZ (IZpow_pos 2 e)) =>
    match IQmake_to_hexadecimal num den with
    | Some (Hexadecimal.Hexadecimal i f) =>
      Some (Hexadecimal.HexadecimalExp i f (Decimal.Neg (Pos.to_uint e)))
    | _ => None
    end
  | _ => None
  end.

Definition to_number q :=
  match to_decimal q with
  | None => None
  | Some q => Some (Number.Decimal q)
  end.

Definition to_hex_number q :=
  match to_hexadecimal q with
  | None => None
  | Some q => Some (Number.Hexadecimal q)
  end.

Number Notation R of_number to_hex_number (via IR
  mapping [IZR => IRZ, Q2R => IRQ, Rmult => IRmult, Rdiv => IRdiv,
           Z.pow_pos => IZpow_pos, Z0 => IZ0, Zpos => IZpos, Zneg => IZneg])
  : hex_R_scope.

Number Notation R of_number to_number (via IR
  mapping [IZR => IRZ, Q2R => IRQ, Rmult => IRmult, Rdiv => IRdiv,
           Z.pow_pos => IZpow_pos, Z0 => IZ0, Zpos => IZpos, Zneg => IZneg])
  : R_scope.
