(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export BinInt.
Require Export ZArithRing.
Require Export ZArith.BinInt.
Require Export Morphisms Setoid Bool.

Require ZArith.Zcompare.
Require ZArith_dec.

(** * Definition of [Q] and basic properties *)

(** Rationals are pairs of [Z] and [positive] numbers. *)

Record Q : Set := Qmake {Qnum : Z; Qden : positive}.

Declare Scope hex_Q_scope.
Delimit Scope hex_Q_scope with xQ.

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.
Arguments Qmake _%_Z _%_positive.

Register Q as rat.Q.type.
Register Qmake as rat.Q.Qmake.

Open Scope Q_scope.
Ltac simpl_mult := rewrite ?Pos2Z.inj_mul.

(** [a#b] denotes the fraction [a] over [b]. *)

Notation "a # b" := (Qmake a b) (at level 55, no associativity) : Q_scope.

Definition inject_Z (x : Z) := Qmake x 1.
Arguments inject_Z x%_Z.

Notation QDen p := (Zpos (Qden p)).

Definition Qeq (p q : Q) := (Qnum p * QDen q)%Z = (Qnum q * QDen p)%Z.
Definition Qle (x y : Q) := (Qnum x * QDen y <= Qnum y * QDen x)%Z.
Definition Qlt (x y : Q) := (Qnum x * QDen y < Qnum y * QDen x)%Z.
Notation Qgt a b := (Qlt b a) (only parsing).
Notation Qge a b := (Qle b a) (only parsing).

Infix "==" := Qeq (at level 70, no associativity) : Q_scope.
Infix "<" := Qlt : Q_scope.
Infix "<=" := Qle : Q_scope.
Notation "x > y" := (Qlt y x)(only parsing) : Q_scope.
Notation "x >= y" := (Qle y x)(only parsing) : Q_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : Q_scope.
Notation "x <= y < z" := (x<=y/\y<z) : Q_scope.
Notation "x < y <= z" := (x<y/\y<=z) : Q_scope.
Notation "x < y < z" := (x<y/\y<z) : Q_scope.

Register Qeq as rat.Q.Qeq.
Register Qle as rat.Q.Qle.
Register Qlt as rat.Q.Qlt.

(**
  Qeq construction from parts.
  Establishing equality by establishing equality
  for numerator and denominator separately.
*)

Lemma Qden_cancel : forall (a b : Z) (p : positive),
  (a#p)==(b#p) -> a=b.
Proof.
  intros a b p.
  unfold Qeq.
  apply Z.mul_cancel_r, not_eq_sym, Z.lt_neq, Pos2Z.is_pos.
Qed.

Lemma Qnum_cancel : forall (a b : positive) (z : Z),
  z<>0%Z -> (z#a)==(z#b) -> a=b.
Proof.
  intros a b z Hz_ne_0.
  unfold Qeq.
  rewrite Z.eq_sym_iff, <- Pos2Z.inj_iff.
  apply (Z.mul_reg_l _ _ _ Hz_ne_0).
Qed.

(** injection from Z is injective. *)

Lemma inject_Z_injective (a b: Z): inject_Z a == inject_Z b <-> a = b.
Proof.
 unfold Qeq; simpl; rewrite !Z.mul_1_r; reflexivity.
Qed.

(** Another approach : using Qcompare for defining order relations. *)

Definition Qcompare (p q : Q) := (Qnum p * QDen q ?= Qnum q * QDen p)%Z.
Notation "p ?= q" := (Qcompare p q) : Q_scope.

Lemma Qeq_alt p q : (p == q) <-> (p ?= q) = Eq.
Proof.
symmetry. apply Z.compare_eq_iff.
Qed.

Lemma Qlt_alt p q : (p<q) <-> (p?=q = Lt).
Proof.
reflexivity.
Qed.

Lemma Qgt_alt p q : (p>q) <-> (p?=q = Gt).
Proof.
symmetry. apply Z.gt_lt_iff.
Qed.

Lemma Qle_alt p q : (p<=q) <-> (p?=q <> Gt).
Proof.
reflexivity.
Qed.

Lemma Qge_alt p q : (p>=q) <-> (p?=q <> Lt).
Proof.
symmetry. apply Z.ge_le_iff.
Qed.

#[global]
Hint Unfold Qeq Qlt Qle : qarith.
#[global]
Hint Extern 5 (?X1 <> ?X2) => intro; discriminate: qarith.

Lemma Qcompare_antisym x y : CompOpp (x ?= y) = (y ?= x).
Proof.
 symmetry. apply Z.compare_antisym.
Qed.

Lemma Qcompare_spec x y : CompareSpec (x==y) (x<y) (y<x) (x ?= y).
Proof.
 unfold Qeq, Qlt, Qcompare. case Z.compare_spec; now constructor.
Qed.

(** * Properties of equality. *)

Theorem Qeq_refl x : x == x.
Proof.
 auto with qarith.
Qed.

Theorem Qeq_sym x y : x == y -> y == x.
Proof.
 auto with qarith.
Qed.

Theorem Qeq_trans x y z : x == y -> y == z -> x == z.
Proof.
unfold Qeq; intros XY YZ.
apply Z.mul_reg_r with (QDen y); [auto with qarith|].
now rewrite Z.mul_shuffle0, XY, Z.mul_shuffle0, YZ, Z.mul_shuffle0.
Qed.

#[global]
Hint Immediate Qeq_sym : qarith.
#[global]
Hint Resolve Qeq_refl Qeq_trans : qarith.

(** In a word, [Qeq] is a setoid equality. *)

#[global]
Instance Q_Setoid : Equivalence Qeq.
Proof. split; red; eauto with qarith. Qed.

(** Furthermore, this equality is decidable: *)

Theorem Qeq_dec x y : {x==y} + {~ x==y}.
Proof.
 apply Z.eq_dec.
Defined.

Definition Qeq_bool x y :=
  (Z.eqb (Qnum x * QDen y) (Qnum y * QDen x))%Z.

Definition Qle_bool x y :=
  (Z.leb (Qnum x * QDen y) (Qnum y * QDen x))%Z.

Lemma Qeq_bool_iff x y : Qeq_bool x y = true <-> x == y.
Proof. apply Z.eqb_eq. Qed.

Lemma Qeq_bool_eq x y : Qeq_bool x y = true -> x == y.
Proof.
  apply Qeq_bool_iff.
Qed.

Lemma Qeq_eq_bool x y : x == y -> Qeq_bool x y = true.
Proof.
  apply Qeq_bool_iff.
Qed.

Lemma Qeq_bool_neq x y : Qeq_bool x y = false -> ~ x == y.
Proof.
  rewrite <- Qeq_bool_iff. now intros ->.
Qed.

Lemma Qle_bool_iff x y : Qle_bool x y = true <-> x <= y.
Proof. apply Z.leb_le. Qed.

Lemma Qle_bool_imp_le x y : Qle_bool x y = true -> x <= y.
Proof.
  apply Qle_bool_iff.
Qed.

Theorem Qnot_eq_sym x y : ~x == y -> ~y == x.
Proof.
 auto with qarith.
Qed.

Lemma Qeq_bool_comm x y: Qeq_bool x y = Qeq_bool y x.
Proof.
 apply eq_true_iff_eq. rewrite !Qeq_bool_iff. now symmetry.
Qed.

Lemma Qeq_bool_refl x: Qeq_bool x x = true.
Proof.
  rewrite Qeq_bool_iff. now reflexivity.
Qed.

Lemma Qeq_bool_sym x y: Qeq_bool x y = true -> Qeq_bool y x = true.
Proof.
  rewrite !Qeq_bool_iff. now symmetry.
Qed.

Lemma Qeq_bool_trans x y z: Qeq_bool x y = true -> Qeq_bool y z = true -> Qeq_bool x z = true.
Proof.
  rewrite !Qeq_bool_iff; apply Qeq_trans.
Qed.

#[global]
Hint Resolve Qnot_eq_sym : qarith.

(** * Addition, multiplication and opposite *)

(** The addition, multiplication and opposite are defined
   in the straightforward way: *)

Definition Qplus (x y : Q) :=
  (Qnum x * QDen y + Qnum y * QDen x) # (Qden x * Qden y).

Definition Qmult (x y : Q) := (Qnum x * Qnum y) # (Qden x * Qden y).

Definition Qopp (x : Q) := (- Qnum x) # (Qden x).

Definition Qminus (x y : Q) := Qplus x (Qopp y).

Definition Qinv (x : Q) :=
  match Qnum x with
  | Z0 => 0#1
  | Zpos p => (QDen x)#p
  | Zneg p => (Zneg (Qden x))#p
  end.

Definition Qdiv (x y : Q) := Qmult x (Qinv y).

Infix "+" := Qplus : Q_scope.
Notation "- x" := (Qopp x) : Q_scope.
Infix "-" := Qminus : Q_scope.
Infix "*" := Qmult : Q_scope.
Notation "/ x" := (Qinv x) : Q_scope.
Infix "/" := Qdiv : Q_scope.

Register Qplus  as rat.Q.Qplus.
Register Qminus as rat.Q.Qminus.
Register Qopp   as rat.Q.Qopp.
Register Qmult  as rat.Q.Qmult.

(** Number notation for constants *)

Inductive IZ :=
  | IZpow_pos : Z -> positive -> IZ
  | IZ0 : IZ
  | IZpos : positive -> IZ
  | IZneg : positive -> IZ.

Inductive IQ :=
  | IQmake : IZ -> positive -> IQ
  | IQmult : IQ -> IQ -> IQ
  | IQdiv : IQ -> IQ -> IQ.

Definition IZ_of_Z z :=
  match z with
  | Z0 => IZ0
  | Zpos e => IZpos e
  | Zneg e => IZneg e
  end.

Definition IZ_to_Z z :=
  match z with
  | IZ0 => Some Z0
  | IZpos e => Some (Zpos e)
  | IZneg e => Some (Zneg e)
  | IZpow_pos _ _ => None
  end.

Definition of_decimal (d:Decimal.decimal) : IQ :=
  let '(i, f, e) :=
    match d with
    | Decimal.Decimal i f => (i, f, Decimal.Pos Decimal.Nil)
    | Decimal.DecimalExp i f e => (i, f, e)
    end in
  let num := Z.of_int (Decimal.app_int i f) in
  let den := Nat.iter (Decimal.nb_digits f) (Pos.mul 10) 1%positive in
  let q := IQmake (IZ_of_Z num) den in
  let e := Z.of_int e in
  match e with
  | Z0 => q
  | Zpos e => IQmult q (IQmake (IZpow_pos 10 e) 1)
  | Zneg e => IQdiv q (IQmake (IZpow_pos 10 e) 1)
  end.

Definition IQmake_to_decimal num den :=
  let num := Z.to_int num in
  let (den, e_den) := Decimal.nztail (Pos.to_uint den) in
  match den with
  | Decimal.D1 Decimal.Nil =>
    match e_den with
    | O => Some (Decimal.Decimal num Decimal.Nil)
    | ne =>
      let ai := Decimal.abs num in
      let ni := Decimal.nb_digits ai in
      if Nat.ltb ne ni then
        let i := Decimal.del_tail_int ne num in
        let f := Decimal.del_head (Nat.sub ni ne) ai in
        Some (Decimal.Decimal i f)
      else
        let z := match num with
          | Decimal.Pos _ => Decimal.Pos (Decimal.zero)
          | Decimal.Neg _ => Decimal.Neg (Decimal.zero) end in
        Some (Decimal.Decimal z (Nat.iter (Nat.sub ne ni) Decimal.D0 ai))
    end
  | _ => None
  end.

Definition IQmake_to_decimal' num den :=
  match IZ_to_Z num with
  | None => None
  | Some num => IQmake_to_decimal num den
  end.

Definition to_decimal (n : IQ) : option Decimal.decimal :=
  match n with
  | IQmake num den => IQmake_to_decimal' num den
  | IQmult (IQmake num den) (IQmake (IZpow_pos 10 e) 1) =>
    match IQmake_to_decimal' num den with
    | Some (Decimal.Decimal i f) =>
      Some (Decimal.DecimalExp i f (Pos.to_int e))
    | _ => None
    end
  | IQdiv (IQmake num den) (IQmake (IZpow_pos 10 e) 1) =>
    match IQmake_to_decimal' num den with
    | Some (Decimal.Decimal i f) =>
      Some (Decimal.DecimalExp i f (Decimal.Neg (Pos.to_uint e)))
    | _ => None
    end
  | _ => None
  end.

Definition of_hexadecimal (d:Hexadecimal.hexadecimal) : IQ :=
  let '(i, f, e) :=
    match d with
    | Hexadecimal.Hexadecimal i f => (i, f, Decimal.Pos Decimal.Nil)
    | Hexadecimal.HexadecimalExp i f e => (i, f, e)
    end in
  let num := Z.of_hex_int (Hexadecimal.app_int i f) in
  let den := Nat.iter (Hexadecimal.nb_digits f) (Pos.mul 16) 1%positive in
  let q := IQmake (IZ_of_Z num) den in
  let e := Z.of_int e in
  match e with
  | Z0 => q
  | Zpos e => IQmult q (IQmake (IZpow_pos 2 e) 1)
  | Zneg e => IQdiv q (IQmake (IZpow_pos 2 e) 1)
  end.

Definition IQmake_to_hexadecimal num den :=
  let num := Z.to_hex_int num in
  let (den, e_den) := Hexadecimal.nztail (Pos.to_hex_uint den) in
  match den with
  | Hexadecimal.D1 Hexadecimal.Nil =>
    match e_den with
    | O => Some (Hexadecimal.Hexadecimal num Hexadecimal.Nil)
    | ne =>
      let ai := Hexadecimal.abs num in
      let ni := Hexadecimal.nb_digits ai in
      if Nat.ltb ne ni then
        let i := Hexadecimal.del_tail_int ne num in
        let f := Hexadecimal.del_head (Nat.sub ni ne) ai in
        Some (Hexadecimal.Hexadecimal i f)
      else
        let z := match num with
          | Hexadecimal.Pos _ => Hexadecimal.Pos (Hexadecimal.zero)
          | Hexadecimal.Neg _ => Hexadecimal.Neg (Hexadecimal.zero) end in
        Some (Hexadecimal.Hexadecimal z (Nat.iter (Nat.sub ne ni) Hexadecimal.D0 ai))
    end
  | _ => None
  end.

Definition IQmake_to_hexadecimal' num den :=
  match IZ_to_Z num with
  | None => None
  | Some num => IQmake_to_hexadecimal num den
  end.

Definition to_hexadecimal (n : IQ) : option Hexadecimal.hexadecimal :=
  match n with
  | IQmake num den => IQmake_to_hexadecimal' num den
  | IQmult (IQmake num den) (IQmake (IZpow_pos 2 e) 1) =>
    match IQmake_to_hexadecimal' num den with
    | Some (Hexadecimal.Hexadecimal i f) =>
      Some (Hexadecimal.HexadecimalExp i f (Pos.to_int e))
    | _ => None
    end
  | IQdiv (IQmake num den) (IQmake (IZpow_pos 2 e) 1) =>
    match IQmake_to_hexadecimal' num den with
    | Some (Hexadecimal.Hexadecimal i f) =>
      Some (Hexadecimal.HexadecimalExp i f (Decimal.Neg (Pos.to_uint e)))
    | _ => None
    end
  | _ => None
  end.

Definition of_number (n : Number.number) : IQ :=
  match n with
  | Number.Decimal d => of_decimal d
  | Number.Hexadecimal h => of_hexadecimal h
  end.

Definition to_number (q:IQ) : option Number.number :=
  match to_decimal q with
  | None => None
  | Some q => Some (Number.Decimal q)
  end.

Definition to_hex_number q :=
  match to_hexadecimal q with
  | None => None
  | Some q => Some (Number.Hexadecimal q)
  end.

Number Notation Q of_number to_hex_number (via IQ
  mapping [Qmake => IQmake, Qmult => IQmult, Qdiv => IQdiv,
           Z.pow_pos => IZpow_pos, Z0 => IZ0, Zpos => IZpos, Zneg => IZneg])
  : hex_Q_scope.

Number Notation Q of_number to_number (via IQ
  mapping [Qmake => IQmake, Qmult => IQmult, Qdiv => IQdiv,
           Z.pow_pos => IZpow_pos, Z0 => IZ0, Zpos => IZpos, Zneg => IZneg])
  : Q_scope.

(** A light notation for [Zpos] *)

Lemma Qmake_Qdiv a b : a#b==inject_Z a/inject_Z (Zpos b).
Proof.
unfold Qeq. simpl. ring.
Qed.

(** * Setoid compatibility results *)

#[global]
Instance Qplus_comp : Proper (Qeq==>Qeq==>Qeq) Qplus.
Proof.
  unfold Qeq, Qplus; simpl.
  Open Scope Z_scope.
  intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
  simpl_mult; ring_simplify.
  replace (p1 * Zpos r2 * Zpos q2) with (p1 * Zpos q2 * Zpos r2) by ring.
  rewrite H.
  replace (r1 * Zpos p2 * Zpos q2 * Zpos s2) with (r1 * Zpos s2 * Zpos p2 * Zpos q2) by ring.
  rewrite H0.
  ring.
  Close Scope Z_scope.
Qed.

#[global]
Instance Qopp_comp : Proper (Qeq==>Qeq) Qopp.
Proof.
  unfold Qeq, Qopp; simpl.
  Open Scope Z_scope.
  intros x y H; simpl.
  replace (- Qnum x * Zpos (Qden y)) with (- (Qnum x * Zpos (Qden y))) by ring.
  rewrite H;  ring.
  Close Scope Z_scope.
Qed.

#[global]
Instance Qminus_comp : Proper (Qeq==>Qeq==>Qeq) Qminus.
Proof.
  intros x x' Hx y y' Hy.
  unfold Qminus. rewrite Hx, Hy; auto with qarith.
Qed.

#[global]
Instance Qmult_comp : Proper (Qeq==>Qeq==>Qeq) Qmult.
Proof.
  unfold Qeq; simpl.
  Open Scope Z_scope.
  intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
  intros; simpl_mult; ring_simplify.
  replace (q1 * s1 * Zpos p2) with (q1 * Zpos p2 * s1) by ring.
  rewrite <- H.
  replace (p1 * r1 * Zpos q2 * Zpos s2) with (r1 * Zpos s2 * p1 * Zpos q2) by ring.
  rewrite H0.
  ring.
  Close Scope Z_scope.
Qed.

#[global]
Instance Qinv_comp : Proper (Qeq==>Qeq) Qinv.
Proof.
  unfold Qeq, Qinv; simpl.
  Open Scope Z_scope.
  intros (p1, p2) (q1, q2) EQ; simpl in *.
  destruct q1; simpl in *.
  - apply Z.mul_eq_0 in EQ. destruct EQ; now subst.
  - destruct p1; simpl in *; try discriminate.
    now rewrite Pos.mul_comm, <- EQ, Pos.mul_comm.
  - destruct p1; simpl in *; try discriminate.
    now rewrite Pos.mul_comm, <- EQ, Pos.mul_comm.
  Close Scope Z_scope.
Qed.

#[global]
Instance Qdiv_comp : Proper (Qeq==>Qeq==>Qeq) Qdiv.
Proof.
  intros x x' Hx y y' Hy; unfold Qdiv.
  rewrite Hx, Hy; auto with qarith.
Qed.

#[global]
Instance Qcompare_comp : Proper (Qeq==>Qeq==>eq) Qcompare.
Proof.
  unfold Qeq, Qcompare.
  Open Scope Z_scope.
  intros (p1,p2) (q1,q2) H (r1,r2) (s1,s2) H'; simpl in *.
  rewrite <- (Zcompare.Zcompare_mult_compat (q2*s2) (p1*Zpos r2)).
  rewrite <- (Zcompare.Zcompare_mult_compat (p2*r2) (q1*Zpos s2)).
  change (Zpos (q2*s2)) with (Zpos q2 * Zpos s2).
  change (Zpos (p2*r2)) with (Zpos p2 * Zpos r2).
  replace (Zpos q2 * Zpos s2 * (p1*Zpos r2)) with ((p1*Zpos q2)*Zpos r2*Zpos s2) by ring.
  rewrite H.
  replace (Zpos q2 * Zpos s2 * (r1*Zpos p2)) with ((r1*Zpos s2)*Zpos q2*Zpos p2) by ring.
  rewrite H'.
  f_equal; ring.
  Close Scope Z_scope.
Qed.

#[global]
Instance Qle_comp : Proper (Qeq==>Qeq==>iff) Qle.
Proof.
  intros p q H r s H'. rewrite 2 Qle_alt, H, H'; auto with *.
Qed.

#[global]
Instance Qlt_compat : Proper (Qeq==>Qeq==>iff) Qlt.
Proof.
  intros p q H r s H'. rewrite 2 Qlt_alt, H, H'; auto with *.
Qed.

#[global]
Instance Qeqb_comp : Proper (Qeq==>Qeq==>eq) Qeq_bool.
Proof.
 intros p q H r s H'; apply eq_true_iff_eq.
 rewrite 2 Qeq_bool_iff, H, H'; split; auto with qarith.
Qed.

#[global]
Instance Qleb_comp : Proper (Qeq==>Qeq==>eq) Qle_bool.
Proof.
 intros p q H r s H'; apply eq_true_iff_eq.
 rewrite 2 Qle_bool_iff, H, H'; split; auto with qarith.
Qed.


(** [0] and [1] are apart *)

Lemma Q_apart_0_1 : ~ 1 == 0.
Proof.
  unfold Qeq; auto with qarith.
Qed.

(** * Properties of [Qadd] *)

(** Addition is associative: *)

Theorem Qplus_assoc : forall x y z, x+(y+z)==(x+y)+z.
Proof.
  intros (x1, x2) (y1, y2) (z1, z2).
  unfold Qeq, Qplus; simpl; simpl_mult; ring.
Qed.

(** [0] is a neutral element for addition: *)

Lemma Qplus_0_l : forall x, 0+x == x.
Proof.
  intros (x1, x2); unfold Qeq, Qplus; simpl; ring.
Qed.

Lemma Qplus_0_r : forall x, x+0 == x.
Proof.
  intros (x1, x2); unfold Qeq, Qplus; simpl.
  rewrite Pos.mul_comm; simpl; ring.
Qed.

(** Commutativity of addition: *)

Theorem Qplus_comm : forall x y, x+y == y+x.
Proof.
  intros (x1, x2); unfold Qeq, Qplus; simpl.
  intros; rewrite Pos.mul_comm; ring.
Qed.


(** * Properties of [Qopp] *)

Lemma Qopp_involutive : forall q, - -q == q.
Proof.
  red; simpl; intros; ring.
Qed.

Theorem Qplus_opp_r : forall q, q+(-q) == 0.
Proof.
  red; simpl; intro; ring.
Qed.

(** Injectivity of addition (uses theory about Qopp above): *)

Lemma Qplus_inj_r (x y z: Q):
  x + z == y + z <-> x == y.
Proof.
 split; intro E.
 - rewrite <- (Qplus_0_r x), <- (Qplus_0_r y).
   rewrite <- (Qplus_opp_r z); auto.
   do 2 rewrite Qplus_assoc.
   rewrite E. reflexivity.
 - rewrite E. reflexivity.
Qed.

Lemma Qplus_inj_l (x y z: Q):
  z + x == z + y <-> x == y.
Proof.
 rewrite (Qplus_comm z x), (Qplus_comm z y).
 apply Qplus_inj_r.
Qed.


(** * Properties of [Qmult] *)

(** Multiplication is associative: *)

Theorem Qmult_assoc : forall n m p, n*(m*p)==(n*m)*p.
Proof.
  intros; red; simpl; rewrite Pos.mul_assoc; ring.
Qed.

(** multiplication and zero *)

Lemma Qmult_0_l : forall x , 0*x == 0.
Proof.
  intros; compute; reflexivity.
Qed.

Lemma Qmult_0_r : forall x , x*0 == 0.
Proof.
  intros; red; simpl; ring.
Qed.

(** [1] is a neutral element for multiplication: *)

Lemma Qmult_1_l : forall n, 1*n == n.
Proof.
  intro n; red; simpl; destruct (Qnum n); auto.
Qed.

Theorem Qmult_1_r : forall n, n*1==n.
Proof.
  intro n; red; simpl.
  rewrite (Z.mul_1_r (Qnum n)).
  rewrite Pos.mul_comm; simpl; trivial.
Qed.

(** Commutativity of multiplication *)

Theorem Qmult_comm : forall x y, x*y==y*x.
Proof.
  intros; red; simpl; rewrite Pos.mul_comm; ring.
Qed.

(** Distributivity over [Qadd] *)

Theorem Qmult_plus_distr_r : forall x y z, x*(y+z)==(x*y)+(x*z).
Proof.
  intros (x1, x2) (y1, y2) (z1, z2).
  unfold Qeq, Qmult, Qplus; simpl; simpl_mult; ring.
Qed.

Theorem Qmult_plus_distr_l : forall x y z, (x+y)*z==(x*z)+(y*z).
Proof.
  intros (x1, x2) (y1, y2) (z1, z2).
  unfold Qeq, Qmult, Qplus; simpl; simpl_mult; ring.
Qed.

(** Integrality *)

Theorem Qmult_integral : forall x y, x*y==0 -> x==0 \/ y==0.
Proof.
  intros (x1,x2) (y1,y2).
  unfold Qeq, Qmult; simpl.
  now rewrite <- Z.mul_eq_0, !Z.mul_1_r.
Qed.

Theorem Qmult_integral_l : forall x y, ~ x == 0 -> x*y == 0 -> y == 0.
Proof.
  intros (x1, x2) (y1, y2).
  unfold Qeq, Qmult; simpl.
  rewrite !Z.mul_1_r, Z.mul_eq_0. intuition.
Qed.


(** * inject_Z is a ring homomorphism: *)

Lemma inject_Z_plus (x y: Z): inject_Z (x + y) = inject_Z x + inject_Z y.
Proof.
 unfold Qplus, inject_Z. simpl. f_equal. ring.
Qed.

Lemma inject_Z_mult (x y: Z): inject_Z (x * y) = inject_Z x * inject_Z y.
Proof. reflexivity. Qed.

Lemma inject_Z_opp (x: Z): inject_Z (- x) = - inject_Z x.
Proof. reflexivity. Qed.


(** * Inverse and division. *)

Lemma Qinv_involutive : forall q, (/ / q) == q.
Proof.
intros [[|n|n] d]; red; simpl; reflexivity.
Qed.

Theorem Qmult_inv_r : forall x, ~ x == 0 -> x*(/x) == 1.
Proof.
  intros (x1, x2); unfold Qeq, Qdiv, Qmult; case x1; simpl;
    intros H **; simpl_mult; try ring.
  elim H; auto.
Qed.

Lemma Qinv_mult_distr : forall p q, / (p * q) == /p * /q.
Proof.
  intros (x1,x2) (y1,y2); unfold Qeq, Qinv, Qmult; simpl.
  destruct x1; simpl; auto;
    destruct y1; simpl; auto.
Qed.

Lemma Qinv_pos: forall (a b : positive),
  / (Z.pos b # a) == Z.pos a # b.
Proof.
  intros a b.
  reflexivity.
Qed.

Lemma Qinv_neg: forall (a b : positive),
  / (Z.neg b # a) == Z.neg a # b.
Proof.
  intros a b.
  reflexivity.
Qed.

Theorem Qdiv_mult_l : forall x y, ~ y == 0 -> (x*y)/y == x.
Proof.
  intros x y H; unfold Qdiv.
  rewrite <- (Qmult_assoc x y (Qinv y)).
  rewrite (Qmult_inv_r y H).
  apply Qmult_1_r.
Qed.

Theorem Qmult_div_r : forall x y, ~ y == 0 -> y*(x/y) == x.
Proof.
  intros x y ?; unfold Qdiv.
  rewrite (Qmult_assoc y x (Qinv y)).
  rewrite (Qmult_comm y x).
  fold (Qdiv (Qmult x y) y).
  apply Qdiv_mult_l; auto.
Qed.

Lemma Qinv_plus_distr : forall a b c, ((a # c) + (b # c) == (a+b) # c)%Q.
Proof.
  intros. unfold Qeq. simpl. rewrite Pos2Z.inj_mul. ring.
Qed.

Lemma Qinv_minus_distr : forall a b c, (a # c) + - (b # c) == (a-b) # c.
Proof.
  intros. unfold Qeq. simpl. rewrite Pos2Z.inj_mul. ring.
Qed.

(** Injectivity of Qmult (requires theory about Qinv above): *)

Lemma Qmult_inj_r (x y z: Q): ~ z == 0 -> (x * z == y * z <-> x == y).
Proof.
 intro z_ne_0.
 split; intro E.
 - rewrite <- (Qmult_1_r x), <- (Qmult_1_r y).
   rewrite <- (Qmult_inv_r z); auto.
   do 2 rewrite Qmult_assoc.
   rewrite E. reflexivity.
 - rewrite E. reflexivity.
Qed.

Lemma Qmult_inj_l (x y z: Q): ~ z == 0 -> (z * x == z * y <-> x == y).
Proof.
 rewrite (Qmult_comm z x), (Qmult_comm z y).
 apply Qmult_inj_r.
Qed.

(** * Reduction and construction of Q *)

(** ** Removal/introduction of common factor in both numerator and denominator. *)

Lemma Qreduce_l : forall (a : Z) (b z : positive),
  (Zpos z)*a # z*b == a#b.
Proof.
  intros a b z.
  unfold Qeq, Qnum, Qden.
  rewrite Pos2Z.inj_mul.
  ring.
Qed.

Lemma Qreduce_r : forall (a : Z) (b z : positive),
  a*(Zpos z) # b*z == a#b.
Proof.
  intros a b z.
  unfold Qeq, Qnum, Qden.
  rewrite Pos2Z.inj_mul.
  ring.
Qed.

Lemma Qreduce_num_l : forall (a b : positive),
  Z.pos a # a * b == (1 # b).
Proof.
  intros a b.
  unfold Qeq, Qnum, Qden.
  rewrite Pos2Z.inj_mul.
  ring.
Qed.

Lemma Qreduce_num_r : forall (a b : positive),
  Z.pos b # a * b == (1 # a).
Proof.
  intros a b.
  unfold Qeq, Qnum, Qden.
  rewrite Pos2Z.inj_mul.
  ring.
Qed.

Lemma Qreduce_den_l : forall (a : positive) (b : Z),
  Z.pos a * b # a == (b # 1).
Proof.
  intros a b.
  unfold Qeq, Qnum, Qden.
  ring.
Qed.

Lemma Qreduce_den_r : forall (a : Z) (b : positive),
  a * Z.pos b # b == (a # 1).
Proof.
  intros a b.
  unfold Qeq, Qnum, Qden.
  ring.
Qed.

Lemma Qreduce_den_inject_Z_l : forall (a : positive) (b : Z),
  (Z.pos a * b # a == inject_Z b)%Q.
Proof.
  intros a b.
  unfold Qeq, Qnum, Qden, inject_Z.
  ring.
Qed.

Lemma Qreduce_den_inject_Z_r : forall (a : Z) (b : positive),
  a * Z.pos b # b == inject_Z a.
Proof.
  intros a b.
  unfold Qeq, Qnum, Qden, inject_Z.
  ring.
Qed.

Lemma Qreduce_zero: forall (d : positive),
  (0#d == 0)%Q.
Proof.
  intros d.
  unfold Qeq, Qnum, Qden; reflexivity.
Qed.

(** ** Construction of a new rational by multiplication with an integer or pure fraction *)

(** (or to be more precise multiplication with a rational of the form z/1 or 1/p) *)

Lemma Qmult_inject_Z_l : forall (a : Z) (b : positive) (z : Z),
  (inject_Z z) * (a#b) == z*a#b.
Proof.
  intros a b z.
  unfold Qeq. cbn. ring.
Qed.

Lemma Qmult_inject_Z_r : forall (a : Z) (b : positive) (z : Z),
  (a#b) * inject_Z z == a*z#b.
Proof.
  intros a b z.
  unfold Qeq. cbn.
  rewrite Pos2Z.inj_mul.
  ring.
Qed.

Lemma Qmult_frac_l : forall (a:Z) (b c:positive), (a # (b * c)) == (1#b) * (a#c).
Proof.
  intros a b c.
  unfold Qeq, Qnum, Qden; cbn.
  destruct a; reflexivity.
Qed.

Lemma Qmult_frac_r : forall (a:Z) (b c:positive), (a # (b * c)) == (a#b) * (1#c).
Proof.
  intros a b c.
  unfold Qeq, Qnum, Qden; cbn.
  rewrite Pos2Z.inj_mul.
  ring.
Qed.

(** * Properties of order upon Q. *)

Lemma Qle_refl x : x<=x.
Proof.
  unfold Qle; reflexivity.
Qed.

Lemma Qle_antisym x y : x<=y -> y<=x -> x==y.
Proof. apply Z.le_antisymm. Qed.

Lemma Qle_trans : forall x y z, x<=y -> y<=z -> x<=z.
Proof.
  unfold Qle; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
  Open Scope Z_scope.
  apply Z.mul_le_mono_pos_r with (Zpos y2); [easy|].
  apply Z.le_trans with (y1 * Zpos x2 * Zpos z2).
  - rewrite Z.mul_shuffle0. now apply Z.mul_le_mono_pos_r.
  - rewrite Z.mul_shuffle0, (Z.mul_shuffle0 z1).
    now apply Z.mul_le_mono_pos_r.
  Close Scope Z_scope.
Qed.

#[global]
Hint Resolve Qle_trans : qarith.

Lemma Qlt_irrefl x : ~x<x.
Proof. apply Z.lt_irrefl. Qed.

Lemma Qlt_not_eq x y : x<y -> ~ x==y.
Proof. apply Z.lt_neq. Qed.

Lemma Zle_Qle (x y: Z): (x <= y)%Z = (inject_Z x <= inject_Z y).
Proof.
 unfold Qle. simpl. now rewrite !Z.mul_1_r.
Qed.

Lemma Zlt_Qlt (x y: Z): (x < y)%Z = (inject_Z x < inject_Z y).
Proof.
 unfold Qlt. simpl. now rewrite !Z.mul_1_r.
Qed.


(** Large = strict or equal *)

Lemma Qle_lteq x y : x<=y <-> x<y \/ x==y.
Proof.
 rewrite Qeq_alt, Qle_alt, Qlt_alt.
 destruct (x ?= y); intuition; discriminate.
Qed.

Lemma Qlt_leneq: forall p q : Q, p < q <-> p <= q /\ ~ (p == q).
Proof.
  intros p q; split; intros H.
  - rewrite Qlt_alt in H; rewrite Qle_alt, Qeq_alt.
    rewrite H; split; intros H1; inversion H1.
  - rewrite Qlt_alt; rewrite Qle_alt, Qeq_alt in H.
    destruct (p ?= q); tauto.
Qed.

Lemma Qlt_le_weak x y : x<y -> x<=y.
Proof. apply Z.lt_le_incl. Qed.

(** Qgt and Qge are just a notations, but one might not know this and search for these lemmas *)

Lemma Qgt_lt: forall p q : Q, p > q -> q < p.
Proof.
  intros p q H; assumption.
Qed.

Lemma Qlt_gt: forall p q : Q, p < q -> q > p.
Proof.
  intros p q H; assumption.
Qed.

Lemma Qge_le: forall p q : Q, p >= q -> q <= p.
Proof.
  intros p q H; assumption.
Qed.

Lemma Qle_ge: forall p q : Q, p <= q -> q >= p.
Proof.
  intros p q H; assumption.
Qed.

Lemma Qle_lt_trans : forall x y z, x<=y -> y<z -> x<z.
Proof.
  unfold Qle, Qlt; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
  Open Scope Z_scope.
  apply Z.mul_lt_mono_pos_r with (Zpos y2); [easy|].
  apply Z.le_lt_trans with (y1 * Zpos x2 * Zpos z2).
  - rewrite Z.mul_shuffle0. now apply Z.mul_le_mono_pos_r.
  - rewrite Z.mul_shuffle0, (Z.mul_shuffle0 z1).
    now apply Z.mul_lt_mono_pos_r.
  Close Scope Z_scope.
Qed.

Lemma Qlt_le_trans : forall x y z, x<y -> y<=z -> x<z.
Proof.
  unfold Qle, Qlt; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
  Open Scope Z_scope.
  apply Z.mul_lt_mono_pos_r with (Zpos y2); [easy|].
  apply Z.lt_le_trans with (y1 * Zpos x2 * Zpos z2).
  - rewrite Z.mul_shuffle0. now apply Z.mul_lt_mono_pos_r.
  - rewrite Z.mul_shuffle0, (Z.mul_shuffle0 z1).
    now apply Z.mul_le_mono_pos_r.
  Close Scope Z_scope.
Qed.

Lemma Qlt_trans : forall x y z, x<y -> y<z -> x<z.
Proof.
  intros x y z ? ?.
  apply Qle_lt_trans with y; auto.
  apply Qlt_le_weak; auto.
Qed.

(** [x<y] iff [~(y<=x)] *)

Lemma Qnot_lt_le x y : ~ x < y -> y <= x.
Proof. apply Z.nlt_ge. Qed.

Lemma Qnot_le_lt x y : ~ x <= y -> y < x.
Proof. apply Z.nle_gt. Qed.

Lemma Qlt_not_le x y : x < y -> ~ y <= x.
Proof. apply Z.lt_nge. Qed.

Lemma Qle_not_lt x y : x <= y -> ~ y < x.
Proof. apply Z.le_ngt. Qed.

Lemma Qle_lt_or_eq : forall x y, x<=y -> x<y \/ x==y.
Proof.
  unfold Qle, Qlt, Qeq; intros; now apply Z.lt_eq_cases.
Qed.

#[global]
Hint Resolve Qle_not_lt Qlt_not_le Qnot_le_lt Qnot_lt_le
 Qlt_le_weak Qlt_not_eq Qle_antisym Qle_refl: qarith.

(** ** Some decidability results about orders. *)

Lemma Q_dec : forall x y, {x<y} + {y<x} + {x==y}.
Proof.
  unfold Qlt, Qle, Qeq; intros x y.
  exact (ZArith_dec.Z_dec' (Qnum x * QDen y) (Qnum y * QDen x)).
Defined.

Lemma Qlt_le_dec : forall x y, {x<y} + {y<=x}.
Proof.
  unfold Qlt, Qle; intros x y.
  exact (ZArith_dec.Z_lt_le_dec (Qnum x * QDen y) (Qnum y * QDen x)).
Defined.

Lemma Qarchimedean : forall q : Q, { p : positive | q < Z.pos p # 1 }.
Proof.
  intros q. destruct q as [a b]. destruct a as [|p|p].
  - exists xH. reflexivity.
  - exists (p+1)%positive. apply (Z.lt_le_trans _ (Z.pos (p+1))).
    + simpl. rewrite Pos.mul_1_r.
      apply Z.lt_succ_diag_r.
    + simpl. rewrite Pos2Z.inj_mul.
      rewrite <- (Zmult_1_r (Z.pos (p+1))). apply Z.mul_le_mono_nonneg.
      * discriminate.
      * rewrite Zmult_1_r. apply Z.le_refl.
      * discriminate.
      * apply Pos2Z.pos_le_pos, Pos.le_1_l.
  - exists xH. reflexivity.
Defined.

(** ** Compatibility of addition with order *)

Lemma Qopp_le_compat : forall p q, p<=q -> -q <= -p.
Proof.
  intros (a1,a2) (b1,b2); unfold Qle, Qlt; simpl.
  now rewrite !Z.mul_opp_l, <- Z.opp_le_mono.
Qed.

Lemma Qopp_lt_compat: forall p q : Q, p < q -> - q < - p.
Proof.
  intros (a1,a2) (b1,b2); unfold Qle, Qlt; simpl.
  now rewrite !Z.mul_opp_l, <- Z.opp_lt_mono.
Qed.

#[global]
Hint Resolve Qopp_le_compat Qopp_lt_compat : qarith.

Lemma Qle_minus_iff : forall p q, p <= q <-> 0 <= q+-p.
Proof.
  intros (x1,x2) (y1,y2); unfold Qle; simpl.
  rewrite Z.mul_1_r, Z.mul_opp_l, <- Z.le_sub_le_add_r, Z.opp_involutive.
  reflexivity.
Qed.

Lemma Qlt_minus_iff : forall p q, p < q <-> 0 < q+-p.
Proof.
  intros (x1,x2) (y1,y2); unfold Qlt; simpl.
  rewrite Z.mul_1_r, Z.mul_opp_l, <- Z.lt_sub_lt_add_r, Z.opp_involutive.
  reflexivity.
Qed.

Lemma Qplus_le_compat :
  forall x y z t, x<=y -> z<=t -> x+z <= y+t.
Proof.
  unfold Qplus, Qle; intros (x1, x2) (y1, y2) (z1, z2) (t1, t2);
    simpl; simpl_mult.
  Open Scope Z_scope.
  intros.
  match goal with |- ?a <= ?b => ring_simplify a b end.
  rewrite Z.add_comm.
  apply Z.add_le_mono.
  - match goal with |- ?a <= ?b => ring_simplify z1 t1 (Zpos z2) (Zpos t2) a b end.
    auto using Z.mul_le_mono_nonneg_r, Pos2Z.is_nonneg.
  - match goal with |- ?a <= ?b => ring_simplify x1 y1 (Zpos x2) (Zpos y2) a b end.
    auto using Z.mul_le_mono_nonneg_r, Pos2Z.is_nonneg.
    Close Scope Z_scope.
Qed.

Lemma Qplus_lt_le_compat :
  forall x y z t, x<y -> z<=t -> x+z < y+t.
Proof.
  unfold Qplus, Qle, Qlt; intros (x1, x2) (y1, y2) (z1, z2) (t1, t2);
    simpl; simpl_mult.
  Open Scope Z_scope.
  intros.
  match goal with |- ?a < ?b => ring_simplify a b end.
  rewrite Z.add_comm.
  apply Z.add_le_lt_mono.
  - match goal with |- ?a <= ?b => ring_simplify z1 t1 (Zpos z2) (Zpos t2) a b end.
    auto using Z.mul_le_mono_nonneg_r, Pos2Z.is_nonneg.
  - match goal with |- ?a < ?b => ring_simplify x1 y1 (Zpos x2) (Zpos y2) a b end.
    do 2 (apply Z.mul_lt_mono_pos_r;try easy).
    Close Scope Z_scope.
Qed.

Lemma Qplus_le_l (x y z: Q): x + z <= y + z <-> x <= y.
Proof.
 split; intros.
 - rewrite <- (Qplus_0_r x), <- (Qplus_0_r y), <- (Qplus_opp_r z).
   do 2 rewrite Qplus_assoc.
   apply Qplus_le_compat; auto with *.
 - apply Qplus_le_compat; auto with *.
Qed.

Lemma Qplus_le_r (x y z: Q): z + x <= z + y <-> x <= y.
Proof.
 rewrite (Qplus_comm z x), (Qplus_comm z y).
 apply Qplus_le_l.
Qed.

Lemma Qplus_lt_l (x y z: Q): x + z < y + z <-> x < y.
Proof.
 split; intros.
 - rewrite <- (Qplus_0_r x), <- (Qplus_0_r y), <- (Qplus_opp_r z).
   do 2 rewrite Qplus_assoc.
   apply Qplus_lt_le_compat; auto with *.
 - apply Qplus_lt_le_compat; auto with *.
Qed.

Lemma Qplus_lt_r (x y z: Q): z + x < z + y <-> x < y.
Proof.
 rewrite (Qplus_comm z x), (Qplus_comm z y).
 apply Qplus_lt_l.
Qed.

Lemma Qplus_lt_compat : forall x y z t : Q,
  x < y -> z < t -> x + z < y + t.
Proof.
  intros x y z t H1 H2.
  apply Qplus_lt_le_compat.
  - assumption.
  - apply Qle_lteq; left; assumption.
Qed.

(** ** Compatibility of multiplication with order. *)

Lemma Qmult_le_compat_r : forall x y z, x <= y -> 0 <= z -> x*z <= y*z.
Proof.
  intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
  Open Scope Z_scope.
  rewrite Z.mul_1_r.
  intros; simpl_mult.
  rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b1).
  apply Z.mul_le_mono_nonneg_r; auto.
  now apply Z.mul_nonneg_nonneg.
  Close Scope Z_scope.
Qed.

Lemma Qmult_lt_0_le_reg_r : forall x y z, 0 < z  -> x*z <= y*z -> x <= y.
Proof.
  intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
  Open Scope Z_scope.
  simpl_mult.
  rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b1).
  rewrite Z.mul_1_r.
  intros LT LE.
  apply Z.mul_le_mono_pos_r in LE; trivial.
  apply Z.mul_pos_pos; easy.
  Close Scope Z_scope.
Qed.

Lemma Qmult_le_r (x y z: Q): 0 < z -> (x*z <= y*z <-> x <= y).
Proof.
 split; intro.
 - now apply Qmult_lt_0_le_reg_r with z.
 - apply Qmult_le_compat_r; auto with qarith.
Qed.

Lemma Qmult_le_l (x y z: Q): 0 < z -> (z*x <= z*y <-> x <= y).
Proof.
 rewrite (Qmult_comm z x), (Qmult_comm z y).
 apply Qmult_le_r.
Qed.

Lemma Qmult_lt_compat_r : forall x y z, 0 < z  -> x < y -> x*z < y*z.
Proof.
  intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
  Open Scope Z_scope.
  rewrite Z.mul_1_r.
  intros; simpl_mult.
  rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b1).
  apply Z.mul_lt_mono_pos_r; auto with zarith.
  apply Z.mul_pos_pos; easy.
  Close Scope Z_scope.
Qed.

Lemma Qmult_lt_r: forall x y z, 0 < z -> (x*z < y*z <-> x < y).
Proof.
 Open Scope Z_scope.
 intros (a1,a2) (b1,b2) (c1,c2).
 unfold Qle, Qlt; simpl.
 simpl_mult.
 rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b1).
 rewrite Z.mul_1_r.
 intro LT. rewrite <- Z.mul_lt_mono_pos_r.
 - reflexivity.
 - now apply Z.mul_pos_pos.
   Close Scope Z_scope.
Qed.

Lemma Qmult_lt_l (x y z: Q): 0 < z -> (z*x < z*y <-> x < y).
Proof.
 rewrite (Qmult_comm z x), (Qmult_comm z y).
 apply Qmult_lt_r.
Qed.

Lemma Qmult_le_0_compat : forall a b, 0 <= a -> 0 <= b -> 0 <= a*b.
Proof.
intros a b Ha Hb.
unfold Qle in *.
simpl in *.
rewrite Z.mul_1_r in *.
auto using Z.mul_nonneg_nonneg.
Qed.

Lemma Qmult_lt_0_compat : forall a b : Q, 0 < a -> 0 < b -> 0 < a * b.
Proof.
  intros a b Ha Hb.
  destruct a,b. unfold Qlt, Qmult, QArith_base.Qnum, QArith_base.Qden in *.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_0_l, Z.mul_1_r in *.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma Qmult_le_1_compat: forall a b : Q, 1 <= a -> 1 <= b -> 1 <= a * b.
Proof.
  intros a b Ha Hb.
  destruct a,b. unfold Qle, Qmult, QArith_base.Qnum, QArith_base.Qden in *.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_1_l, Z.mul_1_r in *.
  apply Z.mul_le_mono_nonneg.
  2,4: assumption.
  1,2: apply Pos2Z.is_nonneg.
Qed.

Lemma Qmult_lt_1_compat: forall a b : Q, 1 < a -> 1 < b -> 1 < a * b.
Proof.
  intros a b Ha Hb.
  destruct a,b. unfold Qlt, Qmult, QArith_base.Qnum, QArith_base.Qden in *.
  rewrite Pos2Z.inj_mul.
  rewrite Z.mul_1_l, Z.mul_1_r in *.
  apply Z.mul_lt_mono_nonneg.
  2,4: assumption.
  1,2: apply Pos2Z.is_nonneg.
Qed.

Lemma Qmult_lt_compat_nonneg: forall x y z t : Q, 0 <= x < y -> 0 <= z < t -> x * z < y * t.
Proof.
  intros [xn xd] [yn yd] [zn zd] [tn td] [H0lex Hxlty] [H0lez Hzltt].
  unfold Qmult, Qlt, Qle, Qnum, Qden in *.
  rewrite Z.mul_0_l,Z.mul_1_r in H0lex, H0lez.
  do 2 rewrite Pos2Z.inj_mul.
  setoid_replace (xn * zn * (Z.pos yd * Z.pos td))%Z with ((xn * Z.pos yd) * (zn * Z.pos td))%Z by ring.
  setoid_replace (yn * tn * (Z.pos xd * Z.pos zd))%Z with ((yn * Z.pos xd) * (tn * Z.pos zd))%Z by ring.
  apply Z.mul_lt_mono_nonneg.
  2,4 : assumption.
  1,2 : rewrite <- (Z.mul_0_l 0); apply Z.mul_le_mono_nonneg;
          [reflexivity|assumption|reflexivity|apply Pos2Z.is_nonneg].
Qed.

Lemma Qmult_le_lt_compat_pos: forall x y z t : Q, 0 < x <= y -> 0 < z < t -> x * z < y * t.
Proof.
  intros [xn xd] [yn yd] [zn zd] [tn td] [H0ltx Hxlty] [H0ltz Hzltt].
  unfold Qmult, Qlt, Qle, Qnum, Qden in *.
  rewrite Z.mul_0_l,Z.mul_1_r in H0ltx, H0ltz.
  do 2 rewrite Pos2Z.inj_mul.
  setoid_replace (xn * zn * (Z.pos yd * Z.pos td))%Z with ((xn * Z.pos yd) * (zn * Z.pos td))%Z by ring.
  setoid_replace (yn * tn * (Z.pos xd * Z.pos zd))%Z with ((yn * Z.pos xd) * (tn * Z.pos zd))%Z by ring.
  apply Zorder.Zmult_lt_compat2; split.
  2,4 : assumption.
  1,2 : rewrite <- (Z.mul_0_l 0); apply Z.mul_lt_mono_nonneg;
          [reflexivity|assumption|reflexivity|apply Pos2Z.is_pos].
Qed.

Lemma Qmult_le_compat_nonneg: forall x y z t : Q, 0 <= x <= y -> 0 <= z <= t -> x * z <= y * t.
Proof.
  intros [xn xd] [yn yd] [zn zd] [tn td] [H0lex Hxlty] [H0lez Hzltt].
  unfold Qmult, Qlt, Qle, Qnum, Qden in *.
  rewrite Z.mul_0_l,Z.mul_1_r in H0lex, H0lez.
  do 2 rewrite Pos2Z.inj_mul.
  setoid_replace (xn * zn * (Z.pos yd * Z.pos td))%Z with ((xn * Z.pos yd) * (zn * Z.pos td))%Z by ring.
  setoid_replace (yn * tn * (Z.pos xd * Z.pos zd))%Z with ((yn * Z.pos xd) * (tn * Z.pos zd))%Z by ring.
  apply Z.mul_le_mono_nonneg.
  2,4 : assumption.
  1,2 : rewrite <- (Z.mul_0_l 0); apply Z.mul_le_mono_nonneg;
          [reflexivity|assumption|reflexivity|apply Pos2Z.is_nonneg].
Qed.

(** ** Compatibility of inversion and division with order *)

Lemma Qinv_le_0_compat : forall a, 0 <= a -> 0 <= /a.
Proof.
intros [[|n|n] d] Ha; assumption.
Qed.

Lemma Qle_shift_div_l : forall a b c,
 0 < c -> a*c <= b -> a <= b/c.
Proof.
intros a b c Hc H.
apply Qmult_lt_0_le_reg_r with (c).
- assumption.
- setoid_replace (b/c*c) with (c*(b/c)) by apply Qmult_comm.
  rewrite Qmult_div_r; try assumption.
  auto with *.
Qed.

Lemma Qle_shift_inv_l : forall a c,
 0 < c -> a*c <= 1 -> a <= /c.
Proof.
intros a c Hc H.
setoid_replace (/c) with (1*/c) by (symmetry; apply Qmult_1_l).
change (a <= 1/c).
apply Qle_shift_div_l; assumption.
Qed.

Lemma Qle_shift_div_r : forall a b c,
 0 < b -> a <= c*b -> a/b <= c.
Proof.
intros a b c Hc H.
apply Qmult_lt_0_le_reg_r with b.
- assumption.
- setoid_replace (a/b*b) with (b*(a/b)) by apply Qmult_comm.
  rewrite Qmult_div_r; try assumption.
  auto with *.
Qed.

Lemma Qle_shift_inv_r : forall b c,
 0 < b -> 1 <= c*b -> /b <= c.
Proof.
intros b c Hc H.
setoid_replace (/b) with (1*/b) by (symmetry; apply Qmult_1_l).
change (1/b <= c).
apply Qle_shift_div_r; assumption.
Qed.

Lemma Qinv_lt_0_compat : forall a, 0 < a -> 0 < /a.
Proof.
intros [[|n|n] d] Ha; assumption.
Qed.

Lemma Qlt_shift_div_l : forall a b c,
 0 < c -> a*c < b -> a < b/c.
Proof.
intros a b c Hc H.
apply Qnot_le_lt.
intros H0.
apply (Qlt_not_le _ _ H).
apply Qmult_lt_0_le_reg_r with (/c).
- apply Qinv_lt_0_compat.
  assumption.
- setoid_replace (a*c/c) with (a) by (apply Qdiv_mult_l; auto with *).
  assumption.
Qed.

Lemma Qlt_shift_inv_l : forall a c,
 0 < c -> a*c < 1 -> a < /c.
Proof.
intros a c Hc H.
setoid_replace (/c) with (1*/c) by (symmetry; apply Qmult_1_l).
change (a < 1/c).
apply Qlt_shift_div_l; assumption.
Qed.

Lemma Qlt_shift_div_r : forall a b c,
 0 < b -> a < c*b -> a/b < c.
Proof.
intros a b c Hc H.
apply Qnot_le_lt.
intros H0.
apply (Qlt_not_le _ _ H).
apply Qmult_lt_0_le_reg_r with (/b).
- apply Qinv_lt_0_compat.
  assumption.
- setoid_replace (c*b/b) with (c) by (apply Qdiv_mult_l; auto with *).
  assumption.
Qed.

Lemma Qlt_shift_inv_r : forall b c,
 0 < b -> 1 < c*b -> /b < c.
Proof.
intros b c Hc H.
setoid_replace (/b) with (1*/b) by (symmetry; apply Qmult_1_l).
change (1/b < c).
apply Qlt_shift_div_r; assumption.
Qed.

Lemma Qinv_lt_contravar : forall a b : Q,
    0 < a -> 0 < b -> (a < b <-> /b < /a).
Proof.
  intros a b H H0. split.
  - intro H1. rewrite <- Qmult_1_l. apply Qlt_shift_div_r.
    + apply H0.
    + rewrite <- (Qmult_inv_r a).
      * rewrite Qmult_comm.
        apply Qmult_lt_l.
        -- apply Qinv_lt_0_compat.  apply H.
        -- apply H1.
      * intro abs. rewrite abs in H. apply (Qlt_irrefl 0 H).
  - intro H1. rewrite <- (Qinv_involutive b). rewrite <- (Qmult_1_l (// b)).
    apply Qlt_shift_div_l.
    + apply Qinv_lt_0_compat. apply H0.
    + rewrite <- (Qmult_inv_r a).
      * apply Qmult_lt_l.
        -- apply H.
        -- apply H1.
      * intro abs. rewrite abs in H. apply (Qlt_irrefl 0 H).
Qed.


(** * Rational to the n-th power *)

Definition Qpower_positive : Q -> positive -> Q :=
 pow_pos Qmult.

#[global]
Instance Qpower_positive_comp : Proper (Qeq==>eq==>Qeq) Qpower_positive.
Proof.
intros x x' Hx y y' Hy. rewrite <-Hy; clear y' Hy.
unfold Qpower_positive.
induction y as [y IHy|y IHy|]; simpl;
try rewrite IHy;
try rewrite Hx;
reflexivity.
Qed.

Definition Qpower (q:Q) (z:Z) :=
    match z with
      | Zpos p => Qpower_positive q p
      | Z0 => 1
      | Zneg p => /Qpower_positive q p
    end.

Notation " q ^ z " := (Qpower q z) : Q_scope.

Register Qpower as  rat.Q.Qpower.

#[global]
Instance Qpower_comp : Proper (Qeq==>eq==>Qeq) Qpower.
Proof.
intros x x' Hx y y' Hy. rewrite <- Hy; clear y' Hy.
destruct y; simpl; rewrite ?Hx; auto with *.
Qed.
