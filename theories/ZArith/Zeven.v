(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import BinInt.

(**********************************************************************)
(** About parity: even and odd predicates on Z, division by 2 on Z *)

(**********************************************************************)
(** [Zeven], [Zodd], [Zdiv2] and their related properties *)

Definition Zeven (z:Z) :=
  match z with
  | Z0 => True
  | Zpos (xO _) => True
  | Zneg (xO _) => True
  | _ => False
  end.

Definition Zodd (z:Z) :=
  match z with
  | Zpos xH => True
  | Zneg xH => True
  | Zpos (xI _) => True
  | Zneg (xI _) => True
  | _ => False
  end.

Definition Zeven_bool (z:Z) :=
  match z with
  | Z0 => true
  | Zpos (xO _) => true
  | Zneg (xO _) => true
  | _ => false
  end.

Definition Zodd_bool (z:Z) :=
  match z with
  | Z0 => false
  | Zpos (xO _) => false
  | Zneg (xO _) => false
  | _ => true
  end.

Definition Zeven_odd_dec : forall z:Z, {Zeven z} + {Zodd z}.
Proof.
  intro z. case z;
  [ left; compute in |- *; trivial
  | intro p; case p; intros;
     (right; compute in |- *; exact I) || (left; compute in |- *; exact I)
  | intro p; case p; intros;
     (right; compute in |- *; exact I) || (left; compute in |- *; exact I) ].
Defined.

Definition Zeven_dec : forall z:Z, {Zeven z} + {~ Zeven z}.
Proof.
  intro z. case z;
  [ left; compute in |- *; trivial
  | intro p; case p; intros;
     (left; compute in |- *; exact I) || (right; compute in |- *; trivial)
  | intro p; case p; intros;
     (left; compute in |- *; exact I) || (right; compute in |- *; trivial) ].
Defined.

Definition Zodd_dec : forall z:Z, {Zodd z} + {~ Zodd z}.
Proof.
  intro z. case z;
  [ right; compute in |- *; trivial
  | intro p; case p; intros;
     (left; compute in |- *; exact I) || (right; compute in |- *; trivial)
  | intro p; case p; intros;
     (left; compute in |- *; exact I) || (right; compute in |- *; trivial) ].
Defined.

Lemma Zeven_not_Zodd : forall n:Z, Zeven n -> ~ Zodd n.
Proof.
  intro z; destruct z; [ idtac | destruct p | destruct p ]; compute in |- *;
   trivial.
Qed.

Lemma Zodd_not_Zeven : forall n:Z, Zodd n -> ~ Zeven n.
Proof.
  intro z; destruct z; [ idtac | destruct p | destruct p ]; compute in |- *;
   trivial.
Qed.

Lemma Zeven_Sn : forall n:Z, Zodd n -> Zeven (Zsucc n).
Proof.
 intro z; destruct z; unfold Zsucc in |- *;
  [ idtac | destruct p | destruct p ]; simpl in |- *; 
  trivial. 
 unfold Pdouble_minus_one in |- *; case p; simpl in |- *; auto.
Qed.

Lemma Zodd_Sn : forall n:Z, Zeven n -> Zodd (Zsucc n).
Proof.
 intro z; destruct z; unfold Zsucc in |- *;
  [ idtac | destruct p | destruct p ]; simpl in |- *; 
  trivial. 
 unfold Pdouble_minus_one in |- *; case p; simpl in |- *; auto.
Qed.

Lemma Zeven_pred : forall n:Z, Zodd n -> Zeven (Zpred n).
Proof.
 intro z; destruct z; unfold Zpred in |- *;
  [ idtac | destruct p | destruct p ]; simpl in |- *; 
  trivial. 
 unfold Pdouble_minus_one in |- *; case p; simpl in |- *; auto.
Qed.

Lemma Zodd_pred : forall n:Z, Zeven n -> Zodd (Zpred n).
Proof.
 intro z; destruct z; unfold Zpred in |- *;
  [ idtac | destruct p | destruct p ]; simpl in |- *; 
  trivial. 
 unfold Pdouble_minus_one in |- *; case p; simpl in |- *; auto.
Qed.

Hint Unfold Zeven Zodd: zarith.

(**********************************************************************)
(** [Zdiv2] is defined on all [Z], but notice that for odd negative
    integers it is not the euclidean quotient: in that case we have [n =
    2*(n/2)-1] *)

Definition Zdiv2 (z:Z) :=
  match z with
  | Z0 => 0%Z
  | Zpos xH => 0%Z
  | Zpos p => Zpos (Pdiv2 p)
  | Zneg xH => 0%Z
  | Zneg p => Zneg (Pdiv2 p)
  end.

Lemma Zeven_div2 : forall n:Z, Zeven n -> n = (2 * Zdiv2 n)%Z.
Proof.
intro x; destruct x.
auto with arith.
destruct p; auto with arith.
intros. absurd (Zeven (Zpos (xI p))); red in |- *; auto with arith.
intros. absurd (Zeven 1); red in |- *; auto with arith.
destruct p; auto with arith.
intros. absurd (Zeven (Zneg (xI p))); red in |- *; auto with arith.
intros. absurd (Zeven (-1)); red in |- *; auto with arith.
Qed.

Lemma Zodd_div2 : forall n:Z, (n >= 0)%Z -> Zodd n -> n = (2 * Zdiv2 n + 1)%Z.
Proof.
intro x; destruct x.
intros. absurd (Zodd 0); red in |- *; auto with arith.
destruct p; auto with arith.
intros. absurd (Zodd (Zpos (xO p))); red in |- *; auto with arith.
intros. absurd (Zneg p >= 0)%Z; red in |- *; auto with arith.
Qed.

Lemma Zodd_div2_neg :
 forall n:Z, (n <= 0)%Z -> Zodd n -> n = (2 * Zdiv2 n - 1)%Z.
Proof.
intro x; destruct x.
intros. absurd (Zodd 0); red in |- *; auto with arith.
intros. absurd (Zneg p >= 0)%Z; red in |- *; auto with arith.
destruct p; auto with arith.
intros. absurd (Zodd (Zneg (xO p))); red in |- *; auto with arith.
Qed.

Lemma Z_modulo_2 :
 forall n:Z, {y : Z | n = (2 * y)%Z} + {y : Z | n = (2 * y + 1)%Z}.
Proof.
intros x.
elim (Zeven_odd_dec x); intro.
left. split with (Zdiv2 x). exact (Zeven_div2 x a).
right. generalize b; clear b; case x.
intro b; inversion b.
intro p; split with (Zdiv2 (Zpos p)). apply (Zodd_div2 (Zpos p)); trivial.
unfold Zge, Zcompare in |- *; simpl in |- *; discriminate.
intro p; split with (Zdiv2 (Zpred (Zneg p))).
pattern (Zneg p) at 1 in |- *; rewrite (Zsucc_pred (Zneg p)).
pattern (Zpred (Zneg p)) at 1 in |- *; rewrite (Zeven_div2 (Zpred (Zneg p))).
reflexivity.
apply Zeven_pred; assumption.
Qed.

Lemma Zsplit2 :
 forall n:Z,
   {p : Z * Z |
   let (x1, x2) := p in n = (x1 + x2)%Z /\ (x1 = x2 \/ x2 = (x1 + 1)%Z)}.
Proof.
intros x.
elim (Z_modulo_2 x); intros [y Hy]; rewrite Zmult_comm in Hy;
 rewrite <- Zplus_diag_eq_mult_2 in Hy.
exists (y, y); split. 
assumption.
left; reflexivity.
exists (y, (y + 1)%Z); split.
rewrite Zplus_assoc; assumption.
right; reflexivity.
Qed.