(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Import ZArith.
Require Import BigNumPrelude.
Require Import NSig.
Require Import ZSig.

Open Scope Z_scope.

(** * ZMake

  A generic transformation from a structure of natural numbers
  [NSig.NType] to a structure of integers [ZSig.ZType].
*)

Module Make (N:NType) <: ZType.

 Inductive t_ :=
  | Pos : N.t -> t_
  | Neg : N.t -> t_.

 Definition t := t_.

 Definition zero := Pos N.zero.
 Definition one  := Pos N.one.
 Definition minus_one := Neg N.one.

 Definition of_Z x :=
  match x with
  | Zpos x => Pos (N.of_N (Npos x))
  | Z0 => zero
  | Zneg x => Neg (N.of_N (Npos x))
  end.

 Definition to_Z x :=
  match x with
  | Pos nx => N.to_Z nx
  | Neg nx => Zopp (N.to_Z nx)
  end.

 Theorem spec_of_Z: forall x, to_Z (of_Z x) = x.
 Proof.
 intros x; case x; unfold to_Z, of_Z, zero.
   exact N.spec_0.
   intros; rewrite N.spec_of_N; auto.
   intros; rewrite N.spec_of_N; auto.
 Qed.

 Definition eq x y := (to_Z x = to_Z y).

 Theorem spec_0: to_Z zero = 0.
 exact N.spec_0.
 Qed.

 Theorem spec_1: to_Z one = 1.
 exact N.spec_1.
 Qed.

 Theorem spec_m1: to_Z minus_one = -1.
 simpl; rewrite N.spec_1; auto.
 Qed.

 Definition compare x y :=
  match x, y with
  | Pos nx, Pos ny => N.compare nx ny
  | Pos nx, Neg ny =>
    match N.compare nx N.zero with
    | Gt => Gt
    | _ => N.compare ny N.zero
    end
  | Neg nx, Pos ny =>
    match N.compare N.zero nx with
    | Lt => Lt
    | _ => N.compare N.zero ny
    end
  | Neg nx, Neg ny => N.compare ny nx
  end.

 Theorem spec_compare :
  forall x y, compare x y = Zcompare (to_Z x) (to_Z y).
 Proof.
 unfold compare, to_Z.
 destruct x as [x|x], y as [y|y];
 rewrite ?N.spec_compare, ?N.spec_0, <-?Zcompare_opp; auto;
 assert (Hx:=N.spec_pos x); assert (Hy:=N.spec_pos y);
 set (X:=N.to_Z x) in *; set (Y:=N.to_Z y) in *; clearbody X Y.
 destruct (Zcompare_spec X 0) as [EQ|LT|GT].
  rewrite EQ. rewrite <- Zopp_0 at 2. apply Zcompare_opp.
  exfalso. omega.
  symmetry. change (X > -Y). omega.
 destruct (Zcompare_spec 0 X) as [EQ|LT|GT].
  rewrite <- EQ. rewrite Zopp_0; auto.
  symmetry. change (-X < Y). omega.
  exfalso. omega.
 Qed.

 Definition eq_bool x y :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

 Theorem spec_eq_bool:
  forall x y, eq_bool x y = Zeq_bool (to_Z x) (to_Z y).
 Proof.
 unfold eq_bool, Zeq_bool; intros; rewrite spec_compare; reflexivity.
 Qed.

 Definition lt n m := to_Z n < to_Z m.
 Definition le n m := to_Z n <= to_Z m.

 Definition min n m := match compare n m with Gt => m | _ => n end.
 Definition max n m := match compare n m with Lt => m | _ => n end.

 Theorem spec_min : forall n m, to_Z (min n m) = Zmin (to_Z n) (to_Z m).
 Proof.
 unfold min, Zmin. intros. rewrite spec_compare. destruct Zcompare; auto.
 Qed.

 Theorem spec_max : forall n m, to_Z (max n m) = Zmax (to_Z n) (to_Z m).
 Proof.
 unfold max, Zmax. intros. rewrite spec_compare. destruct Zcompare; auto.
 Qed.

 Definition to_N x :=
  match x with
  | Pos nx => nx
  | Neg nx => nx
  end.

 Definition abs x := Pos (to_N x).

 Theorem spec_abs: forall x, to_Z (abs x) = Zabs (to_Z x).
 Proof.
 intros x; case x; clear x; intros x; assert (F:=N.spec_pos x).
    simpl; rewrite Zabs_eq; auto.
 simpl; rewrite Zabs_non_eq; simpl; auto with zarith.
 Qed.

 Definition opp x :=
  match x with
  | Pos nx => Neg nx
  | Neg nx => Pos nx
  end.

 Theorem spec_opp: forall x, to_Z (opp x) = - to_Z x.
 Proof.
 intros x; case x; simpl; auto with zarith.
 Qed.

 Definition succ x :=
  match x with
  | Pos n => Pos (N.succ n)
  | Neg n =>
    match N.compare N.zero n with
    | Lt => Neg (N.pred n)
    | _ => one
    end
  end.

 Theorem spec_succ: forall n, to_Z (succ n) = to_Z n + 1.
 Proof.
 intros x; case x; clear x; intros x.
   exact (N.spec_succ x).
 simpl. rewrite N.spec_compare. case Zcompare_spec; rewrite ?N.spec_0; simpl.
  intros HH; rewrite <- HH; rewrite N.spec_1; ring.
  intros HH; rewrite N.spec_pred, Zmax_r; auto with zarith.
 generalize (N.spec_pos x); auto with zarith.
 Qed.

 Definition add x y :=
  match x, y with
  | Pos nx, Pos ny => Pos (N.add nx ny)
  | Pos nx, Neg ny =>
    match N.compare nx ny with
    | Gt => Pos (N.sub nx ny)
    | Eq => zero
    | Lt => Neg (N.sub ny nx)
    end
  | Neg nx, Pos ny =>
    match N.compare nx ny with
    | Gt => Neg (N.sub nx ny)
    | Eq => zero
    | Lt => Pos (N.sub ny nx)
    end
  | Neg nx, Neg ny => Neg (N.add nx ny)
  end.

 Theorem spec_add: forall x y, to_Z (add x y) = to_Z x +  to_Z y.
 Proof.
 unfold add, to_Z; intros [x | x] [y | y];
   try (rewrite N.spec_add; auto with zarith);
 rewrite N.spec_compare; case Zcompare_spec;
  unfold zero; rewrite ?N.spec_0, ?N.spec_sub; omega with *.
 Qed.

 Definition pred x :=
  match x with
  | Pos nx =>
    match N.compare N.zero nx with
    | Lt => Pos (N.pred nx)
    | _ => minus_one
    end
  | Neg nx => Neg (N.succ nx)
  end.

 Theorem spec_pred: forall x, to_Z (pred x) = to_Z x - 1.
 Proof.
 unfold pred, to_Z, minus_one; intros [x | x];
   try (rewrite N.spec_succ; ring).
 rewrite N.spec_compare; case Zcompare_spec;
  rewrite ?N.spec_0, ?N.spec_1, ?N.spec_pred;
  generalize (N.spec_pos x); omega with *.
 Qed.

 Definition sub x y :=
  match x, y with
  | Pos nx, Pos ny =>
    match N.compare nx ny with
    | Gt => Pos (N.sub nx ny)
    | Eq => zero
    | Lt => Neg (N.sub ny nx)
    end
  | Pos nx, Neg ny => Pos (N.add nx ny)
  | Neg nx, Pos ny => Neg (N.add nx ny)
  | Neg nx, Neg ny =>
    match N.compare nx ny with
    | Gt => Neg (N.sub nx ny)
    | Eq => zero
    | Lt => Pos (N.sub ny nx)
    end
  end.

 Theorem spec_sub: forall x y, to_Z (sub x y) = to_Z x - to_Z y.
 Proof.
 unfold sub, to_Z; intros [x | x] [y | y];
  try (rewrite N.spec_add; auto with zarith);
 rewrite N.spec_compare; case Zcompare_spec;
  unfold zero; rewrite ?N.spec_0, ?N.spec_sub; omega with *.
 Qed.

 Definition mul x y :=
  match x, y with
  | Pos nx, Pos ny => Pos (N.mul nx ny)
  | Pos nx, Neg ny => Neg (N.mul nx ny)
  | Neg nx, Pos ny => Neg (N.mul nx ny)
  | Neg nx, Neg ny => Pos (N.mul nx ny)
  end.

 Theorem spec_mul: forall x y, to_Z (mul x y) = to_Z x * to_Z y.
 Proof.
 unfold mul, to_Z; intros [x | x] [y | y]; rewrite N.spec_mul; ring.
 Qed.

 Definition square x :=
  match x with
  | Pos nx => Pos (N.square nx)
  | Neg nx => Pos (N.square nx)
  end.

 Theorem spec_square: forall x, to_Z (square x) = to_Z x *  to_Z x.
 Proof.
 unfold square, to_Z; intros [x | x]; rewrite N.spec_square; ring.
 Qed.

 Definition power_pos x p :=
  match x with
  | Pos nx => Pos (N.power_pos nx p)
  | Neg nx =>
    match p with
    | xH => x
    | xO _ => Pos (N.power_pos nx p)
    | xI _ => Neg (N.power_pos nx p)
    end
  end.

 Theorem spec_power_pos: forall x n, to_Z (power_pos x n) = to_Z x ^ Zpos n.
 Proof.
 assert (F0: forall x, (-x)^2 = x^2).
   intros x; rewrite Zpower_2; ring.
 unfold power_pos, to_Z; intros [x | x] [p | p |];
   try rewrite N.spec_power_pos; try ring.
 assert (F: 0 <= 2 * Zpos p).
  assert (0 <= Zpos p); auto with zarith.
 rewrite Zpos_xI; repeat rewrite Zpower_exp; auto with zarith.
 repeat rewrite Zpower_mult; auto with zarith.
 rewrite F0; ring.
 assert (F: 0 <= 2 * Zpos p).
  assert (0 <= Zpos p); auto with zarith.
 rewrite Zpos_xO; repeat rewrite Zpower_exp; auto with zarith.
 repeat rewrite Zpower_mult; auto with zarith.
 rewrite F0; ring.
 Qed.

 Definition power x n :=
  match n with
  | N0 => one
  | Npos p => power_pos x p
  end.

 Theorem spec_power: forall x n, to_Z (power x n) = to_Z x ^ Z_of_N n.
 Proof.
 destruct n; simpl. rewrite N.spec_1; reflexivity.
 apply spec_power_pos.
 Qed.


 Definition sqrt x :=
  match x with
  | Pos nx => Pos (N.sqrt nx)
  | Neg nx => Neg N.zero
  end.

 Theorem spec_sqrt: forall x, 0 <= to_Z x ->
   to_Z (sqrt x) ^ 2 <= to_Z x < (to_Z (sqrt x) + 1) ^ 2.
 Proof.
 unfold to_Z, sqrt; intros [x | x] H.
   exact (N.spec_sqrt x).
 replace (N.to_Z x) with 0.
   rewrite N.spec_0; simpl Zpower; unfold Zpower_pos, iter_pos;
    auto with zarith.
 generalize (N.spec_pos x); auto with zarith.
 Qed.

 Definition div_eucl x y :=
  match x, y with
  | Pos nx, Pos ny =>
    let (q, r) := N.div_eucl nx ny in
    (Pos q, Pos r)
  | Pos nx, Neg ny =>
    let (q, r) := N.div_eucl nx ny in
    if N.eq_bool N.zero r
    then (Neg q, zero)
    else (Neg (N.succ q), Neg (N.sub ny r))
  | Neg nx, Pos ny =>
    let (q, r) := N.div_eucl nx ny in
    if N.eq_bool N.zero r
    then (Neg q, zero)
    else (Neg (N.succ q), Pos (N.sub ny r))
  | Neg nx, Neg ny =>
    let (q, r) := N.div_eucl nx ny in
    (Pos q, Neg r)
  end.

 Ltac break_nonneg x px EQx :=
  let H := fresh "H" in
  assert (H:=N.spec_pos x);
  destruct (N.to_Z x) as [|px|px]_eqn:EQx;
   [clear H|clear H|elim H; reflexivity].

 Theorem spec_div_eucl: forall x y,
   let (q,r) := div_eucl x y in
   (to_Z q, to_Z r) = Zdiv_eucl (to_Z x) (to_Z y).
 Proof.
 unfold div_eucl, to_Z. intros [x | x] [y | y].
 (* Pos Pos *)
 generalize (N.spec_div_eucl x y); destruct (N.div_eucl x y); auto.
 (* Pos Neg *)
 generalize (N.spec_div_eucl x y); destruct (N.div_eucl x y) as (q,r).
 break_nonneg x px EQx; break_nonneg y py EQy;
 try (injection 1; intros Hr Hq; rewrite N.spec_eq_bool, N.spec_0, Hr;
      simpl; rewrite Hq, N.spec_0; auto).
 change (- Zpos py) with (Zneg py).
 assert (GT : Zpos py > 0) by (compute; auto).
 generalize (Z_div_mod (Zpos px) (Zpos py) GT).
 unfold Zdiv_eucl. destruct (Zdiv_eucl_POS px (Zpos py)) as (q',r').
 intros (EQ,MOD). injection 1. intros Hr' Hq'.
 rewrite N.spec_eq_bool, N.spec_0, Hr'.
 break_nonneg r pr EQr.
 subst; simpl. rewrite N.spec_0; auto.
 subst. lazy iota beta delta [Zeq_bool Zcompare].
 rewrite N.spec_sub, N.spec_succ, EQy, EQr. f_equal. omega with *.
 (* Neg Pos *)
 generalize (N.spec_div_eucl x y); destruct (N.div_eucl x y) as (q,r).
 break_nonneg x px EQx; break_nonneg y py EQy;
 try (injection 1; intros Hr Hq; rewrite N.spec_eq_bool, N.spec_0, Hr;
      simpl; rewrite Hq, N.spec_0; auto).
 change (- Zpos px) with (Zneg px).
 assert (GT : Zpos py > 0) by (compute; auto).
 generalize (Z_div_mod (Zpos px) (Zpos py) GT).
 unfold Zdiv_eucl. destruct (Zdiv_eucl_POS px (Zpos py)) as (q',r').
 intros (EQ,MOD). injection 1. intros Hr' Hq'.
 rewrite N.spec_eq_bool, N.spec_0, Hr'.
 break_nonneg r pr EQr.
 subst; simpl. rewrite N.spec_0; auto.
 subst. lazy iota beta delta [Zeq_bool Zcompare].
 rewrite N.spec_sub, N.spec_succ, EQy, EQr. f_equal. omega with *.
 (* Neg Neg *)
 generalize (N.spec_div_eucl x y); destruct (N.div_eucl x y) as (q,r).
 break_nonneg x px EQx; break_nonneg y py EQy;
 try (injection 1; intros Hr Hq; rewrite Hr, Hq; auto).
 simpl. intros <-; auto.
 Qed.

 Definition div x y := fst (div_eucl x y).

 Definition spec_div: forall x y,
     to_Z (div x y) = to_Z x / to_Z y.
 Proof.
 intros x y; generalize (spec_div_eucl x y); unfold div, Zdiv.
 case div_eucl; case Zdiv_eucl; simpl; auto.
 intros q r q11 r1 H; injection H; auto.
 Qed.

 Definition modulo x y := snd (div_eucl x y).

 Theorem spec_modulo:
   forall x y, to_Z (modulo x y) = to_Z x mod to_Z y.
 Proof.
 intros x y; generalize (spec_div_eucl x y); unfold modulo, Zmod.
 case div_eucl; case Zdiv_eucl; simpl; auto.
 intros q r q11 r1 H; injection H; auto.
 Qed.

 Definition gcd x y :=
  match x, y with
  | Pos nx, Pos ny => Pos (N.gcd nx ny)
  | Pos nx, Neg ny => Pos (N.gcd nx ny)
  | Neg nx, Pos ny => Pos (N.gcd nx ny)
  | Neg nx, Neg ny => Pos (N.gcd nx ny)
  end.

 Theorem spec_gcd: forall a b, to_Z (gcd a b) = Zgcd (to_Z a) (to_Z b).
 Proof.
 unfold gcd, Zgcd, to_Z; intros [x | x] [y | y]; rewrite N.spec_gcd; unfold Zgcd;
  auto; case N.to_Z; simpl; auto with zarith;
  try rewrite Zabs_Zopp; auto;
  case N.to_Z; simpl; auto with zarith.
 Qed.

 Definition sgn x :=
  match compare zero x with
   | Lt => one
   | Eq => zero
   | Gt => minus_one
  end.

 Lemma spec_sgn : forall x, to_Z (sgn x) = Zsgn (to_Z x).
 Proof.
 intros. unfold sgn. rewrite spec_compare. case Zcompare_spec.
 rewrite spec_0. intros <-; auto.
 rewrite spec_0, spec_1. symmetry. rewrite Zsgn_pos; auto.
 rewrite spec_0, spec_m1. symmetry. rewrite Zsgn_neg; auto with zarith.
 Qed.

End Make.
