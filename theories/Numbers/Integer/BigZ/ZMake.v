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

 Bind Scope abstract_scope with t t_.

 Definition zero := Pos N.zero.
 Definition one  := Pos N.one.
 Definition two := Pos N.two.
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

 Theorem spec_2: to_Z two = 2.
 exact N.spec_2.
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

 Definition eqb x y :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

 Theorem spec_eqb x y : eqb x y = Z.eqb (to_Z x) (to_Z y).
 Proof.
 apply Bool.eq_iff_eq_true.
 unfold eqb. rewrite Z.eqb_eq, <- Z.compare_eq_iff, spec_compare.
 split; [now destruct Z.compare | now intros ->].
 Qed.

 Definition lt n m := to_Z n < to_Z m.
 Definition le n m := to_Z n <= to_Z m.


 Definition ltb (x y : t) : bool :=
  match compare x y with
  | Lt => true
  | _  => false
  end.

 Theorem spec_ltb x y : ltb x y = Z.ltb (to_Z x) (to_Z y).
 Proof.
 apply Bool.eq_iff_eq_true.
 rewrite Z.ltb_lt. unfold Z.lt, ltb. rewrite spec_compare.
 split; [now destruct Z.compare | now intros ->].
 Qed.

 Definition leb (x y : t) : bool :=
  match compare x y with
  | Gt => false
  | _  => true
  end.

 Theorem spec_leb x y : leb x y = Z.leb (to_Z x) (to_Z y).
 Proof.
 apply Bool.eq_iff_eq_true.
 rewrite Z.leb_le. unfold Z.le, leb. rewrite spec_compare.
 destruct Z.compare; split; try easy. now destruct 1.
 Qed.

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

 Definition pow_pos x p :=
  match x with
  | Pos nx => Pos (N.pow_pos nx p)
  | Neg nx =>
    match p with
    | xH => x
    | xO _ => Pos (N.pow_pos nx p)
    | xI _ => Neg (N.pow_pos nx p)
    end
  end.

 Theorem spec_pow_pos: forall x n, to_Z (pow_pos x n) = to_Z x ^ Zpos n.
 Proof.
 assert (F0: forall x, (-x)^2 = x^2).
   intros x; rewrite Zpower_2; ring.
 unfold pow_pos, to_Z; intros [x | x] [p | p |];
   try rewrite N.spec_pow_pos; try ring.
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

 Definition pow_N x n :=
  match n with
  | N0 => one
  | Npos p => pow_pos x p
  end.

 Theorem spec_pow_N: forall x n, to_Z (pow_N x n) = to_Z x ^ Z_of_N n.
 Proof.
 destruct n; simpl. apply N.spec_1.
 apply spec_pow_pos.
 Qed.

 Definition pow x y :=
  match to_Z y with
  | Z0 => one
  | Zpos p => pow_pos x p
  | Zneg p => zero
  end.

 Theorem spec_pow: forall x y, to_Z (pow x y) = to_Z x ^ to_Z y.
 Proof.
 intros. unfold pow. destruct (to_Z y); simpl.
 apply N.spec_1.
 apply spec_pow_pos.
 apply N.spec_0.
 Qed.

 Definition log2 x :=
  match x with
  | Pos nx => Pos (N.log2 nx)
  | Neg nx => zero
  end.

 Theorem spec_log2: forall x, to_Z (log2 x) = Z.log2 (to_Z x).
 Proof.
  intros. destruct x as [p|p]; simpl. apply N.spec_log2.
  rewrite N.spec_0.
  destruct (Z_le_lt_eq_dec _ _ (N.spec_pos p)) as [LT|EQ].
  rewrite Z.log2_nonpos; auto with zarith.
  now rewrite <- EQ.
 Qed.

 Definition sqrt x :=
  match x with
  | Pos nx => Pos (N.sqrt nx)
  | Neg nx => Neg N.zero
  end.

 Theorem spec_sqrt: forall x, to_Z (sqrt x) = Z.sqrt (to_Z x).
 Proof.
  destruct x as [p|p]; simpl.
  apply N.spec_sqrt.
  rewrite N.spec_0.
  destruct (Z_le_lt_eq_dec _ _ (N.spec_pos p)) as [LT|EQ].
  rewrite Z.sqrt_neg; auto with zarith.
  now rewrite <- EQ.
 Qed.

 Definition div_eucl x y :=
  match x, y with
  | Pos nx, Pos ny =>
    let (q, r) := N.div_eucl nx ny in
    (Pos q, Pos r)
  | Pos nx, Neg ny =>
    let (q, r) := N.div_eucl nx ny in
    if N.eqb N.zero r
    then (Neg q, zero)
    else (Neg (N.succ q), Neg (N.sub ny r))
  | Neg nx, Pos ny =>
    let (q, r) := N.div_eucl nx ny in
    if N.eqb N.zero r
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
 try (injection 1; intros Hr Hq; rewrite N.spec_eqb, N.spec_0, Hr;
      simpl; rewrite Hq, N.spec_0; auto).
 change (- Zpos py) with (Zneg py).
 assert (GT : Zpos py > 0) by (compute; auto).
 generalize (Z_div_mod (Zpos px) (Zpos py) GT).
 unfold Zdiv_eucl. destruct (Zdiv_eucl_POS px (Zpos py)) as (q',r').
 intros (EQ,MOD). injection 1. intros Hr' Hq'.
 rewrite N.spec_eqb, N.spec_0, Hr'.
 break_nonneg r pr EQr.
 subst; simpl. rewrite N.spec_0; auto.
 subst. lazy iota beta delta [Z.eqb].
 rewrite N.spec_sub, N.spec_succ, EQy, EQr. f_equal. omega with *.
 (* Neg Pos *)
 generalize (N.spec_div_eucl x y); destruct (N.div_eucl x y) as (q,r).
 break_nonneg x px EQx; break_nonneg y py EQy;
 try (injection 1; intros Hr Hq; rewrite N.spec_eqb, N.spec_0, Hr;
      simpl; rewrite Hq, N.spec_0; auto).
 change (- Zpos px) with (Zneg px).
 assert (GT : Zpos py > 0) by (compute; auto).
 generalize (Z_div_mod (Zpos px) (Zpos py) GT).
 unfold Zdiv_eucl. destruct (Zdiv_eucl_POS px (Zpos py)) as (q',r').
 intros (EQ,MOD). injection 1. intros Hr' Hq'.
 rewrite N.spec_eqb, N.spec_0, Hr'.
 break_nonneg r pr EQr.
 subst; simpl. rewrite N.spec_0; auto.
 subst. lazy iota beta delta [Z.eqb].
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

 Definition quot x y :=
  match x, y with
  | Pos nx, Pos ny => Pos (N.div nx ny)
  | Pos nx, Neg ny => Neg (N.div nx ny)
  | Neg nx, Pos ny => Neg (N.div nx ny)
  | Neg nx, Neg ny => Pos (N.div nx ny)
  end.

 Definition rem x y :=
  if eqb y zero then x
  else
    match x, y with
      | Pos nx, Pos ny => Pos (N.modulo nx ny)
      | Pos nx, Neg ny => Pos (N.modulo nx ny)
      | Neg nx, Pos ny => Neg (N.modulo nx ny)
      | Neg nx, Neg ny => Neg (N.modulo nx ny)
    end.

 Lemma spec_quot : forall x y, to_Z (quot x y) = (to_Z x) ÷ (to_Z y).
 Proof.
  intros [x|x] [y|y]; simpl; symmetry; rewrite N.spec_div;
  (* Nota: we rely here on [forall a b, a ÷ 0 = b / 0] *)
  destruct (Z.eq_dec (N.to_Z y) 0) as [EQ|NEQ];
    try (rewrite EQ; now destruct (N.to_Z x));
  rewrite ?Z.quot_opp_r, ?Z.quot_opp_l, ?Z.opp_involutive, ?Z.opp_inj_wd;
  trivial; apply Z.quot_div_nonneg;
   generalize (N.spec_pos x) (N.spec_pos y); Z.order.
 Qed.

 Lemma spec_rem : forall x y,
   to_Z (rem x y) = Z.rem (to_Z x) (to_Z y).
 Proof.
  intros x y. unfold rem. rewrite spec_eqb, spec_0.
  case Z.eqb_spec; intros Hy.
  (* Nota: we rely here on [Z.rem a 0 = a] *)
  rewrite Hy. now destruct (to_Z x).
  destruct x as [x|x], y as [y|y]; simpl in *; symmetry;
   rewrite ?Z.eq_opp_l, ?Z.opp_0 in Hy;
   rewrite N.spec_modulo, ?Z.rem_opp_r, ?Z.rem_opp_l, ?Z.opp_involutive,
    ?Z.opp_inj_wd;
   trivial; apply Z.rem_mod_nonneg;
    generalize (N.spec_pos x) (N.spec_pos y); Z.order.
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

 Definition even z :=
  match z with
   | Pos n => N.even n
   | Neg n => N.even n
  end.

 Definition odd z :=
  match z with
   | Pos n => N.odd n
   | Neg n => N.odd n
  end.

 Lemma spec_even : forall z, even z = Zeven_bool (to_Z z).
 Proof.
  intros [n|n]; simpl; rewrite N.spec_even; trivial.
  destruct (N.to_Z n) as [|p|p]; now try destruct p.
 Qed.

 Lemma spec_odd : forall z, odd z = Zodd_bool (to_Z z).
 Proof.
  intros [n|n]; simpl; rewrite N.spec_odd; trivial.
  destruct (N.to_Z n) as [|p|p]; now try destruct p.
 Qed.

 Definition norm_pos z :=
   match z with
     | Pos _ => z
     | Neg n => if N.eqb n N.zero then Pos n else z
   end.

 Definition testbit a n :=
   match norm_pos n, norm_pos a with
     | Pos p, Pos a => N.testbit a p
     | Pos p, Neg a => negb (N.testbit (N.pred a) p)
     | Neg p, _ => false
   end.

 Definition shiftl a n :=
   match norm_pos a, n with
     | Pos a, Pos n => Pos (N.shiftl a n)
     | Pos a, Neg n => Pos (N.shiftr a n)
     | Neg a, Pos n => Neg (N.shiftl a n)
     | Neg a, Neg n => Neg (N.succ (N.shiftr (N.pred a) n))
   end.

 Definition shiftr a n := shiftl a (opp n).

 Definition lor a b :=
   match norm_pos a, norm_pos b with
     | Pos a, Pos b => Pos (N.lor a b)
     | Neg a, Pos b => Neg (N.succ (N.ldiff (N.pred a) b))
     | Pos a, Neg b => Neg (N.succ (N.ldiff (N.pred b) a))
     | Neg a, Neg b => Neg (N.succ (N.land (N.pred a) (N.pred b)))
   end.

 Definition land a b :=
   match norm_pos a, norm_pos b with
     | Pos a, Pos b => Pos (N.land a b)
     | Neg a, Pos b => Pos (N.ldiff b (N.pred a))
     | Pos a, Neg b => Pos (N.ldiff a (N.pred b))
     | Neg a, Neg b => Neg (N.succ (N.lor (N.pred a) (N.pred b)))
   end.

 Definition ldiff a b :=
   match norm_pos a, norm_pos b with
     | Pos a, Pos b => Pos (N.ldiff a b)
     | Neg a, Pos b => Neg (N.succ (N.lor (N.pred a) b))
     | Pos a, Neg b => Pos (N.land a (N.pred b))
     | Neg a, Neg b => Pos (N.ldiff (N.pred b) (N.pred a))
   end.

 Definition lxor a b :=
   match norm_pos a, norm_pos b with
     | Pos a, Pos b => Pos (N.lxor a b)
     | Neg a, Pos b => Neg (N.succ (N.lxor (N.pred a) b))
     | Pos a, Neg b => Neg (N.succ (N.lxor a (N.pred b)))
     | Neg a, Neg b => Pos (N.lxor (N.pred a) (N.pred b))
   end.

 Definition div2 x := shiftr x one.

 Lemma Zlnot_alt1 : forall x, -(x+1) = Z.lnot x.
 Proof.
  unfold Z.lnot, Zpred; auto with zarith.
 Qed.

 Lemma Zlnot_alt2 : forall x, Z.lnot (x-1) = -x.
 Proof.
  unfold Z.lnot, Zpred; auto with zarith.
 Qed.

 Lemma Zlnot_alt3 : forall x, Z.lnot (-x) = x-1.
 Proof.
  unfold Z.lnot, Zpred; auto with zarith.
 Qed.

 Lemma spec_norm_pos : forall x, to_Z (norm_pos x) = to_Z x.
 Proof.
  intros [x|x]; simpl; trivial.
  rewrite N.spec_eqb, N.spec_0.
  case Z.eqb_spec; simpl; auto with zarith.
 Qed.

 Lemma spec_norm_pos_pos : forall x y, norm_pos x = Neg y ->
  0 < N.to_Z y.
 Proof.
  intros [x|x] y; simpl; try easy.
  rewrite N.spec_eqb, N.spec_0.
  case Z.eqb_spec; simpl; try easy.
  inversion 2. subst. generalize (N.spec_pos y); auto with zarith.
 Qed.

 Ltac destr_norm_pos x :=
  rewrite <- (spec_norm_pos x);
  let H := fresh in
  let x' := fresh x in
  assert (H := spec_norm_pos_pos x);
  destruct (norm_pos x) as [x'|x'];
   specialize (H x' (eq_refl _)) || clear H.

 Lemma spec_testbit: forall x p, testbit x p = Z.testbit (to_Z x) (to_Z p).
 Proof.
  intros x p. unfold testbit.
  destr_norm_pos p; simpl. destr_norm_pos x; simpl.
  apply N.spec_testbit.
  rewrite N.spec_testbit, N.spec_pred, Zmax_r by auto with zarith.
  symmetry. apply Z.bits_opp. apply N.spec_pos.
  symmetry. apply Z.testbit_neg_r; auto with zarith.
 Qed.

 Lemma spec_shiftl: forall x p, to_Z (shiftl x p) = Z.shiftl (to_Z x) (to_Z p).
 Proof.
  intros x p. unfold shiftl.
  destr_norm_pos x; destruct p as [p|p]; simpl;
   assert (Hp := N.spec_pos p).
  apply N.spec_shiftl.
  rewrite Z.shiftl_opp_r. apply N.spec_shiftr.
  rewrite !N.spec_shiftl.
  rewrite !Z.shiftl_mul_pow2 by apply N.spec_pos.
  apply Zopp_mult_distr_l.
  rewrite Z.shiftl_opp_r, N.spec_succ, N.spec_shiftr, N.spec_pred, Zmax_r
   by auto with zarith.
  now rewrite Zlnot_alt1, Z.lnot_shiftr, Zlnot_alt2.
 Qed.

 Lemma spec_shiftr: forall x p, to_Z (shiftr x p) = Z.shiftr (to_Z x) (to_Z p).
 Proof.
  intros. unfold shiftr. rewrite spec_shiftl, spec_opp.
  apply Z.shiftl_opp_r.
 Qed.

 Lemma spec_land: forall x y, to_Z (land x y) = Z.land (to_Z x) (to_Z y).
 Proof.
  intros x y. unfold land.
  destr_norm_pos x; destr_norm_pos y; simpl;
   rewrite ?N.spec_succ, ?N.spec_land, ?N.spec_ldiff, ?N.spec_lor,
    ?N.spec_pred, ?Zmax_r, ?Zlnot_alt1; auto with zarith.
  now rewrite Z.ldiff_land, Zlnot_alt2.
  now rewrite Z.ldiff_land, Z.land_comm, Zlnot_alt2.
  now rewrite Z.lnot_lor, !Zlnot_alt2.
 Qed.

 Lemma spec_lor: forall x y, to_Z (lor x y) = Z.lor (to_Z x) (to_Z y).
 Proof.
  intros x y. unfold lor.
  destr_norm_pos x; destr_norm_pos y; simpl;
   rewrite ?N.spec_succ, ?N.spec_land, ?N.spec_ldiff, ?N.spec_lor,
    ?N.spec_pred, ?Zmax_r, ?Zlnot_alt1; auto with zarith.
  now rewrite Z.lnot_ldiff, Z.lor_comm, Zlnot_alt2.
  now rewrite Z.lnot_ldiff, Zlnot_alt2.
  now rewrite Z.lnot_land, !Zlnot_alt2.
 Qed.

 Lemma spec_ldiff: forall x y, to_Z (ldiff x y) = Z.ldiff (to_Z x) (to_Z y).
 Proof.
  intros x y. unfold ldiff.
  destr_norm_pos x; destr_norm_pos y; simpl;
   rewrite ?N.spec_succ, ?N.spec_land, ?N.spec_ldiff, ?N.spec_lor,
    ?N.spec_pred, ?Zmax_r, ?Zlnot_alt1; auto with zarith.
  now rewrite Z.ldiff_land, Zlnot_alt3.
  now rewrite Z.lnot_lor, Z.ldiff_land, <- Zlnot_alt2.
  now rewrite 2 Z.ldiff_land, Zlnot_alt2, Z.land_comm, Zlnot_alt3.
 Qed.

 Lemma spec_lxor: forall x y, to_Z (lxor x y) = Z.lxor (to_Z x) (to_Z y).
 Proof.
  intros x y. unfold lxor.
  destr_norm_pos x; destr_norm_pos y; simpl;
   rewrite ?N.spec_succ, ?N.spec_lxor, ?N.spec_pred, ?Zmax_r, ?Zlnot_alt1;
   auto with zarith.
  now rewrite !Z.lnot_lxor_r, Zlnot_alt2.
  now rewrite !Z.lnot_lxor_l, Zlnot_alt2.
  now rewrite <- Z.lxor_lnot_lnot, !Zlnot_alt2.
 Qed.

 Lemma spec_div2: forall x, to_Z (div2 x) = Z.div2 (to_Z x).
 Proof.
  intros x. unfold div2. now rewrite spec_shiftr, Z.div2_spec, spec_1.
 Qed.

End Make.
