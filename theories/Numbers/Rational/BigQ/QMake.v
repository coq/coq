(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * QMake : a generic efficient implementation of rational numbers *)

(** Initial authors : Benjamin Gregoire, Laurent Thery, INRIA, 2007 *)

Require Import BigNumPrelude ROmega.
Require Import QArith Qcanon Qpower Qminmax.
Require Import NSig ZSig QSig.

(** We will build rationals out of an implementation of integers [ZType]
    for numerators and an implementation of natural numbers [NType] for
    denominators. But first we will need some glue between [NType] and
    [ZType]. *)

Module Type NType_ZType (NN:NType)(ZZ:ZType).
 Parameter Z_of_N : NN.t -> ZZ.t.
 Parameter spec_Z_of_N : forall n, ZZ.to_Z (Z_of_N n) = NN.to_Z n.
 Parameter Zabs_N : ZZ.t -> NN.t.
 Parameter spec_Zabs_N : forall z, NN.to_Z (Zabs_N z) = Z.abs (ZZ.to_Z z).
End NType_ZType.

Module Make (NN:NType)(ZZ:ZType)(Import NZ:NType_ZType NN ZZ) <: QType.

 (** The notation of a rational number is either an integer x,
     interpreted as itself or a pair (x,y) of an integer x and a natural
     number y interpreted as x/y. The pairs (x,0) and (0,y) are all
     interpreted as 0. *)

 Inductive t_ :=
  | Qz : ZZ.t -> t_
  | Qq : ZZ.t -> NN.t -> t_.

 Definition t := t_.

 (** Specification with respect to [QArith] *)

 Local Open Scope Q_scope.

 Definition of_Z x: t := Qz (ZZ.of_Z x).

 Definition of_Q (q:Q) : t :=
  let (x,y) := q in
  match y with
    | 1%positive => Qz (ZZ.of_Z x)
    | _ => Qq (ZZ.of_Z x) (NN.of_N (Npos y))
  end.

 Definition to_Q (q: t) :=
 match q with
   | Qz x => ZZ.to_Z x # 1
   | Qq x y => if NN.eqb y NN.zero then 0
               else ZZ.to_Z x # Z.to_pos (NN.to_Z y)
 end.

 Notation "[ x ]" := (to_Q x).

 Lemma N_to_Z_pos :
  forall x, (NN.to_Z x <> NN.to_Z NN.zero)%Z -> (0 < NN.to_Z x)%Z.
 Proof.
 intros x; rewrite NN.spec_0; generalize (NN.spec_pos x). romega.
 Qed.

 Ltac destr_zcompare := case Z.compare_spec; intros ?H.

 Ltac destr_eqb :=
  match goal with
   | |- context [ZZ.eqb ?x ?y] =>
     rewrite (ZZ.spec_eqb x y);
     case (Z.eqb_spec (ZZ.to_Z x) (ZZ.to_Z y));
     destr_eqb
   | |- context [NN.eqb ?x ?y] =>
     rewrite (NN.spec_eqb x y);
     case (Z.eqb_spec (NN.to_Z x) (NN.to_Z y));
     [ | let H:=fresh "H" in
         try (intro H;generalize (N_to_Z_pos _ H); clear H)];
     destr_eqb
   | _ => idtac
  end.

 Hint Rewrite
  Z.add_0_r Z.add_0_l Z.mul_0_r Z.mul_0_l Z.mul_1_r Z.mul_1_l
  ZZ.spec_0 NN.spec_0 ZZ.spec_1 NN.spec_1 ZZ.spec_m1 ZZ.spec_opp
  ZZ.spec_compare NN.spec_compare
  ZZ.spec_add NN.spec_add ZZ.spec_mul NN.spec_mul ZZ.spec_div NN.spec_div
  ZZ.spec_gcd NN.spec_gcd Z.gcd_abs_l Z.gcd_1_r
  spec_Z_of_N spec_Zabs_N
 : nz.

 Ltac nzsimpl := autorewrite with nz in *.

 Ltac qsimpl := try red; unfold to_Q; simpl; intros;
  destr_eqb; simpl; nzsimpl; intros;
  rewrite ?Z2Pos.id by auto;
  auto.

 Theorem strong_spec_of_Q: forall q: Q, [of_Q q] = q.
 Proof.
 intros(x,y); destruct y; simpl; rewrite ?ZZ.spec_of_Z; auto;
  destr_eqb; now rewrite ?NN.spec_0, ?NN.spec_of_N.
 Qed.

 Theorem spec_of_Q: forall q: Q, [of_Q q] == q.
 Proof.
 intros; rewrite strong_spec_of_Q; red; auto.
 Qed.

 Definition eq x y := [x] == [y].

 Definition zero: t := Qz ZZ.zero.
 Definition one: t := Qz ZZ.one.
 Definition minus_one: t := Qz ZZ.minus_one.

 Lemma spec_0: [zero] == 0.
 Proof.
 simpl. nzsimpl. reflexivity.
 Qed.

 Lemma spec_1: [one] == 1.
 Proof.
 simpl. nzsimpl. reflexivity.
 Qed.

 Lemma spec_m1: [minus_one] == -(1).
 Proof.
 simpl. nzsimpl. reflexivity.
 Qed.

 Definition compare (x y: t) :=
  match x, y with
  | Qz zx, Qz zy => ZZ.compare zx zy
  | Qz zx, Qq ny dy =>
    if NN.eqb dy NN.zero then ZZ.compare zx ZZ.zero
    else ZZ.compare (ZZ.mul zx (Z_of_N dy)) ny
  | Qq nx dx, Qz zy =>
    if NN.eqb dx NN.zero then ZZ.compare ZZ.zero zy
    else ZZ.compare nx (ZZ.mul zy (Z_of_N dx))
  | Qq nx dx, Qq ny dy =>
    match NN.eqb dx NN.zero, NN.eqb dy NN.zero with
    | true, true => Eq
    | true, false => ZZ.compare ZZ.zero ny
    | false, true => ZZ.compare nx ZZ.zero
    | false, false => ZZ.compare (ZZ.mul nx (Z_of_N dy))
                                (ZZ.mul ny (Z_of_N dx))
    end
  end.

 Theorem spec_compare: forall q1 q2, (compare q1 q2) = ([q1] ?= [q2]).
 Proof.
 intros [z1 | x1 y1] [z2 | x2 y2];
   unfold Qcompare, compare; qsimpl.
 Qed.

 Definition lt n m := [n] < [m].
 Definition le n m := [n] <= [m].

 Definition min n m := match compare n m with Gt => m | _ => n end.
 Definition max n m := match compare n m with Lt => m | _ => n end.

 Lemma spec_min : forall n m, [min n m] == Qmin [n] [m].
 Proof.
 unfold min, Qmin, GenericMinMax.gmin. intros.
 rewrite spec_compare; destruct Qcompare; auto with qarith.
 Qed.

 Lemma spec_max : forall n m, [max n m] == Qmax [n] [m].
 Proof.
 unfold max, Qmax, GenericMinMax.gmax. intros.
 rewrite spec_compare; destruct Qcompare; auto with qarith.
 Qed.

 Definition eq_bool n m :=
  match compare n m with Eq => true | _ => false end.

 Theorem spec_eq_bool: forall x y, eq_bool x y = Qeq_bool [x] [y].
 Proof.
 intros. unfold eq_bool. rewrite spec_compare. reflexivity.
 Qed.

 (** [check_int] : is a reduced fraction [n/d] in fact a integer ? *)

 Definition check_int n d :=
  match NN.compare NN.one d with
  | Lt => Qq n d
  | Eq => Qz n
  | Gt => zero  (* n/0 encodes 0 *)
  end.

 Theorem strong_spec_check_int : forall n d, [check_int n d] = [Qq n d].
 Proof.
 intros; unfold check_int.
 nzsimpl.
 destr_zcompare.
 simpl. rewrite <- H; qsimpl. congruence.
 reflexivity.
 qsimpl. exfalso; romega.
 Qed.

 (** Normalisation function *)

 Definition norm n d : t :=
  let gcd := NN.gcd (Zabs_N n) d in
  match NN.compare NN.one gcd with
  | Lt => check_int (ZZ.div n (Z_of_N gcd)) (NN.div d gcd)
  | Eq => check_int n d
  | Gt => zero (* gcd = 0 => both numbers are 0 *)
  end.

 Theorem spec_norm: forall n q, [norm n q] == [Qq n q].
 Proof.
 intros p q; unfold norm.
 assert (Hp := NN.spec_pos (Zabs_N p)).
 assert (Hq := NN.spec_pos q).
 nzsimpl.
 destr_zcompare.
 (* Eq *)
 rewrite strong_spec_check_int; reflexivity.
 (* Lt *)
 rewrite strong_spec_check_int.
 qsimpl.
 generalize (Zgcd_div_pos (ZZ.to_Z p) (NN.to_Z q)). romega.
 replace (NN.to_Z q) with 0%Z in * by assumption.
 rewrite Zdiv_0_l in *; auto with zarith.
 apply Zgcd_div_swap0; romega.
 (* Gt *)
 qsimpl.
 assert (H' : Z.gcd (ZZ.to_Z p) (NN.to_Z q) = 0%Z).
  generalize (Z.gcd_nonneg (ZZ.to_Z p) (NN.to_Z q)); romega.
 symmetry; apply (Z.gcd_eq_0_l _ _ H'); auto.
 Qed.

 Theorem strong_spec_norm : forall p q, [norm p q] = Qred [Qq p q].
 Proof.
 intros.
 replace (Qred [Qq p q]) with (Qred [norm p q]) by
  (apply Qred_complete; apply spec_norm).
 symmetry; apply Qred_identity.
 unfold norm.
 assert (Hp := NN.spec_pos (Zabs_N p)).
 assert (Hq := NN.spec_pos q).
 nzsimpl.
 destr_zcompare; rewrite ?strong_spec_check_int.
 (* Eq *)
 qsimpl.
 (* Lt *)
 qsimpl.
 rewrite Zgcd_1_rel_prime.
 destruct (Z_lt_le_dec 0 (NN.to_Z q)).
 apply Zis_gcd_rel_prime; auto with zarith.
 apply Zgcd_is_gcd.
 replace (NN.to_Z q) with 0%Z in * by romega.
 rewrite Zdiv_0_l in *; romega.
 (* Gt *)
 simpl; auto with zarith.
 Qed.

 (** Reduction function : producing irreducible fractions *)

 Definition red (x : t) : t :=
  match x with
   | Qz z => x
   | Qq n d => norm n d
  end.

 Class Reduced x := is_reduced : [red x] = [x].

 Theorem spec_red : forall x, [red x] == [x].
 Proof.
 intros [ z | n d ].
 auto with qarith.
 unfold red.
 apply spec_norm.
 Qed.

 Theorem strong_spec_red : forall x, [red x] = Qred [x].
 Proof.
 intros [ z | n d ].
 unfold red.
 symmetry; apply Qred_identity; simpl; auto with zarith.
 unfold red; apply strong_spec_norm.
 Qed.

 Definition add (x y: t): t :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (ZZ.add zx zy)
    | Qq ny dy =>
      if NN.eqb dy NN.zero then x
      else Qq (ZZ.add (ZZ.mul zx (Z_of_N dy)) ny) dy
    end
  | Qq nx dx =>
    if NN.eqb dx NN.zero then y
    else match y with
    | Qz zy => Qq (ZZ.add nx (ZZ.mul zy (Z_of_N dx))) dx
    | Qq ny dy =>
      if NN.eqb dy NN.zero then x
      else
       let n := ZZ.add (ZZ.mul nx (Z_of_N dy)) (ZZ.mul ny (Z_of_N dx)) in
       let d := NN.mul dx dy in
       Qq n d
    end
  end.

 Theorem spec_add : forall x y, [add x y] == [x] + [y].
 Proof.
 intros [x | nx dx] [y | ny dy]; unfold Qplus; qsimpl;
  auto with zarith.
 rewrite Pos.mul_1_r, Z2Pos.id; auto.
 rewrite Pos.mul_1_r, Z2Pos.id; auto.
 rewrite Z.mul_eq_0 in *; intuition.
 rewrite Pos2Z.inj_mul, 2 Z2Pos.id; auto.
 Qed.

 Definition add_norm (x y: t): t :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (ZZ.add zx zy)
    | Qq ny dy =>
      if NN.eqb dy NN.zero then x
      else norm (ZZ.add (ZZ.mul zx (Z_of_N dy)) ny) dy
    end
  | Qq nx dx =>
    if NN.eqb dx NN.zero then y
    else match y with
    | Qz zy => norm (ZZ.add nx (ZZ.mul zy (Z_of_N dx))) dx
    | Qq ny dy =>
      if NN.eqb dy NN.zero then x
      else
       let n := ZZ.add (ZZ.mul nx (Z_of_N dy)) (ZZ.mul ny (Z_of_N dx)) in
       let d := NN.mul dx dy in
       norm n d
    end
  end.

 Theorem spec_add_norm : forall x y, [add_norm x y] == [x] + [y].
 Proof.
 intros x y; rewrite <- spec_add.
 destruct x; destruct y; unfold add_norm, add;
 destr_eqb; auto using Qeq_refl, spec_norm.
 Qed.

 Instance strong_spec_add_norm x y
   `(Reduced x, Reduced y) : Reduced (add_norm x y).
 Proof.
 unfold Reduced; intros.
 rewrite strong_spec_red.
 rewrite <- (Qred_complete [add x y]);
  [ | rewrite spec_add, spec_add_norm; apply Qeq_refl ].
 rewrite <- strong_spec_red.
 destruct x as [zx|nx dx]; destruct y as [zy|ny dy];
  simpl; destr_eqb; nzsimpl; simpl; auto.
 Qed.

 Definition opp (x: t): t :=
  match x with
  | Qz zx => Qz (ZZ.opp zx)
  | Qq nx dx => Qq (ZZ.opp nx) dx
  end.

 Theorem strong_spec_opp: forall q, [opp q] = -[q].
 Proof.
 intros [z | x y]; simpl.
 rewrite ZZ.spec_opp; auto.
 match goal with  |- context[NN.eqb ?X ?Y] =>
  generalize (NN.spec_eqb X Y); case NN.eqb
 end; auto; rewrite NN.spec_0.
 rewrite ZZ.spec_opp; auto.
 Qed.

 Theorem spec_opp : forall q, [opp q] == -[q].
 Proof.
 intros; rewrite strong_spec_opp; red; auto.
 Qed.

 Instance strong_spec_opp_norm q `(Reduced q) : Reduced (opp q).
 Proof.
 unfold Reduced; intros.
 rewrite strong_spec_opp, <- H, !strong_spec_red, <- Qred_opp.
 apply Qred_complete; apply spec_opp.
 Qed.

 Definition sub x y := add x (opp y).

 Theorem spec_sub : forall x y, [sub x y] == [x] - [y].
 Proof.
 intros x y; unfold sub; rewrite spec_add; auto.
 rewrite spec_opp; ring.
 Qed.

 Definition sub_norm x y := add_norm x (opp y).

 Theorem spec_sub_norm : forall x y, [sub_norm x y] == [x] - [y].
 Proof.
 intros x y; unfold sub_norm; rewrite spec_add_norm; auto.
 rewrite spec_opp; ring.
 Qed.

 Instance strong_spec_sub_norm x y
  `(Reduced x, Reduced y) : Reduced (sub_norm x y).
 Proof.
 intros.
 unfold sub_norm.
 apply strong_spec_add_norm; auto.
 apply strong_spec_opp_norm; auto.
 Qed.

 Definition mul (x y: t): t :=
  match x, y with
  | Qz zx, Qz zy => Qz (ZZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (ZZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (ZZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (ZZ.mul nx ny) (NN.mul dx dy)
  end.

 Ltac nsubst :=
  match goal with E : NN.to_Z _ = _ |- _ => rewrite E in * end.

 Theorem spec_mul : forall x y, [mul x y] == [x] * [y].
 Proof.
 intros [x | nx dx] [y | ny dy]; unfold Qmult; simpl; qsimpl.
 rewrite Pos.mul_1_r, Z2Pos.id; auto.
 rewrite Z.mul_eq_0 in *; intuition.
 nsubst; auto with zarith.
 nsubst; auto with zarith.
 nsubst; nzsimpl; auto with zarith.
 rewrite Pos2Z.inj_mul, 2 Z2Pos.id; auto.
 Qed.

 Definition norm_denum n d :=
  if NN.eqb d NN.one then Qz n else Qq n d.

 Lemma spec_norm_denum : forall n d,
  [norm_denum n d] == [Qq n d].
 Proof.
 unfold norm_denum; intros; simpl; qsimpl.
 congruence.
 nsubst; auto with zarith.
 Qed.

 Definition irred n d :=
   let gcd := NN.gcd (Zabs_N n) d in
   match NN.compare gcd NN.one with
     | Gt => (ZZ.div n (Z_of_N gcd), NN.div d gcd)
     | _ => (n, d)
   end.

 Lemma spec_irred : forall n d, exists g,
  let (n',d') := irred n d in
  (ZZ.to_Z n' * g = ZZ.to_Z n)%Z /\ (NN.to_Z d' * g = NN.to_Z d)%Z.
 Proof.
 intros.
 unfold irred; nzsimpl; simpl.
 destr_zcompare.
 exists 1%Z; nzsimpl; auto.
 exists 0%Z; nzsimpl.
 assert (Z.gcd (ZZ.to_Z n) (NN.to_Z d) = 0%Z).
  generalize (Z.gcd_nonneg (ZZ.to_Z n) (NN.to_Z d)); romega.
 clear H.
 split.
 symmetry; apply (Z.gcd_eq_0_l _ _ H0).
 symmetry; apply (Z.gcd_eq_0_r _ _ H0).
 exists (Z.gcd (ZZ.to_Z n) (NN.to_Z d)).
 simpl.
 split.
 nzsimpl.
 destruct (Zgcd_is_gcd (ZZ.to_Z n) (NN.to_Z d)).
 rewrite Z.mul_comm; symmetry; apply Zdivide_Zdiv_eq; auto with zarith.
 nzsimpl.
 destruct (Zgcd_is_gcd (ZZ.to_Z n) (NN.to_Z d)).
 rewrite Z.mul_comm; symmetry; apply Zdivide_Zdiv_eq; auto with zarith.
 Qed.

 Lemma spec_irred_zero : forall n d,
   (NN.to_Z d = 0)%Z <-> (NN.to_Z (snd (irred n d)) = 0)%Z.
 Proof.
 intros.
 unfold irred.
 split.
 nzsimpl; intros.
 destr_zcompare; auto.
 simpl.
 nzsimpl.
 rewrite H, Zdiv_0_l; auto.
 nzsimpl; destr_zcompare; simpl; auto.
 nzsimpl.
 intros.
 generalize (NN.spec_pos d); intros.
 destruct (NN.to_Z d); auto.
 assert (0 < 0)%Z.
  rewrite <- H0 at 2.
  apply Zgcd_div_pos; auto with zarith.
  compute; auto.
 discriminate.
 compute in H1; elim H1; auto.
 Qed.

 Lemma strong_spec_irred : forall n d,
  (NN.to_Z d <> 0%Z) ->
  let (n',d') := irred n d in Z.gcd (ZZ.to_Z n') (NN.to_Z d') = 1%Z.
 Proof.
 unfold irred; intros.
 nzsimpl.
 destr_zcompare; simpl; auto.
 elim H.
 apply (Z.gcd_eq_0_r (ZZ.to_Z n)).
 generalize (Z.gcd_nonneg (ZZ.to_Z n) (NN.to_Z d)); romega.

 nzsimpl.
 rewrite Zgcd_1_rel_prime.
 apply Zis_gcd_rel_prime.
 generalize (NN.spec_pos d); romega.
 generalize (Z.gcd_nonneg (ZZ.to_Z n) (NN.to_Z d)); romega.
 apply Zgcd_is_gcd; auto.
 Qed.

 Definition mul_norm_Qz_Qq z n d :=
   if ZZ.eqb z ZZ.zero then zero
   else
    let gcd := NN.gcd (Zabs_N z) d in
    match NN.compare gcd NN.one with
      | Gt =>
        let z := ZZ.div z (Z_of_N gcd) in
        let d := NN.div d gcd in
        norm_denum (ZZ.mul z n) d
      | _  => Qq (ZZ.mul z n) d
    end.

 Definition mul_norm (x y: t): t :=
 match x, y with
 | Qz zx, Qz zy => Qz (ZZ.mul zx zy)
 | Qz zx, Qq ny dy => mul_norm_Qz_Qq zx ny dy
 | Qq nx dx, Qz zy => mul_norm_Qz_Qq zy nx dx
 | Qq nx dx, Qq ny dy =>
    let (nx, dy) := irred nx dy in
    let (ny, dx) := irred ny dx in
    norm_denum (ZZ.mul ny nx) (NN.mul dx dy)
 end.

 Lemma spec_mul_norm_Qz_Qq : forall z n d,
   [mul_norm_Qz_Qq z n d] == [Qq (ZZ.mul z n) d].
 Proof.
 intros z n d; unfold mul_norm_Qz_Qq; nzsimpl; rewrite Zcompare_gt.
 destr_eqb; nzsimpl; intros Hz.
 qsimpl; rewrite Hz; auto.
 destruct Z_le_gt_dec as [LE|GT].
 qsimpl.
 rewrite spec_norm_denum.
 qsimpl.
 rewrite Zdiv_gcd_zero in GT; auto with zarith.
 nsubst. rewrite Zdiv_0_l in *; discriminate.
 rewrite <- Z.mul_assoc, (Z.mul_comm (ZZ.to_Z n)), Z.mul_assoc.
 rewrite Zgcd_div_swap0; try romega.
 ring.
 Qed.

 Instance strong_spec_mul_norm_Qz_Qq z n d :
   forall `(Reduced (Qq n d)), Reduced (mul_norm_Qz_Qq z n d).
 Proof.
 unfold Reduced.
 rewrite 2 strong_spec_red, 2 Qred_iff.
 simpl; nzsimpl.
 destr_eqb; intros Hd H; simpl in *; nzsimpl.

 unfold mul_norm_Qz_Qq; nzsimpl; rewrite Zcompare_gt.
 destr_eqb; intros Hz; simpl; nzsimpl; simpl; auto.
 destruct Z_le_gt_dec.
 simpl; nzsimpl.
 destr_eqb; simpl; nzsimpl; auto with zarith.
 unfold norm_denum. destr_eqb; simpl; nzsimpl.
 rewrite Hd, Zdiv_0_l; discriminate.
 intros _.
 destr_eqb; simpl; nzsimpl; auto.
 nzsimpl; rewrite Hd, Zdiv_0_l; auto with zarith.

 rewrite Z2Pos.id in H; auto.
 unfold mul_norm_Qz_Qq; nzsimpl; rewrite Zcompare_gt.
 destr_eqb; intros Hz; simpl; nzsimpl; simpl; auto.
 destruct Z_le_gt_dec as [H'|H'].
 simpl; nzsimpl.
 destr_eqb; simpl; nzsimpl; auto.
 intros.
 rewrite Z2Pos.id; auto.
 apply Zgcd_mult_rel_prime; auto.
  generalize (Z.gcd_eq_0_l (ZZ.to_Z z) (NN.to_Z d))
    (Z.gcd_nonneg (ZZ.to_Z z) (NN.to_Z d)); romega.
 destr_eqb; simpl; nzsimpl; auto.
 unfold norm_denum.
 destr_eqb; nzsimpl; simpl; destr_eqb; simpl; auto.
 intros; nzsimpl.
 rewrite Z2Pos.id; auto.
 apply Zgcd_mult_rel_prime.
 rewrite Zgcd_1_rel_prime.
 apply Zis_gcd_rel_prime.
 generalize (NN.spec_pos d); romega.
 generalize (Z.gcd_nonneg (ZZ.to_Z z) (NN.to_Z d)); romega.
 apply Zgcd_is_gcd.
 destruct (Zgcd_is_gcd (ZZ.to_Z z) (NN.to_Z d)) as [ (z0,Hz0) (d0,Hd0) Hzd].
 replace (NN.to_Z d / Z.gcd (ZZ.to_Z z) (NN.to_Z d))%Z with d0.
 rewrite Zgcd_1_rel_prime in *.
 apply bezout_rel_prime.
 destruct (rel_prime_bezout _ _ H) as [u v Huv].
 apply Bezout_intro with u (v*(Z.gcd (ZZ.to_Z z) (NN.to_Z d)))%Z.
 rewrite <- Huv; rewrite Hd0 at 2; ring.
 rewrite Hd0 at 1.
 symmetry; apply Z_div_mult_full; auto with zarith.
 Qed.

 Theorem spec_mul_norm : forall x y, [mul_norm x y] == [x] * [y].
 Proof.
 intros x y; rewrite <- spec_mul; auto.
 unfold mul_norm, mul; destruct x; destruct y.
 apply Qeq_refl.
 apply spec_mul_norm_Qz_Qq.
 rewrite spec_mul_norm_Qz_Qq; qsimpl; ring.

 rename t0 into nx, t3 into dy, t2 into ny, t1 into dx.
 destruct (spec_irred nx dy) as (g & Hg).
 destruct (spec_irred ny dx) as (g' & Hg').
 assert (Hz := spec_irred_zero nx dy).
 assert (Hz':= spec_irred_zero ny dx).
 destruct irred as (n1,d1); destruct irred as (n2,d2).
 simpl @snd in *; destruct Hg as [Hg1 Hg2]; destruct Hg' as [Hg1' Hg2'].
 rewrite spec_norm_denum.
 qsimpl.

 match goal with E : (_ * _ = 0)%Z |- _ =>
  rewrite Z.mul_eq_0 in E; destruct E as [Eq|Eq] end.
 rewrite Eq in *; simpl in *.
 rewrite <- Hg2' in *; auto with zarith.
 rewrite Eq in *; simpl in *.
 rewrite <- Hg2 in *; auto with zarith.

 match goal with E : (_ * _ = 0)%Z |- _ =>
  rewrite Z.mul_eq_0 in E; destruct E as [Eq|Eq] end.
 rewrite Hz' in Eq; rewrite Eq in *; auto with zarith.
 rewrite Hz in Eq; rewrite Eq in *; auto with zarith.

 rewrite <- Hg1, <- Hg2, <- Hg1', <- Hg2'; ring.
 Qed.

 Instance strong_spec_mul_norm x y :
  forall `(Reduced x, Reduced y), Reduced (mul_norm x y).
 Proof.
 unfold Reduced; intros.
 rewrite strong_spec_red, Qred_iff.
 destruct x as [zx|nx dx]; destruct y as [zy|ny dy].
 simpl in *; auto with zarith.
 simpl.
 rewrite <- Qred_iff, <- strong_spec_red, strong_spec_mul_norm_Qz_Qq; auto.
 simpl.
 rewrite <- Qred_iff, <- strong_spec_red, strong_spec_mul_norm_Qz_Qq; auto.
 simpl.
 destruct (spec_irred nx dy) as [g Hg].
 destruct (spec_irred ny dx) as [g' Hg'].
 assert (Hz := spec_irred_zero nx dy).
 assert (Hz':= spec_irred_zero ny dx).
 assert (Hgc := strong_spec_irred nx dy).
 assert (Hgc' := strong_spec_irred ny dx).
 destruct irred as (n1,d1); destruct irred as (n2,d2).
 simpl @snd in *; destruct Hg as [Hg1 Hg2]; destruct Hg' as [Hg1' Hg2'].

 unfold norm_denum; qsimpl.

 assert (NEQ : NN.to_Z dy <> 0%Z) by
  (rewrite Hz; intros EQ; rewrite EQ in *; romega).
 specialize (Hgc NEQ).

 assert (NEQ' : NN.to_Z dx <> 0%Z) by
  (rewrite Hz'; intro EQ; rewrite EQ in *; romega).
 specialize (Hgc' NEQ').

 revert H H0.
 rewrite 2 strong_spec_red, 2 Qred_iff; simpl.
 destr_eqb; simpl; nzsimpl; try romega; intros.
 rewrite Z2Pos.id in *; auto.

 apply Zgcd_mult_rel_prime; rewrite Z.gcd_comm;
  apply Zgcd_mult_rel_prime; rewrite Z.gcd_comm; auto.

 rewrite Zgcd_1_rel_prime in *.
 apply bezout_rel_prime.
 destruct (rel_prime_bezout (ZZ.to_Z ny) (NN.to_Z dy)) as [u v Huv]; trivial.
 apply Bezout_intro with (u*g')%Z (v*g)%Z.
 rewrite <- Huv, <- Hg1', <- Hg2. ring.

 rewrite Zgcd_1_rel_prime in *.
 apply bezout_rel_prime.
 destruct (rel_prime_bezout (ZZ.to_Z nx) (NN.to_Z dx)) as [u v Huv]; trivial.
 apply Bezout_intro with (u*g)%Z (v*g')%Z.
 rewrite <- Huv, <- Hg2', <- Hg1. ring.
 Qed.

 Definition inv (x: t): t :=
 match x with
 | Qz z =>
   match ZZ.compare ZZ.zero z with
     | Eq => zero
     | Lt => Qq ZZ.one (Zabs_N z)
     | Gt => Qq ZZ.minus_one (Zabs_N z)
   end
 | Qq n d =>
   match ZZ.compare ZZ.zero n with
     | Eq => zero
     | Lt => Qq (Z_of_N d) (Zabs_N n)
     | Gt => Qq (ZZ.opp (Z_of_N d)) (Zabs_N n)
   end
 end.

 Theorem spec_inv : forall x, [inv x] == /[x].
 Proof.
 destruct x as [ z | n d ].
 (* Qz z *)
 simpl.
 rewrite ZZ.spec_compare; destr_zcompare.
 (* 0 = z *)
 rewrite <- H.
 simpl; nzsimpl; compute; auto.
 (* 0 < z *)
 simpl.
 destr_eqb; nzsimpl; [ intros; rewrite Z.abs_eq in *; romega | intros _ ].
 set (z':=ZZ.to_Z z) in *; clearbody z'.
 red; simpl.
 rewrite Z.abs_eq by romega.
 rewrite Z2Pos.id by auto.
 unfold Qinv; simpl; destruct z'; simpl; auto; discriminate.
 (* 0 > z *)
 simpl.
 destr_eqb; nzsimpl; [ intros; rewrite Z.abs_neq in *; romega | intros _ ].
 set (z':=ZZ.to_Z z) in *; clearbody z'.
 red; simpl.
 rewrite Z.abs_neq by romega.
 rewrite Z2Pos.id by romega.
 unfold Qinv; simpl; destruct z'; simpl; auto; discriminate.
 (* Qq n d *)
 simpl.
 rewrite ZZ.spec_compare; destr_zcompare.
 (* 0 = n *)
 rewrite <- H.
 simpl; nzsimpl.
 destr_eqb; intros; compute; auto.
 (* 0 < n *)
 simpl.
 destr_eqb; nzsimpl; intros.
 intros; rewrite Z.abs_eq in *; romega.
 intros; rewrite Z.abs_eq in *; romega.
 nsubst; compute; auto.
 set (n':=ZZ.to_Z n) in *; clearbody n'.
 rewrite Z.abs_eq by romega.
 red; simpl.
 rewrite Z2Pos.id by auto.
 unfold Qinv; simpl; destruct n'; simpl; auto; try discriminate.
 rewrite Pos2Z.inj_mul, Z2Pos.id; auto.
 (* 0 > n *)
 simpl.
 destr_eqb; nzsimpl; intros.
 intros; rewrite Z.abs_neq in *; romega.
 intros; rewrite Z.abs_neq in *; romega.
 nsubst; compute; auto.
 set (n':=ZZ.to_Z n) in *; clearbody n'.
 red; simpl; nzsimpl.
 rewrite Z.abs_neq by romega.
 rewrite Z2Pos.id by romega.
 unfold Qinv; simpl; destruct n'; simpl; auto; try discriminate.
 assert (T : forall x, Zneg x = Z.opp (Zpos x)) by auto.
 rewrite T, Pos2Z.inj_mul, Z2Pos.id; auto; ring.
 Qed.

 Definition inv_norm (x: t): t :=
   match x with
     | Qz z =>
       match ZZ.compare ZZ.zero z with
         | Eq => zero
         | Lt => Qq ZZ.one (Zabs_N z)
         | Gt => Qq ZZ.minus_one (Zabs_N z)
       end
     | Qq n d =>
       if NN.eqb d NN.zero then zero else
       match ZZ.compare ZZ.zero n with
         | Eq => zero
         | Lt =>
           match ZZ.compare n ZZ.one with
             | Gt => Qq (Z_of_N d) (Zabs_N n)
             | _ => Qz (Z_of_N d)
           end
         | Gt =>
           match ZZ.compare n ZZ.minus_one with
             | Lt => Qq (ZZ.opp (Z_of_N d)) (Zabs_N n)
             | _ => Qz (ZZ.opp (Z_of_N d))
           end
       end
   end.

 Theorem spec_inv_norm : forall x, [inv_norm x] == /[x].
 Proof.
 intros.
 rewrite <- spec_inv.
 destruct x as [ z | n d ].
 (* Qz z *)
 simpl.
 rewrite ZZ.spec_compare; destr_zcompare; auto with qarith.
 (* Qq n d *)
 simpl; nzsimpl; destr_eqb.
 destr_zcompare; simpl; auto with qarith.
 destr_eqb; nzsimpl; auto with qarith.
 intros _ Hd; rewrite Hd; auto with qarith.
 destr_eqb; nzsimpl; auto with qarith.
 intros _ Hd; rewrite Hd; auto with qarith.
 (* 0 < n *)
 destr_zcompare; auto with qarith.
 destr_zcompare; nzsimpl; simpl; auto with qarith; intros.
 destr_eqb; nzsimpl; [ intros; rewrite Z.abs_eq in *; romega | intros _ ].
 rewrite H0; auto with qarith.
 romega.
 (* 0 > n *)
 destr_zcompare; nzsimpl; simpl; auto with qarith.
 destr_eqb; nzsimpl; [ intros; rewrite Z.abs_neq in *; romega | intros _ ].
 rewrite H0; auto with qarith.
 romega.
 Qed.

 Instance strong_spec_inv_norm x : Reduced x -> Reduced (inv_norm x).
 Proof.
 unfold Reduced.
 intros.
 destruct x as [ z | n d ].
 (* Qz *)
 simpl; nzsimpl.
 rewrite strong_spec_red, Qred_iff.
 destr_zcompare; simpl; nzsimpl; auto.
 destr_eqb; nzsimpl; simpl; auto.
 destr_eqb; nzsimpl; simpl; auto.
 (* Qq n d *)
 rewrite strong_spec_red, Qred_iff in H; revert H.
 simpl; nzsimpl.
 destr_eqb; nzsimpl; auto with qarith.
 destr_zcompare; simpl; nzsimpl; auto; intros.
 (* 0 < n *)
 destr_zcompare; simpl; nzsimpl; auto.
 destr_eqb; nzsimpl; simpl; auto.
 rewrite Z.abs_eq; romega.
 intros _.
 rewrite strong_spec_norm; simpl; nzsimpl.
 destr_eqb; nzsimpl.
 rewrite Z.abs_eq; romega.
 intros _.
 rewrite Qred_iff.
 simpl.
 rewrite Z.abs_eq; auto with zarith.
 rewrite Z2Pos.id in *; auto.
 rewrite Z.gcd_comm; auto.
 (* 0 > n *)
 destr_eqb; nzsimpl; simpl; auto; intros.
 destr_zcompare; simpl; nzsimpl; auto.
 destr_eqb; nzsimpl.
 rewrite Z.abs_neq; romega.
 intros _.
 rewrite strong_spec_norm; simpl; nzsimpl.
 destr_eqb; nzsimpl.
 rewrite Z.abs_neq; romega.
 intros _.
 rewrite Qred_iff.
 simpl.
 rewrite Z2Pos.id in *; auto.
 intros.
 rewrite Z.gcd_comm, Z.gcd_abs_l, Z.gcd_comm.
 apply Zis_gcd_gcd; auto with zarith.
 apply Zis_gcd_minus.
 rewrite Z.opp_involutive, <- H1; apply Zgcd_is_gcd.
 rewrite Z.abs_neq; romega.
 Qed.

 Definition div x y := mul x (inv y).

 Theorem spec_div x y: [div x y] == [x] / [y].
 Proof.
 unfold div; rewrite spec_mul; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv; auto.
 Qed.

 Definition div_norm x y := mul_norm x (inv_norm y).

 Theorem spec_div_norm x y: [div_norm x y] == [x] / [y].
 Proof.
 unfold div_norm; rewrite spec_mul_norm; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv_norm; auto.
 Qed.

 Instance strong_spec_div_norm x y
   `(Reduced x, Reduced y) : Reduced (div_norm x y).
 Proof.
 intros; unfold div_norm.
 apply strong_spec_mul_norm; auto.
 apply strong_spec_inv_norm; auto.
 Qed.

 Definition square (x: t): t :=
  match x with
  | Qz zx => Qz (ZZ.square zx)
  | Qq nx dx => Qq (ZZ.square nx) (NN.square dx)
  end.

 Theorem spec_square : forall x, [square x] == [x] ^ 2.
 Proof.
 destruct x as [ z | n d ].
 simpl; rewrite ZZ.spec_square; red; auto.
 simpl.
 destr_eqb; nzsimpl; intros.
 apply Qeq_refl.
 rewrite NN.spec_square in *; nzsimpl.
 rewrite Z.mul_eq_0 in *; romega.
 rewrite NN.spec_square in *; nzsimpl; nsubst; romega.
 rewrite ZZ.spec_square, NN.spec_square.
 red; simpl.
 rewrite Pos2Z.inj_mul; rewrite !Z2Pos.id; auto.
 apply Z.mul_pos_pos; auto.
 Qed.

 Definition power_pos (x : t) p : t :=
  match x with
  | Qz zx => Qz (ZZ.pow_pos zx p)
  | Qq nx dx => Qq (ZZ.pow_pos nx p) (NN.pow_pos dx p)
  end.

 Theorem spec_power_pos : forall x p, [power_pos x p] == [x] ^ Zpos p.
 Proof.
 intros [ z | n d ] p; unfold power_pos.
 (* Qz *)
 simpl.
 rewrite ZZ.spec_pow_pos, Qpower_decomp.
 red; simpl; f_equal.
 now rewrite Pos2Z.inj_pow, Z.pow_1_l.
 (* Qq *)
 simpl.
 rewrite ZZ.spec_pow_pos.
 destr_eqb; nzsimpl; intros.
 - apply Qeq_sym; apply Qpower_positive_0.
 - rewrite NN.spec_pow_pos in *.
   assert (0 < NN.to_Z d ^ ' p)%Z by
    (apply Z.pow_pos_nonneg; auto with zarith).
   romega.
 - exfalso.
   rewrite NN.spec_pow_pos in *. nsubst.
   rewrite Z.pow_0_l' in *; [romega|discriminate].
 - rewrite Qpower_decomp.
   red; simpl; do 3 f_equal.
   apply Pos2Z.inj. rewrite Pos2Z.inj_pow.
   rewrite 2 Z2Pos.id by (generalize (NN.spec_pos d); romega).
   now rewrite NN.spec_pow_pos.
 Qed.

 Instance strong_spec_power_pos x p `(Reduced x) : Reduced (power_pos x p).
 Proof.
 destruct x as [z | n d]; simpl; intros.
 red; simpl; auto.
 red; simpl; intros.
 rewrite strong_spec_norm; simpl.
 destr_eqb; nzsimpl; intros.
 simpl; auto.
 rewrite Qred_iff.
 revert H.
 unfold Reduced; rewrite strong_spec_red, Qred_iff; simpl.
 destr_eqb; nzsimpl; simpl; intros.
 exfalso.
 rewrite NN.spec_pow_pos in *. nsubst.
 rewrite Z.pow_0_l' in *; [romega|discriminate].
 rewrite Z2Pos.id in *; auto.
 rewrite NN.spec_pow_pos, ZZ.spec_pow_pos; auto.
 rewrite Zgcd_1_rel_prime in *.
 apply rel_prime_Zpower; auto with zarith.
 Qed.

 Definition power (x : t) (z : Z) : t :=
   match z with
     | Z0 => one
     | Zpos p => power_pos x p
     | Zneg p => inv (power_pos x p)
   end.

 Theorem spec_power : forall x z, [power x z] == [x]^z.
 Proof.
 destruct z.
 simpl; nzsimpl; red; auto.
 apply spec_power_pos.
 simpl.
 rewrite spec_inv, spec_power_pos; apply Qeq_refl.
 Qed.

 Definition power_norm (x : t) (z : Z) : t :=
   match z with
     | Z0 => one
     | Zpos p => power_pos x p
     | Zneg p => inv_norm (power_pos x p)
   end.

 Theorem spec_power_norm : forall x z, [power_norm x z] == [x]^z.
 Proof.
 destruct z.
 simpl; nzsimpl; red; auto.
 apply spec_power_pos.
 simpl.
 rewrite spec_inv_norm, spec_power_pos; apply Qeq_refl.
 Qed.

 Instance strong_spec_power_norm x z :
   Reduced x -> Reduced (power_norm x z).
 Proof.
 destruct z; simpl.
 intros _; unfold Reduced; rewrite strong_spec_red.
 unfold one.
 simpl to_Q; nzsimpl; auto.
 intros; apply strong_spec_power_pos; auto.
 intros; apply strong_spec_inv_norm; apply strong_spec_power_pos; auto.
 Qed.


 (** Interaction with [Qcanon.Qc] *)

 Open Scope Qc_scope.

 Definition of_Qc q := of_Q (this q).

 Definition to_Qc q := Q2Qc [q].

 Notation "[[ x ]]" := (to_Qc x).

 Theorem strong_spec_of_Qc : forall q, [of_Qc q] = q.
 Proof.
 intros (q,Hq); intros.
 unfold of_Qc; rewrite strong_spec_of_Q; auto.
 Qed.

 Instance strong_spec_of_Qc_bis q : Reduced (of_Qc q).
 Proof.
 intros; red; rewrite strong_spec_red, strong_spec_of_Qc.
 destruct q; simpl; auto.
 Qed.

 Theorem spec_of_Qc: forall q, [[of_Qc q]] = q.
 Proof.
 intros; apply Qc_decomp; simpl; intros.
 rewrite strong_spec_of_Qc; auto.
 Qed.

 Theorem spec_oppc: forall q, [[opp q]] = -[[q]].
 Proof.
 intros q; unfold Qcopp, to_Qc, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 rewrite spec_opp, <- Qred_opp, Qred_correct.
 apply Qeq_refl.
 Qed.

 Theorem spec_oppc_bis : forall q : Qc, [opp (of_Qc q)] = - q.
 Proof.
 intros.
 rewrite <- strong_spec_opp_norm by apply strong_spec_of_Qc_bis.
 rewrite strong_spec_red.
 symmetry; apply (Qred_complete (-q)%Q).
 rewrite spec_opp, strong_spec_of_Qc; auto with qarith.
 Qed.

 Theorem spec_comparec: forall q1 q2,
  compare q1 q2 = ([[q1]] ?= [[q2]]).
 Proof.
 unfold Qccompare, to_Qc.
 intros q1 q2; rewrite spec_compare; simpl; auto.
 apply Qcompare_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_addc x y:
  [[add x y]] = [[x]] + [[y]].
 Proof.
 unfold to_Qc.
 transitivity (Q2Qc ([x] + [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_add; auto.
 unfold Qcplus, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qplus_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_add_normc x y:
  [[add_norm x y]] = [[x]] + [[y]].
 Proof.
 unfold to_Qc.
 transitivity (Q2Qc ([x] + [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_add_norm; auto.
 unfold Qcplus, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qplus_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_add_normc_bis : forall x y : Qc,
   [add_norm (of_Qc x) (of_Qc y)] = x+y.
 Proof.
 intros.
 rewrite <- strong_spec_add_norm by apply strong_spec_of_Qc_bis.
 rewrite strong_spec_red.
 symmetry; apply (Qred_complete (x+y)%Q).
 rewrite spec_add_norm, ! strong_spec_of_Qc; auto with qarith.
 Qed.

 Theorem spec_subc x y:  [[sub x y]] = [[x]] - [[y]].
 Proof.
 unfold sub; rewrite spec_addc; auto.
 rewrite spec_oppc; ring.
 Qed.

 Theorem spec_sub_normc x y:
   [[sub_norm x y]] = [[x]] - [[y]].
 Proof.
 unfold sub_norm; rewrite spec_add_normc; auto.
 rewrite spec_oppc; ring.
 Qed.

 Theorem spec_sub_normc_bis : forall x y : Qc,
   [sub_norm (of_Qc x) (of_Qc y)] = x-y.
 Proof.
 intros.
 rewrite <- strong_spec_sub_norm by apply strong_spec_of_Qc_bis.
 rewrite strong_spec_red.
 symmetry; apply (Qred_complete (x+(-y)%Qc)%Q).
 rewrite spec_sub_norm, ! strong_spec_of_Qc.
 unfold Qcopp, Q2Qc, this. rewrite Qred_correct ; auto with qarith.
 Qed.

 Theorem spec_mulc x y:
  [[mul x y]] = [[x]] * [[y]].
 Proof.
 unfold to_Qc.
 transitivity (Q2Qc ([x] * [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_mul; auto.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_mul_normc x y:
   [[mul_norm x y]] = [[x]] * [[y]].
 Proof.
 unfold to_Qc.
 transitivity (Q2Qc ([x] * [y])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_mul_norm; auto.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_mul_normc_bis : forall x y : Qc,
   [mul_norm (of_Qc x) (of_Qc y)] = x*y.
 Proof.
 intros.
 rewrite <- strong_spec_mul_norm by apply strong_spec_of_Qc_bis.
 rewrite strong_spec_red.
 symmetry; apply (Qred_complete (x*y)%Q).
 rewrite spec_mul_norm, ! strong_spec_of_Qc; auto with qarith.
 Qed.

 Theorem spec_invc x:
   [[inv x]] =  /[[x]].
 Proof.
 unfold to_Qc.
 transitivity (Q2Qc (/[x])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_inv; auto.
 unfold Qcinv, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qinv_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_inv_normc x:
   [[inv_norm x]] =  /[[x]].
 Proof.
 unfold to_Qc.
 transitivity (Q2Qc (/[x])).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_inv_norm; auto.
 unfold Qcinv, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qinv_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_inv_normc_bis : forall x : Qc,
   [inv_norm (of_Qc x)] = /x.
 Proof.
 intros.
 rewrite <- strong_spec_inv_norm by apply strong_spec_of_Qc_bis.
 rewrite strong_spec_red.
 symmetry; apply (Qred_complete (/x)%Q).
 rewrite spec_inv_norm, ! strong_spec_of_Qc; auto with qarith.
 Qed.

 Theorem spec_divc x y: [[div x y]] = [[x]] / [[y]].
 Proof.
 unfold div; rewrite spec_mulc; auto.
 unfold Qcdiv; apply f_equal2 with (f := Qcmult); auto.
 apply spec_invc; auto.
 Qed.

 Theorem spec_div_normc x y: [[div_norm x y]] = [[x]] / [[y]].
 Proof.
 unfold div_norm; rewrite spec_mul_normc; auto.
 unfold Qcdiv; apply f_equal2 with (f := Qcmult); auto.
 apply spec_inv_normc; auto.
 Qed.

 Theorem spec_div_normc_bis : forall x y : Qc,
   [div_norm (of_Qc x) (of_Qc y)] = x/y.
 Proof.
 intros.
 rewrite <- strong_spec_div_norm by apply strong_spec_of_Qc_bis.
 rewrite strong_spec_red.
 symmetry; apply (Qred_complete (x*(/y)%Qc)%Q).
 rewrite spec_div_norm, ! strong_spec_of_Qc.
 unfold Qcinv, Q2Qc, this; rewrite Qred_correct; auto with qarith.
 Qed.

 Theorem spec_squarec x: [[square x]] = [[x]]^2.
 Proof.
 unfold to_Qc.
 transitivity (Q2Qc ([x]^2)).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_square; auto.
 simpl Qcpower.
 replace (Q2Qc [x] * 1) with (Q2Qc [x]); try ring.
 simpl.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_power_posc x p:
   [[power_pos x p]] = [[x]] ^ Pos.to_nat p.
 Proof.
 unfold to_Qc.
 transitivity (Q2Qc ([x]^Zpos p)).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_power_pos; auto.
 induction p using Pos.peano_ind.
 simpl; ring.
 rewrite Pos2Nat.inj_succ; simpl Qcpower.
 rewrite <- IHp; clear IHp.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 setoid_replace ([x] ^ ' Pos.succ p)%Q with ([x] * [x] ^ ' p)%Q.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 simpl.
 rewrite <- Pos.add_1_l.
 rewrite Qpower_plus_positive; simpl; apply Qeq_refl.
 Qed.

End Make.

