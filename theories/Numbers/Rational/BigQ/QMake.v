(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(*i $Id$ i*)

Require Import BigNumPrelude ROmega.
Require Import QArith Qcanon Qpower.
Require Import NSig ZSig QSig.

Module Type NType_ZType (N:NType)(Z:ZType).
 Parameter Z_of_N : N.t -> Z.t.
 Parameter spec_Z_of_N : forall n, Z.to_Z (Z_of_N n) = N.to_Z n.
 Parameter Zabs_N : Z.t -> N.t.
 Parameter spec_Zabs_N : forall z, N.to_Z (Zabs_N z) = Zabs (Z.to_Z z).
End NType_ZType.

Module Make (N:NType)(Z:ZType)(Import NZ:NType_ZType N Z) <: QType.

 (** The notation of a rational number is either an integer x,
     interpreted as itself or a pair (x,y) of an integer x and a natural
     number y interpreted as x/y. The pairs (x,0) and (0,y) are all
     interpreted as 0. *)

 Inductive t_ := 
  | Qz : Z.t -> t_
  | Qq : Z.t -> N.t -> t_.

 Definition t := t_.

 (** Specification with respect to [QArith] *) 

 Open Local Scope Q_scope.

 Definition of_Z x: t := Qz (Z.of_Z x).

 Definition of_Q (q:Q) : t := 
  let (x,y) := q in 
  match y with 
    | 1%positive => Qz (Z.of_Z x)
    | _ => Qq (Z.of_Z x) (N.of_N (Npos y))
  end.

 Definition to_Q (q: t) := 
 match q with 
   | Qz x => Z.to_Z x # 1
   | Qq x y => if N.eq_bool y N.zero then 0
               else Z.to_Z x # Z2P (N.to_Z y)
 end.

 Notation "[ x ]" := (to_Q x).

 Theorem strong_spec_of_Q: forall q: Q, [of_Q q] = q.
 Proof.
 intros(x,y); destruct y; simpl; rewrite Z.spec_of_Z; auto.
 generalize (N.spec_eq_bool (N.of_N (Npos y~1)) N.zero); 
  case N.eq_bool; auto; rewrite N.spec_0.
 rewrite N.spec_of_N; discriminate.
 rewrite N.spec_of_N; auto.
 generalize (N.spec_eq_bool (N.of_N (Npos y~0)) N.zero); 
  case N.eq_bool; auto; rewrite N.spec_0.
 rewrite N.spec_of_N; discriminate.
 rewrite N.spec_of_N; auto.
 Qed.

 Theorem spec_of_Q: forall q: Q, [of_Q q] == q.
 Proof.
 intros; rewrite strong_spec_of_Q; red; auto.
 Qed.

 Definition eq x y := [x] == [y].

 Definition zero: t := Qz Z.zero.
 Definition one: t := Qz Z.one.
 Definition minus_one: t := Qz Z.minus_one.

 Lemma spec_0: [zero] == 0.
 Proof.
 simpl; rewrite Z.spec_0; reflexivity.
 Qed.

 Lemma spec_1: [one] == 1.
 Proof.
 simpl; rewrite Z.spec_1; reflexivity.
 Qed.

 Lemma spec_m1: [minus_one] == -(1).
 Proof.
 simpl; rewrite Z.spec_m1; reflexivity.
 Qed.

 Definition compare (x y: t) :=
  match x, y with
  | Qz zx, Qz zy => Z.compare zx zy
  | Qz zx, Qq ny dy => 
    if N.eq_bool dy N.zero then Z.compare zx Z.zero
    else Z.compare (Z.mul zx (Z_of_N dy)) ny
  | Qq nx dx, Qz zy => 
    if N.eq_bool dx N.zero then Z.compare Z.zero zy 
    else Z.compare nx (Z.mul zy (Z_of_N dx))
  | Qq nx dx, Qq ny dy =>
    match N.eq_bool dx N.zero, N.eq_bool dy N.zero with
    | true, true => Eq
    | true, false => Z.compare Z.zero ny
    | false, true => Z.compare nx Z.zero
    | false, false => Z.compare (Z.mul nx (Z_of_N dy)) 
                                (Z.mul ny (Z_of_N dx))
    end
  end.

 Lemma Zcompare_spec_alt : 
  forall z z', Z.compare z z' = (Z.to_Z z ?= Z.to_Z z')%Z.
 Proof.
 intros; generalize (Z.spec_compare z z'); destruct Z.compare; auto.
 intro H; rewrite H; symmetry; apply Zcompare_refl.
 Qed.
 
 Lemma Ncompare_spec_alt : 
  forall n n', N.compare n n' = (N.to_Z n ?= N.to_Z n')%Z.
 Proof.
 intros; generalize (N.spec_compare n n'); destruct N.compare; auto.
 intro H; rewrite H; symmetry; apply Zcompare_refl.
 Qed.

 Lemma N_to_Z2P : forall n, N.to_Z n <> 0%Z -> 
  Zpos (Z2P (N.to_Z n)) = N.to_Z n.
 Proof.
 intros; apply Z2P_correct.
 generalize (N.spec_pos n); romega.
 Qed.

 Hint Rewrite 
  Zplus_0_r Zplus_0_l Zmult_0_r Zmult_0_l Zmult_1_r Zmult_1_l 
  Z.spec_0 N.spec_0 Z.spec_1 N.spec_1 Z.spec_m1 Z.spec_opp
  Zcompare_spec_alt Ncompare_spec_alt
  Z.spec_add N.spec_add Z.spec_mul N.spec_mul 
  Z.spec_gcd N.spec_gcd Zgcd_Zabs Zgcd_1
  spec_Z_of_N spec_Zabs_N
 : nz.
 Ltac nzsimpl := autorewrite with nz in *.

 Ltac destr_neq_bool := repeat
 (match goal with |- context [N.eq_bool ?x ?y] => 
   generalize (N.spec_eq_bool x y); case N.eq_bool
  end).
 
 Ltac destr_zeq_bool := repeat
 (match goal with |- context [Z.eq_bool ?x ?y] => 
   generalize (Z.spec_eq_bool x y); case Z.eq_bool
  end).

 Ltac simpl_ndiv := rewrite N.spec_div by (nzsimpl; romega).
 Tactic Notation "simpl_ndiv" "in" "*" := 
   rewrite N.spec_div in * by (nzsimpl; romega).

 Ltac simpl_zdiv := rewrite Z.spec_div by (nzsimpl; romega).
 Tactic Notation "simpl_zdiv" "in" "*" := 
   rewrite Z.spec_div in * by (nzsimpl; romega).

 Ltac qsimpl := try red; unfold to_Q; simpl; intros; 
  destr_neq_bool; destr_zeq_bool; simpl; nzsimpl; auto; intros.

 Theorem spec_compare: forall q1 q2, (compare q1 q2) = ([q1] ?= [q2]).
 Proof.
 intros [z1 | x1 y1] [z2 | x2 y2]; 
   unfold Qcompare, compare; qsimpl; rewrite ! N_to_Z2P; auto.
 Qed.

 Definition lt n m := compare n m = Lt.
 Definition le n m := compare n m <> Gt.
 Definition min n m := match compare n m with Gt => m | _ => n end.
 Definition max n m := match compare n m with Lt => m | _ => n end.

 Definition eq_bool n m := 
  match compare n m with Eq => true | _ => false end.

 Theorem spec_eq_bool: forall x y,
  if eq_bool x y then [x] == [y] else ~([x] == [y]).
 Proof.
 intros.
 unfold eq_bool.
 rewrite spec_compare.
 generalize (Qeq_alt [x] [y]).
 destruct Qcompare.
 intros H; rewrite H; auto.
 intros H H'; rewrite H in H'; discriminate.
 intros H H'; rewrite H in H'; discriminate.
 Qed.

 (** Normalisation function *)

 Definition norm n d : t :=
  let gcd := N.gcd (Zabs_N n) d in 
  match N.compare N.one gcd with
  | Lt => 
    let n := Z.div n (Z_of_N gcd) in
    let d := N.div d gcd in
    match N.compare d N.one with
    | Gt => Qq n d
    | Eq => Qz n
    | Lt => zero
    end
  | Eq => Qq n d
  | Gt => zero (* gcd = 0 => both numbers are 0 *)
  end.

 Theorem spec_norm: forall n q, [norm n q] == [Qq n q].
 Proof.
 intros p q; unfold norm.
 assert (Hp := N.spec_pos (Zabs_N p)).
 assert (Hq := N.spec_pos q).
 nzsimpl.
 destr_zcompare.
 qsimpl.

 simpl_ndiv.
 destr_zcompare.
 qsimpl.
 rewrite H1 in *; rewrite Zdiv_0_l in H0; discriminate.
 rewrite N_to_Z2P; auto.
 simpl_zdiv; nzsimpl.
 rewrite Zgcd_div_swap0, H0; romega.

 qsimpl.
 assert (0 < N.to_Z q / Zgcd (Z.to_Z p) (N.to_Z q))%Z.
  apply Zgcd_div_pos; romega.
 romega.

 qsimpl.
 simpl_ndiv in *; nzsimpl; romega.
 simpl_ndiv in *.
 rewrite H1, Zdiv_0_l in H2; elim H2; auto.
 rewrite 2 N_to_Z2P; auto.
 simpl_ndiv; simpl_zdiv; nzsimpl.
 apply Zgcd_div_swap0; romega.

 qsimpl.
 assert (H' : Zgcd (Z.to_Z p) (N.to_Z q) = 0%Z).
  generalize (Zgcd_is_pos (Z.to_Z p) (N.to_Z q)); romega.
 symmetry; apply (Zgcd_inv_0_l _ _ H'); auto.
 Qed.

 Theorem strong_spec_norm : forall p q, [norm p q] = Qred [Qq p q].
 Proof.
 intros.
 replace (Qred [Qq p q]) with (Qred [norm p q]) by 
  (apply Qred_complete; apply spec_norm).
 symmetry; apply Qred_identity.
 unfold norm.
 assert (Hp := N.spec_pos (Zabs_N p)).
 assert (Hq := N.spec_pos q).
 nzsimpl.
 destr_zcompare.
 (* Eq *)
 simpl.
 destr_neq_bool; nzsimpl; simpl; auto.
 intros.
 rewrite N_to_Z2P; auto.
 (* Lt *)
 simpl_ndiv.
 destr_zcompare.
 qsimpl; auto.
 qsimpl.
 qsimpl.
 simpl_zdiv; nzsimpl.
 rewrite N_to_Z2P; auto.
 clear H1.
 simpl_ndiv; nzsimpl.
 rewrite Zgcd_1_rel_prime.
 destruct (Z_lt_le_dec 0 (N.to_Z q)).
 apply Zis_gcd_rel_prime; auto with zarith.
 apply Zgcd_is_gcd.
 replace (N.to_Z q) with 0%Z in * by romega.
 rewrite Zdiv_0_l in H0; discriminate.
 (* Gt *)
 simpl; auto with zarith.
 Qed.

 (** Reduction function : producing irreducible fractions *) 

 Definition red (x : t) : t := 
  match x with 
   | Qz z => x
   | Qq n d => norm n d
  end.

 Definition Reduced x := [red x] = [x].

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
    | Qz zy => Qz (Z.add zx zy)
    | Qq ny dy => 
      if N.eq_bool dy N.zero then x 
      else Qq (Z.add (Z.mul zx (Z_of_N dy)) ny) dy
    end
  | Qq nx dx =>
    if N.eq_bool dx N.zero then y 
    else match y with
    | Qz zy => Qq (Z.add nx (Z.mul zy (Z_of_N dx))) dx
    | Qq ny dy =>
      if N.eq_bool dy N.zero then x
      else
       let n := Z.add (Z.mul nx (Z_of_N dy)) (Z.mul ny (Z_of_N dx)) in
       let d := N.mul dx dy in
       Qq n d
    end
  end.

 Theorem spec_add : forall x y, [add x y] == [x] + [y].
 Proof.
 intros [x | nx dx] [y | ny dy]; unfold Qplus; qsimpl.
 intuition.
 rewrite N_to_Z2P; auto.
 intuition.
 rewrite Pmult_1_r, N_to_Z2P; auto.
 intuition.
 rewrite Pmult_1_r, N_to_Z2P; auto.
 destruct (Zmult_integral _ _ H); intuition.
 rewrite Zpos_mult_morphism, 2 N_to_Z2P; auto.
 rewrite (Z2P_correct (N.to_Z dx * N.to_Z dy)); auto.
 apply Zmult_lt_0_compat.
  generalize (N.spec_pos dx); romega.
  generalize (N.spec_pos dy); romega.
 Qed.

 Definition add_norm (x y: t): t :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (Z.add zx zy)
    | Qq ny dy =>  
      if N.eq_bool dy N.zero then x 
      else norm (Z.add (Z.mul zx (Z_of_N dy)) ny) dy
    end
  | Qq nx dx =>
    if N.eq_bool dx N.zero then y 
    else match y with
    | Qz zy => norm (Z.add nx (Z.mul zy (Z_of_N dx))) dx
    | Qq ny dy =>
      if N.eq_bool dy N.zero then x
      else
       let n := Z.add (Z.mul nx (Z_of_N dy)) (Z.mul ny (Z_of_N dx)) in
       let d := N.mul dx dy in
       norm n d
    end
  end.

 Theorem spec_add_norm : forall x y, [add_norm x y] == [x] + [y].
 Proof.
 intros x y; rewrite <- spec_add.
 destruct x; destruct y; unfold add_norm, add; 
 destr_neq_bool; auto using Qeq_refl, spec_norm.
 Qed.

 Theorem strong_spec_add_norm : forall x y : t, 
   Reduced x -> Reduced y -> Reduced (add_norm x y).
 Proof.
 unfold Reduced; intros.
 rewrite strong_spec_red.
 rewrite <- (Qred_complete [add x y]); 
  [ | rewrite spec_add, spec_add_norm; apply Qeq_refl ].
 rewrite <- strong_spec_red.
 destruct x as [zx|nx dx]; destruct y as [zy|ny dy].
 simpl in *; auto.
 simpl; intros.
 destr_neq_bool; nzsimpl; simpl; auto.
 simpl; intros.
 destr_neq_bool; nzsimpl; simpl; auto.
 simpl; intros.
 destr_neq_bool; nzsimpl; simpl; auto.
 Qed.

 Definition opp (x: t): t :=
  match x with
  | Qz zx => Qz (Z.opp zx)
  | Qq nx dx => Qq (Z.opp nx) dx
  end.

 Theorem strong_spec_opp: forall q, [opp q] = -[q].
 Proof.
 intros [z | x y]; simpl.
 rewrite Z.spec_opp; auto.
 match goal with  |- context[N.eq_bool ?X ?Y] => 
  generalize (N.spec_eq_bool X Y); case N.eq_bool
 end; auto; rewrite N.spec_0.
 rewrite Z.spec_opp; auto.
 Qed.

 Theorem spec_opp : forall q, [opp q] == -[q].
 Proof.
 intros; rewrite strong_spec_opp; red; auto.
 Qed.

 Theorem strong_spec_opp_norm : forall q, Reduced q -> Reduced (opp q).
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

 Theorem strong_spec_sub_norm : forall x y, 
  Reduced x -> Reduced y -> Reduced (sub_norm x y).
 Proof.
 intros.
 unfold sub_norm.
 apply strong_spec_add_norm; auto.
 apply strong_spec_opp_norm; auto.
 Qed.

 Definition mul (x y: t): t :=
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy => Qq (Z.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (Z.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (Z.mul nx ny) (N.mul dx dy)
  end.

 Theorem spec_mul : forall x y, [mul x y] == [x] * [y].
 Proof.
 intros [x | nx dx] [y | ny dy]; unfold Qmult; simpl; qsimpl.
 rewrite Pmult_1_r, N_to_Z2P; auto.
 destruct (Zmult_integral _ _ H1); intuition.
 rewrite H0 in H1; elim H1; auto.
 rewrite H0 in H1; elim H1; auto.
 rewrite H in H1; nzsimpl; elim H1; auto.
 rewrite Zpos_mult_morphism, 2 N_to_Z2P; auto.
 rewrite (Z2P_correct (N.to_Z dx * N.to_Z dy)); auto.
 apply Zmult_lt_0_compat.
  generalize (N.spec_pos dx); omega.
  generalize (N.spec_pos dy); omega.
 Qed.

 Lemma norm_denum : forall n d, 
  [if N.eq_bool d N.one then Qz n else Qq n d] == [Qq n d].
 Proof.
 intros; simpl; qsimpl.
 rewrite H0 in H; discriminate.
 rewrite N_to_Z2P, H0; auto with zarith.
 Qed.

 Definition irred n d :=        
   let gcd := N.gcd (Zabs_N n) d in
   match N.compare gcd N.one with 
     | Gt => (Z.div n (Z_of_N gcd), N.div d gcd)
     | _ => (n, d)
   end.

 Lemma spec_irred : forall n d, exists g, 
  let (n',d') := irred n d in 
  (Z.to_Z n' * g = Z.to_Z n)%Z /\ (N.to_Z d' * g = N.to_Z d)%Z.
 Proof.
 intros.
 unfold irred; nzsimpl; simpl.
 destr_zcompare.
 exists 1%Z; nzsimpl; auto.
 exists 0%Z; nzsimpl.
 assert (Zgcd (Z.to_Z n) (N.to_Z d) = 0%Z).
  generalize (Zgcd_is_pos (Z.to_Z n) (N.to_Z d)); romega.
 clear H.
 split.
 symmetry; apply (Zgcd_inv_0_l _ _ H0).
 symmetry; apply (Zgcd_inv_0_r _ _ H0).
 exists (Zgcd (Z.to_Z n) (N.to_Z d)).
 simpl.
 split.
 simpl_zdiv; nzsimpl.
 destruct (Zgcd_is_gcd (Z.to_Z n) (N.to_Z d)).
 rewrite Zmult_comm; symmetry; apply Zdivide_Zdiv_eq; auto with zarith.
 simpl_ndiv; nzsimpl.
 destruct (Zgcd_is_gcd (Z.to_Z n) (N.to_Z d)).
 rewrite Zmult_comm; symmetry; apply Zdivide_Zdiv_eq; auto with zarith.
 Qed.

 Lemma spec_irred_zero : forall n d, 
   (N.to_Z d = 0)%Z <-> (N.to_Z (snd (irred n d)) = 0)%Z.
 Proof.
 intros.
 unfold irred.
 split.
 nzsimpl; intros.
 destr_zcompare; auto.
 simpl.
 simpl_ndiv; nzsimpl.
 rewrite H, Zdiv_0_l; auto.
 nzsimpl; destr_zcompare; simpl; auto.
 simpl_ndiv; nzsimpl.
 intros.
 generalize (N.spec_pos d); intros.
 destruct (N.to_Z d); auto.
 assert (0 < 0)%Z.
  rewrite <- H0 at 2.
  apply Zgcd_div_pos; auto with zarith.
  compute; auto.
 discriminate.
 compute in H1; elim H1; auto.
 Qed.

 Lemma strong_spec_irred : forall n d, 
  (N.to_Z d <> 0%Z) -> 
  let (n',d') := irred n d in Zgcd (Z.to_Z n') (N.to_Z d') = 1%Z.
 Proof.
 unfold irred; intros.
 nzsimpl.
 destr_zcompare; simpl; auto.
 elim H.
 apply (Zgcd_inv_0_r (Z.to_Z n)).
 generalize (Zgcd_is_pos (Z.to_Z n) (N.to_Z d)); romega.

 simpl_ndiv; simpl_zdiv; nzsimpl.
 rewrite Zgcd_1_rel_prime.
 apply Zis_gcd_rel_prime.
 generalize (N.spec_pos d); romega.
 generalize (Zgcd_is_pos (Z.to_Z n) (N.to_Z d)); romega.
 apply Zgcd_is_gcd; auto.
 Qed.

 Definition mul_norm_Qz_Qq z n d := 
   if Z.eq_bool z Z.zero then zero 
   else
    let gcd := N.gcd (Zabs_N z) d in
    match N.compare gcd N.one with
      | Gt => 
        let z := Z.div z (Z_of_N gcd) in
        let d := N.div d gcd in
        if N.eq_bool d N.one then Qz (Z.mul z n) else Qq (Z.mul z n) d
      | _  => Qq (Z.mul z n) d
    end.

 Definition mul_norm (x y: t): t := 
 match x, y with
 | Qz zx, Qz zy => Qz (Z.mul zx zy)
 | Qz zx, Qq ny dy => mul_norm_Qz_Qq zx ny dy
 | Qq nx dx, Qz zy => mul_norm_Qz_Qq zy nx dx
 | Qq nx dx, Qq ny dy => 
    let (nx, dy) := irred nx dy in 
    let (ny, dx) := irred ny dx in 
    let d := N.mul dx dy in
    if N.eq_bool d N.one then Qz (Z.mul ny nx) else Qq (Z.mul ny nx) d
 end.

 Lemma spec_mul_norm_Qz_Qq : forall z n d, 
   [mul_norm_Qz_Qq z n d] == [Qq (Z.mul z n) d].
 Proof.
 intros z n d; unfold mul_norm_Qz_Qq; nzsimpl; rewrite Zcompare_gt.
 destr_zeq_bool; intros Hz; nzsimpl.
 qsimpl; rewrite Hz; auto.
 assert (Hd := N.spec_pos d).
 destruct Z_le_gt_dec.
 qsimpl.
 rewrite norm_denum.
 qsimpl.
 simpl_ndiv in *; nzsimpl.
 rewrite (Zdiv_gcd_zero _ _ H0 H) in z0; discriminate.
 simpl_ndiv in *; nzsimpl.
 rewrite H, Zdiv_0_l in H0; elim H0; auto.
 rewrite 2 N_to_Z2P; auto.
 simpl_ndiv; simpl_zdiv; nzsimpl.
 rewrite (Zmult_comm (Z.to_Z z)), <- 2 Zmult_assoc.
 rewrite <- Zgcd_div_swap0; auto with zarith; ring.
 Qed.

 Lemma strong_spec_mul_norm_Qz_Qq : forall z n d, 
   Reduced (Qq n d) -> Reduced (mul_norm_Qz_Qq z n d).
 Proof.
 unfold Reduced; intros z n d.
 rewrite 2 strong_spec_red, 2 Qred_iff.
 simpl; nzsimpl.
 destr_neq_bool; intros Hd H; simpl in *; nzsimpl.
 
 unfold mul_norm_Qz_Qq; nzsimpl; rewrite Zcompare_gt.
 destr_zeq_bool; intros Hz; simpl; nzsimpl; simpl; auto.
 destruct Z_le_gt_dec.
 simpl; nzsimpl.
 destr_neq_bool; simpl; nzsimpl; auto.
 intros H'; elim H'; auto.
 destr_neq_bool; simpl; nzsimpl.
 simpl_ndiv; nzsimpl; rewrite Hd, Zdiv_0_l; discriminate.
 intros _.
 destr_neq_bool; simpl; nzsimpl; auto.
 simpl_ndiv; nzsimpl; rewrite Hd, Zdiv_0_l; intro H'; elim H'; auto.

 rewrite N_to_Z2P in H; auto.
 unfold mul_norm_Qz_Qq; nzsimpl; rewrite Zcompare_gt.
 destr_zeq_bool; intros Hz; simpl; nzsimpl; simpl; auto.
 destruct Z_le_gt_dec as [H'|H'].
 simpl; nzsimpl.
 destr_neq_bool; simpl; nzsimpl; auto.
 intros.
 rewrite N_to_Z2P; auto.
 apply Zgcd_mult_rel_prime; auto.
  generalize (Zgcd_inv_0_l (Z.to_Z z) (N.to_Z d))
    (Zgcd_is_pos (Z.to_Z z) (N.to_Z d)); romega.
 destr_neq_bool; simpl; nzsimpl; auto.
 simpl_ndiv; simpl_zdiv; nzsimpl.
 intros.
 destr_neq_bool; simpl; nzsimpl; auto.
 simpl_ndiv in *; nzsimpl.
 intros.
 rewrite Z2P_correct.
 apply Zgcd_mult_rel_prime.
 rewrite Zgcd_1_rel_prime.
 apply Zis_gcd_rel_prime.
 generalize (N.spec_pos d); romega.
 generalize (Zgcd_is_pos (Z.to_Z z) (N.to_Z d)); romega.
 apply Zgcd_is_gcd.
 destruct (Zgcd_is_gcd (Z.to_Z z) (N.to_Z d)) as [ (z0,Hz0) (d0,Hd0) Hzd].
 replace (N.to_Z d / Zgcd (Z.to_Z z) (N.to_Z d))%Z with d0.
 rewrite Zgcd_1_rel_prime in *.
 apply bezout_rel_prime.
 destruct (rel_prime_bezout _ _ H) as [u v Huv].
 apply Bezout_intro with u (v*(Zgcd (Z.to_Z z) (N.to_Z d)))%Z.
 rewrite <- Huv; rewrite Hd0 at 2; ring.
 rewrite Hd0 at 1.
 symmetry; apply Z_div_mult_full; auto with zarith.
 apply Zgcd_div_pos.
 generalize (N.spec_pos d); romega.
 generalize (Zgcd_is_pos (Z.to_Z z) (N.to_Z d)); romega.
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
 simpl snd in *; destruct Hg as [Hg1 Hg2]; destruct Hg' as [Hg1' Hg2'].
 rewrite norm_denum.
 qsimpl.

 elim H; destruct (Zmult_integral _ _ H0) as [Eq|Eq].
 rewrite <- Hz' in Eq; rewrite Eq; simpl; auto.
 rewrite <- Hz in Eq; rewrite Eq; nzsimpl; auto.

 elim H0; destruct (Zmult_integral _ _ H) as [Eq|Eq].
 rewrite Hz' in Eq; rewrite Eq; simpl; auto.
 rewrite Hz in Eq; rewrite Eq; nzsimpl; auto.

 rewrite 2 Z2P_correct.
 rewrite <- Hg1, <- Hg2, <- Hg1', <- Hg2'; ring.

 assert (0 <= N.to_Z d2 * N.to_Z d1)%Z 
  by (apply Zmult_le_0_compat; apply N.spec_pos).
 romega.
 assert (0 <= N.to_Z dx * N.to_Z dy)%Z 
  by (apply Zmult_le_0_compat; apply N.spec_pos).
 romega.
 Qed.

 Theorem strong_spec_mul_norm : forall x y,
  Reduced x -> Reduced y -> Reduced (mul_norm x y).
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
 simpl snd in *; destruct Hg as [Hg1 Hg2]; destruct Hg' as [Hg1' Hg2'].
 destr_neq_bool; simpl; nzsimpl; intros; auto.
 destr_neq_bool; simpl; nzsimpl; intros; auto.

 revert H H0.
 rewrite 2 strong_spec_red, 2 Qred_iff; simpl.
 destr_neq_bool; simpl; nzsimpl; intros.
 rewrite Hz in H; rewrite H in H2; nzsimpl; elim H2; auto.
 rewrite Hz' in H0; rewrite H0 in H2; nzsimpl; elim H2; auto.
 rewrite Hz in H; rewrite H in H2; nzsimpl; elim H2; auto.

 rewrite N_to_Z2P in *; auto.
 rewrite Z2P_correct.

 apply Zgcd_mult_rel_prime; rewrite Zgcd_comm;
  apply Zgcd_mult_rel_prime; rewrite Zgcd_comm; auto.
 
 rewrite Zgcd_1_rel_prime in *.
 apply bezout_rel_prime.
 destruct (rel_prime_bezout _ _ H4) as [u v Huv].
 apply Bezout_intro with (u*g')%Z (v*g)%Z.
 rewrite <- Huv, <- Hg1', <- Hg2. ring.

 rewrite Zgcd_1_rel_prime in *.
 apply bezout_rel_prime.
 destruct (rel_prime_bezout _ _ H3) as [u v Huv].
 apply Bezout_intro with (u*g)%Z (v*g')%Z.
 rewrite <- Huv, <- Hg2', <- Hg1. ring.

 assert (0 <= N.to_Z d2 * N.to_Z d1)%Z.
  apply Zmult_le_0_compat; apply N.spec_pos.
 romega.
 Qed.

 Definition inv (x: t): t := 
 match x with
 | Qz z => 
   match Z.compare Z.zero z with 
     | Eq => zero
     | Lt => Qq Z.one (Zabs_N z)
     | Gt => Qq Z.minus_one (Zabs_N z)
   end
 | Qq n d => 
   match Z.compare Z.zero n with
     | Eq => zero
     | Lt => Qq (Z_of_N d) (Zabs_N n)
     | Gt => Qq (Z.opp (Z_of_N d)) (Zabs_N n)
   end
 end.

 Theorem spec_inv : forall x, [inv x] == /[x].
 Proof.
 destruct x as [ z | n d ].
 (* Qz z *)
 simpl.
 rewrite Zcompare_spec_alt; destr_zcompare.
 (* 0 = z *)
 rewrite <- H.
 simpl; nzsimpl; compute; auto.
 (* 0 < z *)
 simpl.
 destr_neq_bool; nzsimpl; [ intros; rewrite Zabs_eq in *; romega | intros _ ].
 set (z':=Z.to_Z z) in *; clearbody z'.
 red; simpl.
 rewrite Zabs_eq by romega.
 rewrite Z2P_correct by auto.
 unfold Qinv; simpl; destruct z'; simpl; auto; discriminate.
 (* 0 > z *)
 simpl.
 destr_neq_bool; nzsimpl; [ intros; rewrite Zabs_non_eq in *; romega | intros _ ].
 set (z':=Z.to_Z z) in *; clearbody z'.
 red; simpl.
 rewrite Zabs_non_eq by romega.
 rewrite Z2P_correct by romega.
 unfold Qinv; simpl; destruct z'; simpl; auto; discriminate.
 (* Qq n d *)
 simpl.
 rewrite Zcompare_spec_alt; destr_zcompare.
 (* 0 = n *)
 rewrite <- H.
 simpl; nzsimpl.
 destr_neq_bool; intros; compute; auto.
 (* 0 < n *)
 simpl.
 destr_neq_bool; nzsimpl; intros.
 intros; rewrite Zabs_eq in *; romega.
 intros; rewrite Zabs_eq in *; romega.
 clear H1.
 rewrite H0.
 compute; auto.
 clear H1.
 set (n':=Z.to_Z n) in *; clearbody n'.
 rewrite Zabs_eq by romega.
 red; simpl.
 rewrite Z2P_correct by auto.
 unfold Qinv; simpl; destruct n'; simpl; auto; try discriminate.
 rewrite Zpos_mult_morphism, N_to_Z2P; auto.
 (* 0 > n *)
 simpl.
 destr_neq_bool; nzsimpl; intros.
 intros; rewrite Zabs_non_eq in *; romega.
 intros; rewrite Zabs_non_eq in *; romega.
 clear H1.
 red; nzsimpl; rewrite H0; compute; auto.
 clear H1.
 set (n':=Z.to_Z n) in *; clearbody n'.
 red; simpl; nzsimpl.
 rewrite Zabs_non_eq by romega.
 rewrite Z2P_correct by romega.
 unfold Qinv; simpl; destruct n'; simpl; auto; try discriminate.
 assert (T : forall x, Zneg x = Zopp (Zpos x)) by auto.
 rewrite T, Zpos_mult_morphism, N_to_Z2P; auto; ring.
 Qed.

 Definition inv_norm (x: t): t := 
   match x with
     | Qz z => 
       match Z.compare Z.zero z with 
         | Eq => zero
         | Lt => Qq Z.one (Zabs_N z)
         | Gt => Qq Z.minus_one (Zabs_N z)
       end
     | Qq n d => 
       if N.eq_bool d N.zero then zero else 
       match Z.compare Z.zero n with 
         | Eq => zero
         | Lt => 
           match Z.compare n Z.one with 
             | Gt => Qq (Z_of_N d) (Zabs_N n)
             | _ => Qz (Z_of_N d)
           end
         | Gt => 
           match Z.compare n Z.minus_one with 
             | Lt => Qq (Z.opp (Z_of_N d)) (Zabs_N n)
             | _ => Qz (Z.opp (Z_of_N d))
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
 rewrite Zcompare_spec_alt; destr_zcompare; auto with qarith.
 (* Qq n d *)
 simpl; nzsimpl; destr_neq_bool.
 destr_zcompare; simpl; auto with qarith.
 destr_neq_bool; nzsimpl; auto with qarith.
 intros _ Hd; rewrite Hd; auto with qarith.
 destr_neq_bool; nzsimpl; auto with qarith.
 intros _ Hd; rewrite Hd; auto with qarith.
 (* 0 < n *)
 destr_zcompare; auto with qarith.
 destr_zcompare; nzsimpl; simpl; auto with qarith; intros.
 destr_neq_bool; nzsimpl; [ intros; rewrite Zabs_eq in *; romega | intros _ ].
 rewrite H0; auto with qarith.
 romega.
 (* 0 > n *)
 destr_zcompare; nzsimpl; simpl; auto with qarith.
 destr_neq_bool; nzsimpl; [ intros; rewrite Zabs_non_eq in *; romega | intros _ ].
 rewrite H0; auto with qarith.
 romega.
 Qed.

 Theorem strong_spec_inv_norm : forall x, Reduced x -> Reduced (inv_norm x).
 Proof.
 unfold Reduced. 
 intros.
 destruct x as [ z | n d ].
 (* Qz *)
 simpl; nzsimpl.
 rewrite strong_spec_red, Qred_iff.
 destr_zcompare; simpl; nzsimpl; auto.
 destr_neq_bool; nzsimpl; simpl; auto.
 destr_neq_bool; nzsimpl; simpl; auto.
 (* Qq n d *)
 rewrite strong_spec_red, Qred_iff in H; revert H.
 simpl; nzsimpl.
 destr_neq_bool; nzsimpl; auto with qarith.
 destr_zcompare; simpl; nzsimpl; auto; intros.
 (* 0 < n *)
 destr_zcompare; simpl; nzsimpl; auto.
 destr_neq_bool; nzsimpl; simpl; auto.
 rewrite Zabs_eq; romega.
 intros _.
 rewrite strong_spec_norm; simpl; nzsimpl.
 destr_neq_bool; nzsimpl.
 rewrite Zabs_eq; romega.
 intros _.
 rewrite Qred_iff.
 simpl.
 rewrite Zabs_eq; auto with zarith.
 rewrite N_to_Z2P in *; auto.
 rewrite Z2P_correct; auto with zarith.
 rewrite Zgcd_comm; auto.
 (* 0 > n *)
 destr_neq_bool; nzsimpl; simpl; auto; intros.
 destr_zcompare; simpl; nzsimpl; auto.
 destr_neq_bool; nzsimpl.
 rewrite Zabs_non_eq; romega.
 intros _.
 rewrite strong_spec_norm; simpl; nzsimpl.
 destr_neq_bool; nzsimpl.
 rewrite Zabs_non_eq; romega.
 intros _.
 rewrite Qred_iff.
 simpl.
 rewrite N_to_Z2P in *; auto.
 rewrite Z2P_correct; auto with zarith.
 intros.
 rewrite Zgcd_comm, Zgcd_Zabs, Zgcd_comm.
 apply Zis_gcd_gcd; auto with zarith.
 apply Zis_gcd_minus.
 rewrite Zopp_involutive, <- H1; apply Zgcd_is_gcd.
 rewrite Zabs_non_eq; romega.
 Qed.

 Definition div x y := mul x (inv y).

 Theorem spec_div x y: [div x y] == [x] / [y].
 Proof.
 intros x y; unfold div; rewrite spec_mul; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv; auto.
 Qed.

 Definition div_norm x y := mul_norm x (inv_norm y).

 Theorem spec_div_norm x y: [div_norm x y] == [x] / [y].
 Proof.
 intros x y; unfold div_norm; rewrite spec_mul_norm; auto.
 unfold Qdiv; apply Qmult_comp.
 apply Qeq_refl.
 apply spec_inv_norm; auto.
 Qed.
 
 Theorem strong_spec_div_norm : forall x y, 
   Reduced x -> Reduced y -> Reduced (div_norm x y).
 Proof.
 intros; unfold div_norm.
 apply strong_spec_mul_norm; auto.
 apply strong_spec_inv_norm; auto.
 Qed.

 Definition square (x: t): t :=
  match x with
  | Qz zx => Qz (Z.square zx)
  | Qq nx dx => Qq (Z.square nx) (N.square dx)
  end.

 Theorem spec_square : forall x, [square x] == [x] ^ 2.
 Proof.
 destruct x as [ z | n d ].
 simpl; rewrite Z.spec_square; red; auto.
 simpl.
 destr_neq_bool; nzsimpl; intros.
 apply Qeq_refl.
 rewrite N.spec_square in *; nzsimpl.
 contradict H; elim (Zmult_integral _ _ H0); auto.
 rewrite N.spec_square in *; nzsimpl.
 rewrite H in H0; simpl in H0; elim H0; auto.
 assert (0 < N.to_Z d)%Z by (generalize (N.spec_pos d); romega).
 clear H H0.
 rewrite Z.spec_square, N.spec_square.  
 red; simpl.
 rewrite Zpos_mult_morphism; rewrite !Z2P_correct; auto.
 apply Zmult_lt_0_compat; auto.
 Qed.

 Definition power_pos (x : t) p : t :=
  match x with
  | Qz zx => Qz (Z.power_pos zx p)
  | Qq nx dx => Qq (Z.power_pos nx p) (N.power_pos dx p)
  end.
 
 Theorem spec_power_pos : forall x p, [power_pos x p] == [x] ^ Zpos p.
 Proof.
 intros [ z | n d ] p; unfold power_pos.
 (* Qz *)
 simpl.
 rewrite Z.spec_power_pos.
 rewrite Qpower_decomp.
 red; simpl; f_equal.
 rewrite Zpower_pos_1_l; auto.
 (* Qq *)
 simpl.
 rewrite Z.spec_power_pos.
 destr_neq_bool; nzsimpl; intros.
 apply Qeq_sym; apply Qpower_positive_0.
 rewrite N.spec_power_pos in *.
 assert (0 < N.to_Z d ^ ' p)%Z.
  apply Zpower_gt_0; auto with zarith.
  generalize (N.spec_pos d); romega.
 romega.
 rewrite N.spec_power_pos, H in *.
 rewrite Zpower_0_l in H0; [ elim H0; auto | discriminate ].
 rewrite Qpower_decomp.
 red; simpl; do 3 f_equal.
 rewrite Z2P_correct by (generalize (N.spec_pos d); romega).
 rewrite N.spec_power_pos. auto.
 Qed.

 Theorem strong_spec_power_pos : forall x p, 
  Reduced x -> Reduced (power_pos x p).
 Proof.
 destruct x as [z | n d]; simpl; intros.
 red; simpl; auto.
 red; simpl; intros.
 rewrite strong_spec_norm; simpl.
 destr_neq_bool; nzsimpl; intros.
 simpl; auto.
 rewrite Qred_iff.
 revert H.
 unfold Reduced; rewrite strong_spec_red, Qred_iff; simpl.
 destr_neq_bool; nzsimpl; simpl; intros.
 rewrite N.spec_power_pos in H0.
 elim H0; rewrite H; rewrite Zpower_0_l; auto; discriminate.
 rewrite N_to_Z2P in *; auto.
 rewrite N.spec_power_pos, Z.spec_power_pos; auto.
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

 Theorem strong_spec_power_norm : forall x z, 
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

 Definition to_Qc q := !! [q].

 Notation "[[ x ]]" := (to_Qc x).

 Theorem strong_spec_of_Qc : forall q, [of_Qc q] = q.
 Proof.
 intros (q,Hq); intros.
 unfold of_Qc; rewrite strong_spec_of_Q; auto.
 Qed.

 Lemma strong_spec_of_Qc_bis : forall q, Reduced (of_Qc q).
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
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] + [y])).
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
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] + [y])).
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
 intros x y; unfold sub; rewrite spec_addc; auto.
 rewrite spec_oppc; ring.
 Qed.

 Theorem spec_sub_normc x y:
   [[sub_norm x y]] = [[x]] - [[y]].
 Proof.
 intros x y; unfold sub_norm; rewrite spec_add_normc; auto.
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
 unfold Qcopp, Q2Qc; rewrite Qred_correct; auto with qarith.
 Qed.

 Theorem spec_mulc x y:
  [[mul x y]] = [[x]] * [[y]].
 Proof.
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] * [y])).
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
 intros x y; unfold to_Qc.
 apply trans_equal with (!! ([x] * [y])).
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
 intros x; unfold to_Qc.
 apply trans_equal with (!! (/[x])).
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
 intros x; unfold to_Qc.
 apply trans_equal with (!! (/[x])).
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
 intros x y; unfold div; rewrite spec_mulc; auto.
 unfold Qcdiv; apply f_equal2 with (f := Qcmult); auto.
 apply spec_invc; auto. 
 Qed.

 Theorem spec_div_normc x y: [[div_norm x y]] = [[x]] / [[y]].
 Proof.
 intros x y; unfold div_norm; rewrite spec_mul_normc; auto.
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
 unfold Qcinv, Q2Qc; rewrite Qred_correct; auto with qarith.
 Qed.

 Theorem spec_squarec x: [[square x]] =  [[x]]^2.
 Proof.
 intros x; unfold to_Qc.
 apply trans_equal with (!! ([x]^2)).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_square; auto.
 simpl Qcpower.
 replace (!! [x] * 1) with (!![x]); try ring.
 simpl.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 Qed.

 Theorem spec_power_posc x p:
   [[power_pos x p]] = [[x]] ^ nat_of_P p.
 Proof.
 intros x p; unfold to_Qc.
 apply trans_equal with (!! ([x]^Zpos p)).
 unfold Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete; apply spec_power_pos; auto.
 induction p using Pind.
 simpl; ring.
 rewrite nat_of_P_succ_morphism; simpl Qcpower.
 rewrite <- IHp; clear IHp.
 unfold Qcmult, Q2Qc.
 apply Qc_decomp; intros _ _; unfold this.
 apply Qred_complete.
 setoid_replace ([x] ^ ' Psucc p)%Q with ([x] * [x] ^ ' p)%Q.
 apply Qmult_comp; apply Qeq_sym; apply Qred_correct.
 simpl.
 rewrite Pplus_one_succ_l.
 rewrite Qpower_plus_positive; simpl; apply Qeq_refl.
 Qed.

End Make.

