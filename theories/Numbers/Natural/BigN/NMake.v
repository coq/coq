(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(** * NMake *)

(** From a cyclic Z/nZ representation to arbitrary precision natural numbers.*)

(** NB: This file contain the part which is independent from the underlying
    representation. The representation-dependent (and macro-generated) part
    is now in [NMake_gen]. *)

Require Import Bool BigNumPrelude ZArith Nnat Ndigits CyclicAxioms DoubleType
  Nbasic Wf_nat StreamMemo NSig NMake_gen.

Module Make (W0:CyclicType) <: NType.

 (** Let's include the macro-generated part. Even if we can't functorize
     things (due to Eval red_t below), the rest of the module only uses
     elements mentionned in interface [NAbstract]. *)

 Include NMake_gen.Make W0.

 Open Scope Z_scope.

 Local Notation "[ x ]" := (to_Z x).

 Definition eq (x y : t) := [x] = [y].

 Declare Reduction red_t :=
  lazy beta iota delta
   [iter_t reduce same_level mk_t mk_t_S succ_t dom_t dom_op].

 Ltac red_t :=
  match goal with |- ?u => let v := (eval red_t in u) in change v end.

 (** * Generic results *)

 Tactic Notation "destr_t" constr(x) "as" simple_intropattern(pat) :=
  destruct (destr_t x) as pat; cbv zeta;
  rewrite ?iter_mk_t, ?spec_mk_t, ?spec_reduce.

 Lemma spec_same_level : forall A (P:Z->Z->A->Prop)
  (f : forall n, dom_t n -> dom_t n -> A),
  (forall n x y, P (ZnZ.to_Z x) (ZnZ.to_Z y) (f n x y)) ->
  forall x y, P [x] [y] (same_level f x y).
 Proof.
 intros. apply spec_same_level_dep with (P:=fun _ => P); auto.
 Qed.

 Theorem spec_pos: forall x, 0 <= [x].
 Proof.
 intros x. destr_t x as (n,x). now case (ZnZ.spec_to_Z x).
 Qed.

 Lemma digits_dom_op_incr : forall n m, (n<=m)%nat ->
  (ZnZ.digits (dom_op n) <= ZnZ.digits (dom_op m))%positive.
 Proof.
 intros.
 change (Zpos (ZnZ.digits (dom_op n)) <= Zpos (ZnZ.digits (dom_op m))).
 rewrite !digits_dom_op, !Pshiftl_nat_Zpower.
 apply Z.mul_le_mono_nonneg_l; auto with zarith.
 apply Z.pow_le_mono_r; auto with zarith.
 Qed.

 Definition to_N (x : t) := Z.to_N (to_Z x).

 (** * Zero, One *)

 Definition zero := mk_t O ZnZ.zero.
 Definition one := mk_t O ZnZ.one.

 Theorem spec_0: [zero] = 0.
 Proof.
 unfold zero. rewrite spec_mk_t. exact ZnZ.spec_0.
 Qed.

 Theorem spec_1: [one] = 1.
 Proof.
 unfold one. rewrite spec_mk_t. exact ZnZ.spec_1.
 Qed.

 (** * Successor *)

 (** NB: it is crucial here and for the rest of this file to preserve
     the let-in's. They allow to pre-compute once and for all the
     field access to Z/nZ initial structures (when n=0..6). *)

 Local Notation succn := (fun n =>
  let op := dom_op n in
  let succ_c := ZnZ.succ_c in
  let one := ZnZ.one in
  fun x => match succ_c x with
   | C0 r => mk_t n r
   | C1 r => mk_t_S n (WW one r)
  end).

 Definition succ : t -> t := Eval red_t in iter_t succn.

 Lemma succ_fold : succ = iter_t succn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_succ: forall n, [succ n] = [n] + 1.
 Proof.
  intros x. rewrite succ_fold. destr_t x as (n,x).
  generalize (ZnZ.spec_succ_c x); case ZnZ.succ_c.
  intros. rewrite spec_mk_t. assumption.
  intros. unfold interp_carry in *.
  rewrite spec_mk_t_S. simpl. rewrite ZnZ.spec_1. assumption.
 Qed.

 (** Two *)

 (** Not really pretty, but since W0 might be Z/2Z, we're not sure
     there's a proper 2 there. *)

 Definition two := succ one.

 Lemma spec_2 : [two] = 2.
 Proof.
  unfold two. now rewrite spec_succ, spec_1.
 Qed.

 (** * Addition *)

 Local Notation addn := (fun n =>
  let op := dom_op n in
  let add_c := ZnZ.add_c in
  let one := ZnZ.one in
  fun x y =>match add_c x y with
  | C0 r => mk_t n r
  | C1 r => mk_t_S n (WW one r)
  end).

 Definition add : t -> t -> t := Eval red_t in same_level addn.

 Lemma add_fold : add = same_level addn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_add: forall x y, [add x y] = [x] + [y].
 Proof.
  intros x y. rewrite add_fold. apply spec_same_level; clear x y.
  intros n x y. cbv beta iota zeta.
  generalize (ZnZ.spec_add_c x y); case ZnZ.add_c; intros z H.
  rewrite spec_mk_t. assumption.
  rewrite spec_mk_t_S. unfold interp_carry in H.
  simpl. rewrite ZnZ.spec_1. assumption.
 Qed.

 (** * Predecessor *)

 Local Notation predn := (fun n =>
  let pred_c := ZnZ.pred_c in
  fun x => match pred_c x with
   | C0 r => reduce n r
   | C1 _ => zero
  end).

 Definition pred : t -> t := Eval red_t in iter_t predn.

 Lemma pred_fold : pred = iter_t predn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_pred_pos : forall x, 0 < [x] -> [pred x] = [x] - 1.
 Proof.
  intros x. rewrite pred_fold. destr_t x as (n,x). intros H.
  generalize (ZnZ.spec_pred_c x); case ZnZ.pred_c; intros y H'.
  rewrite spec_reduce. assumption.
  exfalso. unfold interp_carry in *.
  generalize (ZnZ.spec_to_Z x) (ZnZ.spec_to_Z y); auto with zarith.
 Qed.

 Theorem spec_pred0 : forall x, [x] = 0 -> [pred x] = 0.
 Proof.
  intros x. rewrite pred_fold. destr_t x as (n,x). intros H.
  generalize (ZnZ.spec_pred_c x); case ZnZ.pred_c; intros y H'.
  rewrite spec_reduce.
  unfold interp_carry in H'.
  generalize (ZnZ.spec_to_Z y); auto with zarith.
  exact spec_0.
 Qed.

 Lemma spec_pred x : [pred x] = Z.max 0 ([x]-1).
 Proof.
 rewrite Z.max_comm.
 destruct (Z.max_spec ([x]-1) 0) as [(H,->)|(H,->)].
 - apply spec_pred0; generalize (spec_pos x); auto with zarith.
 - apply spec_pred_pos; auto with zarith.
 Qed.

 (** * Subtraction *)

 Local Notation subn := (fun n =>
  let sub_c := ZnZ.sub_c in
  fun x y => match sub_c x y with
  | C0 r => reduce n r
  | C1 r => zero
  end).

 Definition sub : t -> t -> t := Eval red_t in same_level subn.

 Lemma sub_fold : sub = same_level subn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_sub_pos : forall x y, [y] <= [x] -> [sub x y] = [x] - [y].
 Proof.
  intros x y. rewrite sub_fold. apply spec_same_level. clear x y.
  intros n x y. simpl.
  generalize (ZnZ.spec_sub_c x y); case ZnZ.sub_c; intros z H LE.
  rewrite spec_reduce. assumption.
  unfold interp_carry in H.
  exfalso.
  generalize (ZnZ.spec_to_Z z); auto with zarith.
 Qed.

 Theorem spec_sub0 : forall x y, [x] < [y] -> [sub x y] = 0.
 Proof.
  intros x y. rewrite sub_fold. apply spec_same_level. clear x y.
  intros n x y. simpl.
  generalize (ZnZ.spec_sub_c x y); case ZnZ.sub_c; intros z H LE.
  rewrite spec_reduce.
  unfold interp_carry in H.
  generalize (ZnZ.spec_to_Z z); auto with zarith.
  exact spec_0.
 Qed.

 Lemma spec_sub : forall x y, [sub x y] = Z.max 0 ([x]-[y]).
 Proof.
 intros. destruct (Z.le_gt_cases [y] [x]).
 rewrite Z.max_r; auto with zarith. apply spec_sub_pos; auto.
 rewrite Z.max_l; auto with zarith. apply spec_sub0; auto.
 Qed.

 (** * Comparison *)

 Definition comparen_m n :
  forall m, word (dom_t n) (S m) -> dom_t n -> comparison :=
  let op := dom_op n in
  let zero := ZnZ.zero (Ops:=op) in
  let compare := ZnZ.compare (Ops:=op) in
  let compare0 := compare zero in
  fun m => compare_mn_1 (dom_t n) (dom_t n) zero compare compare0 compare (S m).

 Let spec_comparen_m:
  forall n m (x : word (dom_t n) (S m)) (y : dom_t n),
   comparen_m n m x y = Z.compare (eval n (S m) x) (ZnZ.to_Z y).
 Proof.
  intros n m x y.
  unfold comparen_m, eval.
  rewrite nmake_double.
  apply spec_compare_mn_1.
  exact ZnZ.spec_0.
  intros. apply ZnZ.spec_compare.
  exact ZnZ.spec_to_Z.
  exact ZnZ.spec_compare.
  exact ZnZ.spec_compare.
  exact ZnZ.spec_to_Z.
 Qed.

 Definition comparenm n m wx wy :=
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
    ZnZ.compare
       (castm (diff_r n m) (extend_tr wx (snd d)))
       (castm (diff_l n m) (extend_tr wy (fst d))).

 Local Notation compare_folded :=
   (iter_sym _
      (fun n => ZnZ.compare (Ops:=dom_op n))
      comparen_m
      comparenm
      CompOpp).

 Definition compare : t -> t -> comparison :=
  Eval lazy beta iota delta [iter_sym dom_op dom_t comparen_m] in
  compare_folded.

 Lemma compare_fold : compare = compare_folded.
 Proof.
 lazy beta iota delta [iter_sym dom_op dom_t comparen_m]. reflexivity.
 Qed.

 Theorem spec_compare : forall x y,
   compare x y = Z.compare [x] [y].
 Proof.
  intros x y. rewrite compare_fold. apply spec_iter_sym; clear x y.
  intros. apply ZnZ.spec_compare.
  intros. cbv beta zeta. apply spec_comparen_m.
  intros n m x y; unfold comparenm.
  rewrite (spec_cast_l n m x), (spec_cast_r n m y).
  unfold to_Z; apply ZnZ.spec_compare.
  intros. subst. now rewrite <- Z.compare_antisym.
 Qed.

 Definition eqb (x y : t) : bool :=
  match compare x y with
  | Eq => true
  | _  => false
  end.

 Theorem spec_eqb x y : eqb x y = Z.eqb [x] [y].
 Proof.
 apply eq_iff_eq_true.
 unfold eqb. rewrite Z.eqb_eq, <- Z.compare_eq_iff, spec_compare.
 split; [now destruct Z.compare | now intros ->].
 Qed.

 Definition lt (n m : t) := [n] < [m].
 Definition le (n m : t) := [n] <= [m].

 Definition ltb (x y : t) : bool :=
  match compare x y with
  | Lt => true
  | _  => false
  end.

 Theorem spec_ltb x y : ltb x y = Z.ltb [x] [y].
 Proof.
 apply eq_iff_eq_true.
 rewrite Z.ltb_lt. unfold Z.lt, ltb. rewrite spec_compare.
 split; [now destruct Z.compare | now intros ->].
 Qed.

 Definition leb (x y : t) : bool :=
  match compare x y with
  | Gt => false
  | _  => true
  end.

 Theorem spec_leb x y : leb x y = Z.leb [x] [y].
 Proof.
 apply eq_iff_eq_true.
 rewrite Z.leb_le. unfold Z.le, leb. rewrite spec_compare.
 destruct Z.compare; split; try easy. now destruct 1.
 Qed.

 Definition min (n m : t) : t := match compare n m with Gt => m | _ => n end.
 Definition max (n m : t) : t := match compare n m with Lt => m | _ => n end.

 Theorem spec_max : forall n m, [max n m] = Z.max [n] [m].
 Proof.
 intros. unfold max, Z.max. rewrite spec_compare; destruct Z.compare; reflexivity.
 Qed.

 Theorem spec_min : forall n m, [min n m] = Z.min [n] [m].
 Proof.
 intros. unfold min, Z.min. rewrite spec_compare; destruct Z.compare; reflexivity.
 Qed.

 (** * Multiplication *)

 Definition wn_mul n : forall m, word (dom_t n) (S m) -> dom_t n -> t :=
  let op := dom_op n in
  let zero := ZnZ.zero in
  let succ := ZnZ.succ (Ops:=op) in
  let add_c := ZnZ.add_c (Ops:=op) in
  let mul_c := ZnZ.mul_c (Ops:=op) in
  let ww := @ZnZ.WW _ op in
  let ow := @ZnZ.OW _ op in
  let eq0 := ZnZ.eq0 in
  let mul_add := @DoubleMul.w_mul_add _ zero succ add_c mul_c in
  let mul_add_n1 := @DoubleMul.double_mul_add_n1 _ zero ww ow mul_add in
  fun m x y =>
   let (w,r) := mul_add_n1 (S m) x y zero in
   if eq0 w then mk_t_w' n m r
   else mk_t_w' n (S m) (WW (extend n m w) r).

 Definition mulnm n m x y :=
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
     reduce_n (S mn) (ZnZ.mul_c
       (castm (diff_r n m) (extend_tr x (snd d)))
       (castm (diff_l n m) (extend_tr y (fst d)))).

 Local Notation mul_folded :=
  (iter_sym _
    (fun n => let mul_c := ZnZ.mul_c in
      fun x y => reduce (S n) (succ_t _ (mul_c x y)))
    wn_mul
    mulnm
    (fun x => x)).

 Definition mul : t -> t -> t :=
  Eval lazy beta iota delta
   [iter_sym dom_op dom_t reduce succ_t extend zeron
    wn_mul DoubleMul.w_mul_add mk_t_w'] in
  mul_folded.

 Lemma mul_fold : mul = mul_folded.
 Proof.
  lazy beta iota delta
   [iter_sym dom_op dom_t reduce succ_t extend zeron
    wn_mul  DoubleMul.w_mul_add mk_t_w']. reflexivity.
 Qed.

 Lemma spec_muln:
   forall n (x: word _ (S n)) y,
     [Nn (S n) (ZnZ.mul_c (Ops:=make_op n) x y)] = [Nn n x] * [Nn n y].
 Proof.
    intros n x y; unfold to_Z.
    rewrite <- ZnZ.spec_mul_c.
    rewrite make_op_S.
    case ZnZ.mul_c; auto.
 Qed.

 Lemma spec_mul_add_n1: forall n m x y z,
  let (q,r) := DoubleMul.double_mul_add_n1 ZnZ.zero ZnZ.WW ZnZ.OW
          (DoubleMul.w_mul_add ZnZ.zero ZnZ.succ ZnZ.add_c ZnZ.mul_c)
          (S m) x y z in
  ZnZ.to_Z q * (base (ZnZ.digits (nmake_op _ (dom_op n) (S m))))
   + eval n (S m) r =
  eval n (S m) x * ZnZ.to_Z y + ZnZ.to_Z z.
 Proof.
 intros n m x y z.
 rewrite digits_nmake.
 unfold eval. rewrite nmake_double.
 apply DoubleMul.spec_double_mul_add_n1.
 apply ZnZ.spec_0.
 exact ZnZ.spec_WW.
 exact ZnZ.spec_OW.
 apply DoubleCyclic.spec_mul_add.
 Qed.

 Lemma spec_wn_mul : forall n m x y,
   [wn_mul n m x y] = (eval n (S m) x) * ZnZ.to_Z y.
 Proof.
  intros; unfold wn_mul.
  generalize (spec_mul_add_n1 n m x y ZnZ.zero).
  case DoubleMul.double_mul_add_n1; intros q r Hqr.
  rewrite ZnZ.spec_0, Z.add_0_r in Hqr. rewrite <- Hqr.
  generalize (ZnZ.spec_eq0 q); case ZnZ.eq0; intros HH.
  rewrite HH; auto. simpl. apply spec_mk_t_w'.
  clear.
  rewrite spec_mk_t_w'.
  set (m' := S m) in *.
  unfold eval.
  rewrite nmake_WW. f_equal. f_equal.
  rewrite <- spec_mk_t.
  symmetry. apply spec_extend.
 Qed.

 Theorem spec_mul : forall x y, [mul x y] = [x] * [y].
 Proof.
  intros x y. rewrite mul_fold. apply spec_iter_sym; clear x y.
   intros n x y. cbv zeta beta.
    rewrite spec_reduce, spec_succ_t, <- ZnZ.spec_mul_c; auto.
   apply spec_wn_mul.
   intros n m x y; unfold mulnm. rewrite spec_reduce_n.
    rewrite (spec_cast_l n m x), (spec_cast_r n m y).
    apply spec_muln.
   intros. rewrite Z.mul_comm; auto.
 Qed.

 (** * Division by a smaller number *)

 Definition wn_divn1 n :=
  let op := dom_op n in
  let zd := ZnZ.zdigits op in
  let zero := ZnZ.zero in
  let ww := ZnZ.WW in
  let head0 := ZnZ.head0 in
  let add_mul_div := ZnZ.add_mul_div in
  let div21 := ZnZ.div21 in
  let compare := ZnZ.compare in
  let sub := ZnZ.sub in
  let ddivn1 :=
    DoubleDivn1.double_divn1 zd zero ww head0 add_mul_div div21 compare sub in
  fun m x y => let (u,v) := ddivn1 (S m) x y in (mk_t_w' n m u, mk_t n v).

 Definition div_gtnm n m wx wy :=
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
    let (q, r):= ZnZ.div_gt
         (castm (diff_r n m) (extend_tr wx (snd d)))
         (castm (diff_l n m) (extend_tr wy (fst d))) in
    (reduce_n mn q, reduce_n mn r).

 Local Notation div_gt_folded :=
   (iter _
     (fun n => let div_gt := ZnZ.div_gt in
       fun x y => let (u,v) := div_gt x y in (reduce n u, reduce n v))
     (fun n =>
       let div_gt := ZnZ.div_gt in
       fun m x y =>
         let y' := DoubleBase.get_low (zeron n) (S m) y in
         let (u,v) := div_gt x y' in (reduce n u, reduce n v))
      wn_divn1
      div_gtnm).

 Definition div_gt :=
  Eval lazy beta iota delta
   [iter dom_op dom_t reduce zeron wn_divn1 mk_t_w' mk_t] in
  div_gt_folded.

 Lemma div_gt_fold : div_gt = div_gt_folded.
 Proof.
  lazy beta iota delta [iter dom_op dom_t reduce zeron wn_divn1 mk_t_w' mk_t].
  reflexivity.
 Qed.

 Lemma spec_get_endn: forall n m x y,
  eval n m x  <= [mk_t n y] ->
   [mk_t n (DoubleBase.get_low (zeron n) m x)] = eval n m x.
 Proof.
  intros n m x y H.
  unfold eval. rewrite nmake_double.
  rewrite spec_mk_t in *.
  apply DoubleBase.spec_get_low.
  apply spec_zeron.
  exact ZnZ.spec_to_Z.
  apply Z.le_lt_trans with (ZnZ.to_Z y); auto.
    rewrite <- nmake_double; auto.
  case (ZnZ.spec_to_Z y); auto.
 Qed.

 Definition spec_divn1 n :=
   DoubleDivn1.spec_double_divn1
    (ZnZ.zdigits (dom_op n)) (ZnZ.zero:dom_t n)
    ZnZ.WW ZnZ.head0
    ZnZ.add_mul_div ZnZ.div21
    ZnZ.compare ZnZ.sub ZnZ.to_Z
    ZnZ.spec_to_Z
    ZnZ.spec_zdigits
    ZnZ.spec_0 ZnZ.spec_WW ZnZ.spec_head0
    ZnZ.spec_add_mul_div ZnZ.spec_div21
    ZnZ.spec_compare ZnZ.spec_sub.

 Lemma spec_div_gt_aux : forall x y, [x] > [y] -> 0 < [y] ->
   let (q,r) := div_gt x y in
   [x] = [q] * [y] + [r] /\ 0 <= [r] < [y].
 Proof.
  intros x y. rewrite div_gt_fold. apply spec_iter; clear x y.
   intros n x y H1 H2. simpl.
    generalize (ZnZ.spec_div_gt x y H1 H2); case ZnZ.div_gt.
    intros u v. rewrite 2 spec_reduce. auto.
   intros n m x y H1 H2. cbv zeta beta.
    generalize (ZnZ.spec_div_gt x
                (DoubleBase.get_low (zeron n) (S m) y)).
    case ZnZ.div_gt.
    intros u v H3; repeat rewrite spec_reduce.
    generalize (spec_get_endn n (S m) y x). rewrite !spec_mk_t. intros H4.
    rewrite H4 in H3; auto with zarith.
   intros n m x y H1 H2.
    generalize (spec_divn1 n (S m) x y H2).
    unfold wn_divn1; case DoubleDivn1.double_divn1.
    intros u v H3.
    rewrite spec_mk_t_w', spec_mk_t.
    rewrite <- !nmake_double in H3; auto.
   intros n m x y H1 H2; unfold div_gtnm.
    generalize (ZnZ.spec_div_gt
                   (castm (diff_r n m)
                     (extend_tr x (snd (diff n m))))
                   (castm (diff_l n m)
                     (extend_tr y (fst (diff n m))))).
    case ZnZ.div_gt.
    intros xx yy HH.
    repeat rewrite spec_reduce_n.
    rewrite (spec_cast_l n m x), (spec_cast_r n m y).
    unfold to_Z; apply HH.
    rewrite (spec_cast_l n m x) in H1; auto.
    rewrite (spec_cast_r n m y) in H1; auto.
    rewrite (spec_cast_r n m y) in H2; auto.
 Qed.

 Theorem spec_div_gt: forall x y, [x] > [y] -> 0 < [y] ->
  let (q,r) := div_gt x y in
  [q] = [x] / [y] /\ [r] = [x] mod [y].
 Proof.
  intros x y H1 H2; generalize (spec_div_gt_aux x y H1 H2); case div_gt.
  intros q r (H3, H4); split.
  apply (Zdiv_unique [x] [y] [q] [r]); auto.
  rewrite Z.mul_comm; auto.
  apply (Zmod_unique [x] [y] [q] [r]); auto.
  rewrite Z.mul_comm; auto.
 Qed.

 (** * General Division *)

 Definition div_eucl (x y : t) : t * t :=
  if eqb y zero then (zero,zero) else
  match compare x y with
  | Eq => (one, zero)
  | Lt => (zero, x)
  | Gt => div_gt x y
  end.

 Theorem spec_div_eucl: forall x y,
      let (q,r) := div_eucl x y in
      ([q], [r]) = Z.div_eucl [x] [y].
 Proof.
 intros x y. unfold div_eucl.
 rewrite spec_eqb, spec_compare, spec_0.
 case Z.eqb_spec.
 intros ->. rewrite spec_0. destruct [x]; auto.
 intros H'.
 assert (H : 0 < [y]) by (generalize (spec_pos y); auto with zarith).
 clear H'.
 case Z.compare_spec; intros Cmp;
   rewrite ?spec_0, ?spec_1; intros; auto with zarith.
 rewrite Cmp; generalize (Z_div_same [y] (Z.lt_gt _ _ H))
                         (Z_mod_same [y] (Z.lt_gt _ _ H));
  unfold Z.div, Z.modulo; case Z.div_eucl; intros; subst; auto.
 assert (LeLt: 0 <= [x] < [y]) by (generalize (spec_pos x); auto).
 generalize (Zdiv_small _ _ LeLt) (Zmod_small _ _ LeLt);
  unfold Z.div, Z.modulo; case Z.div_eucl; intros; subst; auto.
 generalize (spec_div_gt _ _ (Z.lt_gt _ _ Cmp) H); auto.
 unfold Z.div, Z.modulo; case Z.div_eucl; case div_gt.
 intros a b c d (H1, H2); subst; auto.
 Qed.

 Definition div (x y : t) : t := fst (div_eucl x y).

 Theorem spec_div:
   forall x y, [div x y] = [x] / [y].
 Proof.
 intros x y; unfold div; generalize (spec_div_eucl x y);
   case div_eucl; simpl fst.
 intros xx yy; unfold Z.div; case Z.div_eucl; intros qq rr H;
  injection H; auto.
 Qed.

 (** * Modulo by a smaller number *)

 Definition wn_modn1 n :=
  let op := dom_op n in
  let zd := ZnZ.zdigits op in
  let zero := ZnZ.zero in
  let head0 := ZnZ.head0 in
  let add_mul_div := ZnZ.add_mul_div in
  let div21 := ZnZ.div21 in
  let compare := ZnZ.compare in
  let sub := ZnZ.sub in
  let dmodn1 :=
    DoubleDivn1.double_modn1 zd zero head0 add_mul_div div21 compare sub in
  fun m x y => reduce n (dmodn1 (S m) x y).

 Definition mod_gtnm n m wx wy :=
    let mn := Max.max n m in
    let d := diff n m in
    let op := make_op mn in
    reduce_n mn (ZnZ.modulo_gt
         (castm (diff_r n m) (extend_tr wx (snd d)))
         (castm (diff_l n m) (extend_tr wy (fst d)))).

 Local Notation mod_gt_folded :=
   (iter _
      (fun n => let modulo_gt := ZnZ.modulo_gt in
        fun x y => reduce n (modulo_gt x y))
      (fun n => let modulo_gt := ZnZ.modulo_gt in
        fun m x y =>
          reduce n (modulo_gt x (DoubleBase.get_low (zeron n) (S m) y)))
      wn_modn1
      mod_gtnm).

 Definition mod_gt :=
  Eval lazy beta iota delta [iter dom_op dom_t reduce wn_modn1 zeron] in
  mod_gt_folded.

 Lemma mod_gt_fold : mod_gt = mod_gt_folded.
 Proof.
  lazy beta iota delta [iter dom_op dom_t reduce wn_modn1 zeron].
  reflexivity.
 Qed.

 Definition spec_modn1 n :=
   DoubleDivn1.spec_double_modn1
    (ZnZ.zdigits (dom_op n)) (ZnZ.zero:dom_t n)
    ZnZ.WW ZnZ.head0
    ZnZ.add_mul_div ZnZ.div21
    ZnZ.compare ZnZ.sub ZnZ.to_Z
    ZnZ.spec_to_Z
    ZnZ.spec_zdigits
    ZnZ.spec_0 ZnZ.spec_WW ZnZ.spec_head0
    ZnZ.spec_add_mul_div ZnZ.spec_div21
    ZnZ.spec_compare ZnZ.spec_sub.

 Theorem spec_mod_gt:
   forall x y, [x] > [y] -> 0 < [y] -> [mod_gt x y] = [x] mod [y].
 Proof.
 intros x y. rewrite mod_gt_fold. apply spec_iter; clear x y.
 intros n x y H1 H2. simpl. rewrite spec_reduce.
   exact (ZnZ.spec_modulo_gt x y H1 H2).
 intros n m x y H1 H2. cbv zeta beta. rewrite spec_reduce.
  rewrite <- spec_mk_t in H1.
  rewrite <- (spec_get_endn n (S m) y x); auto with zarith.
  rewrite spec_mk_t.
  apply ZnZ.spec_modulo_gt; auto.
  rewrite <- (spec_get_endn n (S m) y x), !spec_mk_t in H1; auto with zarith.
  rewrite <- (spec_get_endn n (S m) y x), !spec_mk_t in H2; auto with zarith.
 intros n m x y H1 H2. unfold wn_modn1. rewrite spec_reduce.
  unfold eval; rewrite nmake_double.
  apply (spec_modn1 n); auto.
 intros n m x y H1 H2; unfold mod_gtnm.
  repeat rewrite spec_reduce_n.
  rewrite (spec_cast_l n m x), (spec_cast_r n m y).
  unfold to_Z; apply ZnZ.spec_modulo_gt.
  rewrite (spec_cast_l n m x) in H1; auto.
  rewrite (spec_cast_r n m y) in H1; auto.
  rewrite (spec_cast_r n m y) in H2; auto.
 Qed.

 (** * General Modulo *)

 Definition modulo (x y : t) : t :=
  if eqb y zero then zero else
  match compare x y with
  | Eq => zero
  | Lt => x
  | Gt => mod_gt x y
  end.

 Theorem spec_modulo:
   forall x y, [modulo x y] = [x] mod [y].
 Proof.
 intros x y. unfold modulo.
 rewrite spec_eqb, spec_compare, spec_0.
 case Z.eqb_spec.
 intros ->; rewrite spec_0. destruct [x]; auto.
 intro H'.
 assert (H : 0 < [y]) by (generalize (spec_pos y); auto with zarith).
 clear H'.
 case Z.compare_spec;
   rewrite ?spec_0, ?spec_1; intros; try split; auto with zarith.
 rewrite H0; symmetry; apply Z_mod_same; auto with zarith.
 symmetry; apply Zmod_small; auto with zarith.
 generalize (spec_pos x); auto with zarith.
 apply spec_mod_gt; auto with zarith.
 Qed.

 (** * Square *)

 Local Notation squaren := (fun n =>
   let square_c := ZnZ.square_c in
   fun x => reduce (S n) (succ_t _ (square_c x))).

 Definition square : t -> t := Eval red_t in iter_t squaren.

 Lemma square_fold : square = iter_t squaren.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_square: forall x, [square x] = [x] * [x].
 Proof.
  intros x. rewrite square_fold. destr_t x as (n,x).
  rewrite spec_succ_t. exact (ZnZ.spec_square_c x).
 Qed.

 (** * Square Root *)

 Local Notation sqrtn := (fun n =>
   let sqrt := ZnZ.sqrt in
   fun x => reduce n (sqrt x)).

 Definition sqrt : t -> t := Eval red_t in iter_t sqrtn.

 Lemma sqrt_fold : sqrt = iter_t sqrtn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_sqrt_aux: forall x, [sqrt x] ^ 2 <= [x] < ([sqrt x] + 1) ^ 2.
 Proof.
  intros x. rewrite sqrt_fold. destr_t x as (n,x). exact (ZnZ.spec_sqrt x).
 Qed.

 Theorem spec_sqrt: forall x, [sqrt x] = Z.sqrt [x].
 Proof.
  intros x.
  symmetry. apply Z.sqrt_unique.
  rewrite <- ! Z.pow_2_r. apply spec_sqrt_aux.
 Qed.

 (** * Power *)

 Fixpoint pow_pos (x:t)(p:positive) : t :=
  match p with
  | xH => x
  | xO p => square (pow_pos x p)
  | xI p => mul (square (pow_pos x p)) x
  end.

 Theorem spec_pow_pos: forall x n, [pow_pos x n] = [x] ^ Zpos n.
 Proof.
 intros x n; generalize x; elim n; clear n x; simpl pow_pos.
 intros; rewrite spec_mul; rewrite spec_square; rewrite H.
 rewrite Pos2Z.inj_xI; rewrite Zpower_exp; auto with zarith.
 rewrite (Z.mul_comm 2); rewrite Z.pow_mul_r; auto with zarith.
 rewrite Z.pow_2_r; rewrite Z.pow_1_r; auto.
 intros; rewrite spec_square; rewrite H.
 rewrite Pos2Z.inj_xO; auto with zarith.
 rewrite (Z.mul_comm 2); rewrite Z.pow_mul_r; auto with zarith.
 rewrite Z.pow_2_r; auto.
 intros; rewrite Z.pow_1_r; auto.
 Qed.

 Definition pow_N (x:t)(n:N) : t := match n with
  | BinNat.N0 => one
  | BinNat.Npos p => pow_pos x p
 end.

 Theorem spec_pow_N: forall x n, [pow_N x n] = [x] ^ Z.of_N n.
 Proof.
 destruct n; simpl. apply spec_1.
 apply spec_pow_pos.
 Qed.

 Definition pow (x y:t) : t := pow_N x (to_N y).

 Theorem spec_pow : forall x y, [pow x y] = [x] ^ [y].
 Proof.
 intros. unfold pow, to_N.
 now rewrite spec_pow_N, Z2N.id by apply spec_pos.
 Qed.


 (** * digits

     Number of digits in the representation of a numbers
     (including head zero's).
     NB: This function isn't a morphism for setoid [eq].
 *)

 Local Notation digitsn := (fun n =>
   let digits := ZnZ.digits (dom_op n) in
   fun _ => digits).

 Definition digits : t -> positive := Eval red_t in iter_t digitsn.

 Lemma digits_fold : digits = iter_t digitsn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_digits: forall x, 0 <= [x] < 2 ^ Zpos (digits x).
 Proof.
 intros x. rewrite digits_fold. destr_t x as (n,x). exact (ZnZ.spec_to_Z x).
 Qed.

 Lemma digits_level : forall x, digits x = ZnZ.digits (dom_op (level x)).
 Proof.
 intros x. rewrite digits_fold. unfold level. destr_t x as (n,x). reflexivity.
 Qed.

 (** * Gcd *)

 Definition gcd_gt_body a b cont :=
  match compare b zero with
  | Gt =>
    let r := mod_gt a b in
    match compare r zero with
    | Gt => cont r (mod_gt b r)
    | _ => b
    end
  | _ => a
  end.

 Theorem Zspec_gcd_gt_body: forall a b cont p,
    [a] > [b] -> [a] < 2 ^ p ->
      (forall a1 b1, [a1] < 2 ^ (p - 1) -> [a1] > [b1] ->
         Zis_gcd  [a1] [b1] [cont a1 b1]) ->
      Zis_gcd [a] [b] [gcd_gt_body a b cont].
 Proof.
 intros a b cont p H2 H3 H4; unfold gcd_gt_body.
 rewrite ! spec_compare, spec_0. case Z.compare_spec.
  intros ->; apply Zis_gcd_0.
 intros HH; absurd (0 <= [b]); auto with zarith.
 case (spec_digits b); auto with zarith.
 intros H5; case Z.compare_spec.
 intros H6; rewrite <- (Z.mul_1_r [b]).
 rewrite (Z_div_mod_eq [a] [b]); auto with zarith.
 rewrite <- spec_mod_gt; auto with zarith.
 rewrite H6; rewrite Z.add_0_r.
 apply Zis_gcd_mult; apply Zis_gcd_1.
 intros; apply False_ind.
 case (spec_digits (mod_gt a b)); auto with zarith.
 intros H6; apply DoubleDiv.Zis_gcd_mod; auto with zarith.
 apply DoubleDiv.Zis_gcd_mod; auto with zarith.
 rewrite <- spec_mod_gt; auto with zarith.
 assert (F2: [b] > [mod_gt a b]).
   case (Z_mod_lt [a] [b]); auto with zarith.
   repeat rewrite <- spec_mod_gt; auto with zarith.
 assert (F3: [mod_gt a b] > [mod_gt b  (mod_gt a b)]).
   case (Z_mod_lt [b] [mod_gt a b]); auto with zarith.
   rewrite <- spec_mod_gt; auto with zarith.
 repeat rewrite <- spec_mod_gt; auto with zarith.
 apply H4; auto with zarith.
 apply Z.mul_lt_mono_pos_r with 2; auto with zarith.
 apply Z.le_lt_trans with ([b] + [mod_gt a b]); auto with zarith.
 apply Z.le_lt_trans with (([a]/[b]) * [b] + [mod_gt a b]); auto with zarith.
 - apply Z.add_le_mono_r.
   rewrite <- (Z.mul_1_l [b]) at 1.
   apply Z.mul_le_mono_nonneg_r; auto with zarith.
   change 1 with (Z.succ 0). apply Z.le_succ_l.
   apply Z.div_str_pos; auto with zarith.
 - rewrite Z.mul_comm; rewrite spec_mod_gt; auto with zarith.
   rewrite <- Z_div_mod_eq; auto with zarith.
   rewrite Z.mul_comm, <- Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; auto.
   apply Z.le_0_sub. change 1 with (Z.succ 0). apply Z.le_succ_l.
   destruct p; simpl in H3; auto with zarith.
 Qed.

 Fixpoint gcd_gt_aux (p:positive) (cont:t->t->t) (a b:t) : t :=
  gcd_gt_body a b
    (fun a b =>
       match p with
       | xH => cont a b
       | xO p => gcd_gt_aux p (gcd_gt_aux p cont) a b
       | xI p => gcd_gt_aux p (gcd_gt_aux p cont) a b
       end).

 Theorem Zspec_gcd_gt_aux: forall p n a b cont,
    [a] > [b] -> [a] < 2 ^ (Zpos p + n) ->
      (forall a1 b1, [a1] < 2 ^ n -> [a1] > [b1] ->
            Zis_gcd [a1] [b1] [cont a1 b1]) ->
          Zis_gcd [a] [b] [gcd_gt_aux p cont a b].
 intros p; elim p; clear p.
 intros p Hrec n a b cont H2 H3 H4.
   unfold gcd_gt_aux; apply Zspec_gcd_gt_body with (Zpos (xI p) + n); auto.
   intros a1 b1 H6 H7.
     apply Hrec with (Zpos p + n); auto.
       replace (Zpos p + (Zpos p + n)) with
         (Zpos (xI p) + n  - 1); auto.
       rewrite Pos2Z.inj_xI; ring.
   intros a2 b2 H9 H10.
     apply Hrec with n; auto.
 intros p Hrec n a b cont H2 H3 H4.
   unfold gcd_gt_aux; apply Zspec_gcd_gt_body with (Zpos (xO p) + n); auto.
   intros a1 b1 H6 H7.
     apply Hrec with (Zpos p + n - 1); auto.
       replace (Zpos p + (Zpos p + n - 1)) with
         (Zpos (xO p) + n  - 1); auto.
       rewrite Pos2Z.inj_xO; ring.
   intros a2 b2 H9 H10.
     apply Hrec with (n - 1); auto.
       replace (Zpos p + (n - 1)) with
         (Zpos p + n  - 1); auto with zarith.
   intros a3 b3 H12 H13; apply H4; auto with zarith.
    apply Z.lt_le_trans with (1 := H12).
    apply Z.pow_le_mono_r; auto with zarith.
 intros n a b cont H H2 H3.
  simpl gcd_gt_aux.
  apply Zspec_gcd_gt_body with (n + 1); auto with zarith.
  rewrite Z.add_comm; auto.
  intros a1 b1 H5 H6; apply H3; auto.
  replace n with (n + 1 - 1); auto; try ring.
 Qed.

 Definition gcd_cont a b :=
  match compare one b with
  | Eq => one
  | _ => a
  end.

 Definition gcd_gt a b := gcd_gt_aux (digits a) gcd_cont a b.

 Theorem spec_gcd_gt: forall a b,
   [a] > [b] -> [gcd_gt a b] = Z.gcd [a] [b].
 Proof.
 intros a b H2.
 case (spec_digits (gcd_gt a b)); intros H3 H4.
 case (spec_digits a); intros H5 H6.
 symmetry; apply Zis_gcd_gcd; auto with zarith.
 unfold gcd_gt; apply Zspec_gcd_gt_aux with 0; auto with zarith.
 intros a1 a2; rewrite Z.pow_0_r.
 case (spec_digits a2); intros H7 H8;
   intros; apply False_ind; auto with zarith.
 Qed.

 Definition gcd (a b : t) : t :=
  match compare a b with
  | Eq => a
  | Lt => gcd_gt b a
  | Gt => gcd_gt a b
  end.

 Theorem spec_gcd: forall a b, [gcd a b] = Z.gcd [a] [b].
 Proof.
 intros a b.
 case (spec_digits a); intros H1 H2.
 case (spec_digits b); intros H3 H4.
 unfold gcd. rewrite spec_compare. case Z.compare_spec.
 intros HH; rewrite HH; symmetry; apply Zis_gcd_gcd; auto.
   apply Zis_gcd_refl.
 intros; transitivity (Z.gcd [b] [a]).
   apply spec_gcd_gt; auto with zarith.
 apply Zis_gcd_gcd; auto with zarith.
 apply Z.gcd_nonneg.
 apply Zis_gcd_sym; apply Zgcd_is_gcd.
 intros; apply spec_gcd_gt; auto with zarith.
 Qed.

 (** * Parity test *)

 Definition even : t -> bool := Eval red_t in
   iter_t (fun n x => ZnZ.is_even x).

 Definition odd x := negb (even x).

 Lemma even_fold : even = iter_t (fun n x => ZnZ.is_even x).
 Proof. red_t; reflexivity. Qed.

 Theorem spec_even_aux: forall x,
   if even x then [x] mod 2 = 0 else [x] mod 2 = 1.
 Proof.
 intros x. rewrite even_fold. destr_t x as (n,x).
 exact (ZnZ.spec_is_even x).
 Qed.

 Theorem spec_even: forall x, even x = Z.even [x].
 Proof.
 intros x. assert (H := spec_even_aux x). symmetry.
 rewrite (Z.div_mod [x] 2); auto with zarith.
 destruct (even x); rewrite H, ?Z.add_0_r.
 rewrite Zeven_bool_iff. apply Zeven_2p.
 apply not_true_is_false. rewrite Zeven_bool_iff.
 apply Zodd_not_Zeven. apply Zodd_2p_plus_1.
 Qed.

 Theorem spec_odd: forall x, odd x = Z.odd [x].
 Proof.
 intros x. unfold odd.
 assert (H := spec_even_aux x). symmetry.
 rewrite (Z.div_mod [x] 2); auto with zarith.
 destruct (even x); rewrite H, ?Z.add_0_r; simpl negb.
 apply not_true_is_false. rewrite Zodd_bool_iff.
 apply Zeven_not_Zodd. apply Zeven_2p.
 apply Zodd_bool_iff. apply Zodd_2p_plus_1.
 Qed.

 (** * Conversion *)

 Definition pheight p :=
   Peano.pred (Pos.to_nat (get_height (ZnZ.digits (dom_op 0)) (plength p))).

 Theorem pheight_correct: forall p,
    Zpos p < 2 ^ (Zpos (ZnZ.digits (dom_op 0)) * 2 ^ (Z.of_nat (pheight p))).
 Proof.
 intros p; unfold pheight.
 rewrite Nat2Z.inj_pred by apply Pos2Nat.is_pos.
 rewrite positive_nat_Z.
 rewrite <- Z.sub_1_r.
 assert (F2:= (get_height_correct (ZnZ.digits (dom_op 0)) (plength p))).
 apply Z.lt_le_trans with (Zpos (Pos.succ p)).
   rewrite Pos2Z.inj_succ; auto with zarith.
  apply Z.le_trans with (1 := plength_pred_correct (Pos.succ p)).
 rewrite Pos.pred_succ.
 apply Z.pow_le_mono_r; auto with zarith.
 Qed.

 Definition of_pos (x:positive) : t  :=
  let n := pheight x in
  reduce n (snd (ZnZ.of_pos x)).

 Theorem spec_of_pos: forall x,
   [of_pos x] = Zpos x.
 Proof.
 intros x; unfold of_pos.
 rewrite spec_reduce.
 simpl.
 apply ZnZ.of_pos_correct.
 unfold base.
 apply Z.lt_le_trans with (1 := pheight_correct x).
 apply Z.pow_le_mono_r; auto with zarith.
 rewrite (digits_dom_op (_ _)), Pshiftl_nat_Zpower. auto with zarith.
 Qed.

 Definition of_N (x:N) : t :=
  match x with
  | BinNat.N0 => zero
  | Npos p => of_pos p
  end.

 Theorem spec_of_N: forall x,
   [of_N x] = Z.of_N x.
 Proof.
 intros x; case x.
  simpl of_N. exact spec_0.
 intros p; exact (spec_of_pos p).
 Qed.

 (** * [head0] and [tail0]

     Number of zero at the beginning and at the end of
     the representation of the number.
     NB: these functions are not morphism for setoid [eq].
 *)

 Local Notation head0n := (fun n =>
   let head0 := ZnZ.head0 in
   fun x => reduce n (head0 x)).

 Definition head0 : t -> t := Eval red_t in iter_t head0n.

 Lemma head0_fold : head0 = iter_t head0n.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_head00: forall x, [x] = 0 -> [head0 x] = Zpos (digits x).
 Proof.
 intros x. rewrite head0_fold, digits_fold. destr_t x as (n,x).
 exact (ZnZ.spec_head00 x).
 Qed.

 Lemma pow2_pos_minus_1 : forall z, 0<z -> 2^(z-1) = 2^z / 2.
 Proof.
  intros. apply Zdiv_unique with 0; auto with zarith.
  change 2 with (2^1) at 2.
  rewrite <- Zpower_exp; auto with zarith.
  rewrite Z.add_0_r. f_equal. auto with zarith.
 Qed.

 Theorem spec_head0: forall x, 0 < [x] ->
   2 ^ (Zpos (digits x) - 1) <= 2 ^ [head0 x] * [x] < 2 ^ Zpos (digits x).
 Proof.
 intros x. rewrite pow2_pos_minus_1 by (red; auto).
 rewrite head0_fold, digits_fold. destr_t x as (n,x). exact (ZnZ.spec_head0 x).
 Qed.

 Local Notation tail0n := (fun n =>
  let tail0 := ZnZ.tail0 in
  fun x => reduce n (tail0 x)).

 Definition tail0 : t -> t := Eval red_t in iter_t tail0n.

 Lemma tail0_fold : tail0 = iter_t tail0n.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_tail00: forall x, [x] = 0 -> [tail0 x] = Zpos (digits x).
 Proof.
 intros x. rewrite tail0_fold, digits_fold. destr_t x as (n,x).
 exact (ZnZ.spec_tail00 x).
 Qed.

 Theorem spec_tail0: forall x,
   0 < [x] -> exists y, 0 <= y /\ [x] = (2 * y + 1) * 2 ^ [tail0 x].
 Proof.
 intros x. rewrite tail0_fold. destr_t x as (n,x). exact (ZnZ.spec_tail0 x).
 Qed.

 (** * [Ndigits]

     Same as [digits] but encoded using large integers
     NB: this function is not a morphism for setoid [eq].
 *)

 Local Notation Ndigitsn := (fun n =>
  let d := reduce n (ZnZ.zdigits (dom_op n)) in
  fun _ => d).

 Definition Ndigits : t -> t := Eval red_t in iter_t Ndigitsn.

 Lemma Ndigits_fold : Ndigits = iter_t Ndigitsn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_Ndigits: forall x, [Ndigits x] = Zpos (digits x).
 Proof.
 intros x. rewrite Ndigits_fold, digits_fold. destr_t x as (n,x).
 apply ZnZ.spec_zdigits.
 Qed.

 (** * Binary logarithm *)

 Local Notation log2n := (fun n =>
  let op := dom_op n in
  let zdigits := ZnZ.zdigits op in
  let head0 := ZnZ.head0 in
  let sub_carry := ZnZ.sub_carry in
  fun x => reduce n (sub_carry zdigits (head0 x))).

 Definition log2 : t -> t := Eval red_t in
   let log2 := iter_t log2n in
   fun x => if eqb x zero then zero else log2 x.

 Lemma log2_fold :
   log2 = fun x => if eqb x zero then zero else iter_t log2n x.
 Proof. red_t; reflexivity. Qed.

 Lemma spec_log2_0 : forall x, [x] = 0 -> [log2 x] = 0.
 Proof.
 intros x H. rewrite log2_fold.
 rewrite spec_eqb, H. rewrite spec_0. simpl. exact spec_0.
 Qed.

 Lemma head0_zdigits : forall n (x : dom_t n),
  0 < ZnZ.to_Z x ->
  ZnZ.to_Z (ZnZ.head0 x) < ZnZ.to_Z (ZnZ.zdigits (dom_op n)).
 Proof.
 intros n x H.
 destruct (ZnZ.spec_head0 x H) as (_,H0).
 intros.
 assert (H1 := ZnZ.spec_to_Z (ZnZ.head0 x)).
 assert (H2 := ZnZ.spec_to_Z (ZnZ.zdigits (dom_op n))).
 unfold base in *.
 rewrite ZnZ.spec_zdigits in H2 |- *.
 set (h := ZnZ.to_Z (ZnZ.head0 x)) in *; clearbody h.
 set (d := ZnZ.digits (dom_op n)) in *; clearbody d.
 destruct (Z_lt_le_dec h (Zpos d)); auto. exfalso.
 assert (1 * 2^Zpos d <= ZnZ.to_Z x * 2^h).
  apply Z.mul_le_mono_nonneg; auto with zarith.
  apply Z.pow_le_mono_r; auto with zarith.
 rewrite Z.mul_comm in H0. auto with zarith.
 Qed.

 Lemma spec_log2_pos : forall x, [x]<>0 ->
   2^[log2 x] <= [x] < 2^([log2 x]+1).
 Proof.
 intros x H. rewrite log2_fold.
 rewrite spec_eqb. rewrite spec_0.
 case Z.eqb_spec.
 auto with zarith.
 clear H.
 destr_t x as (n,x). intros H.
 rewrite ZnZ.spec_sub_carry.
 assert (H0 := ZnZ.spec_to_Z x).
 assert (H1 := ZnZ.spec_to_Z (ZnZ.head0 x)).
 assert (H2 := ZnZ.spec_to_Z (ZnZ.zdigits (dom_op n))).
 assert (H3 := head0_zdigits n x).
 rewrite Zmod_small by auto with zarith.
 rewrite Z.sub_simpl_r.
 rewrite (Z.mul_lt_mono_pos_l (2^(ZnZ.to_Z (ZnZ.head0 x))));
  auto with zarith.
 rewrite (Z.mul_le_mono_pos_l _ _ (2^(ZnZ.to_Z (ZnZ.head0 x))));
  auto with zarith.
 rewrite <- 2 Zpower_exp; auto with zarith.
 rewrite !Z.add_sub_assoc, !Z.add_simpl_l.
 rewrite ZnZ.spec_zdigits.
 rewrite pow2_pos_minus_1 by (red; auto).
 apply ZnZ.spec_head0; auto with zarith.
 Qed.

 Lemma spec_log2 : forall x, [log2 x] = Z.log2 [x].
 Proof.
  intros. destruct (Z_lt_ge_dec 0 [x]).
  symmetry. apply Z.log2_unique. apply spec_pos.
  apply spec_log2_pos. intro EQ; rewrite EQ in *; auto with zarith.
  rewrite spec_log2_0. rewrite Z.log2_nonpos; auto with zarith.
  generalize (spec_pos x); auto with zarith.
 Qed.

 Lemma log2_digits_head0 : forall x, 0 < [x] ->
   [log2 x] = Zpos (digits x) - [head0 x] - 1.
 Proof.
 intros. rewrite log2_fold.
 rewrite spec_eqb. rewrite spec_0.
 case Z.eqb_spec.
 auto with zarith.
 intros _. revert H. rewrite digits_fold, head0_fold. destr_t x as (n,x).
 rewrite ZnZ.spec_sub_carry.
 intros.
 generalize (head0_zdigits n x H).
 generalize (ZnZ.spec_to_Z (ZnZ.head0 x)).
 generalize (ZnZ.spec_to_Z (ZnZ.zdigits (dom_op n))).
 rewrite ZnZ.spec_zdigits. intros. apply Zmod_small.
 auto with zarith.
 Qed.

 (** * Right shift *)

 Local Notation shiftrn := (fun n =>
   let op := dom_op n in
   let zdigits := ZnZ.zdigits op in
   let sub_c := ZnZ.sub_c in
   let add_mul_div := ZnZ.add_mul_div in
   let zzero := ZnZ.zero in
   fun x p => match sub_c zdigits p with
   | C0 d => reduce n (add_mul_div d zzero x)
   | C1 _ => zero
   end).

 Definition shiftr : t -> t -> t := Eval red_t in
   same_level shiftrn.

 Lemma shiftr_fold : shiftr = same_level shiftrn.
 Proof. red_t; reflexivity. Qed.

 Lemma div_pow2_bound :forall x y z,
   0 <= x -> 0 <= y -> x < z -> 0 <= x / 2 ^ y < z.
 Proof.
   intros x y z HH HH1 HH2.
   split; auto with zarith.
   apply Z.le_lt_trans with (2 := HH2); auto with zarith.
   apply Zdiv_le_upper_bound; auto with zarith.
   pattern x at 1; replace x with (x * 2 ^ 0); auto with zarith.
   apply Z.mul_le_mono_nonneg_l; auto.
   apply Z.pow_le_mono_r; auto with zarith.
   rewrite Z.pow_0_r; ring.
 Qed.

 Theorem spec_shiftr_pow2 : forall x n,
  [shiftr x n] = [x] / 2 ^ [n].
 Proof.
  intros x y. rewrite shiftr_fold. apply spec_same_level. clear x y.
  intros n x p. simpl.
  assert (Hx := ZnZ.spec_to_Z x).
  assert (Hy := ZnZ.spec_to_Z p).
  generalize (ZnZ.spec_sub_c (ZnZ.zdigits (dom_op n)) p).
  case ZnZ.sub_c; intros d H; unfold interp_carry in *; simpl.
  (** Subtraction without underflow : [ p <= digits ] *)
  rewrite spec_reduce.
  rewrite ZnZ.spec_zdigits in H.
  rewrite ZnZ.spec_add_mul_div by auto with zarith.
  rewrite ZnZ.spec_0, Z.mul_0_l, Z.add_0_l.
  rewrite Zmod_small.
  f_equal. f_equal. auto with zarith.
  split. auto with zarith.
  apply div_pow2_bound; auto with zarith.
  (** Subtraction with underflow : [ digits < p ] *)
  rewrite ZnZ.spec_0. symmetry.
  apply Zdiv_small.
  split; auto with zarith.
  apply Z.lt_le_trans with (base (ZnZ.digits (dom_op n))); auto with zarith.
  unfold base. apply Z.pow_le_mono_r; auto with zarith.
  rewrite ZnZ.spec_zdigits in H.
  generalize (ZnZ.spec_to_Z d); auto with zarith.
 Qed.

 Lemma spec_shiftr: forall x p, [shiftr x p] = Z.shiftr [x] [p].
 Proof.
  intros.
  now rewrite spec_shiftr_pow2, Z.shiftr_div_pow2 by apply spec_pos.
 Qed.

 (** * Left shift *)

 (** First an unsafe version, working correctly only if
     the representation is large enough *)

 Local Notation unsafe_shiftln := (fun n =>
   let op := dom_op n in
   let add_mul_div := ZnZ.add_mul_div in
   let zero := ZnZ.zero in
   fun x p => reduce n (add_mul_div p x zero)).

 Definition unsafe_shiftl : t -> t -> t := Eval red_t in
   same_level unsafe_shiftln.

 Lemma unsafe_shiftl_fold : unsafe_shiftl = same_level unsafe_shiftln.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_unsafe_shiftl_aux : forall x p K,
  0 <= K ->
  [x] < 2^K ->
  [p] + K <= Zpos (digits x) ->
  [unsafe_shiftl x p] = [x] * 2 ^ [p].
 Proof.
 intros x p.
 rewrite unsafe_shiftl_fold. rewrite digits_level.
 apply spec_same_level_dep.
 intros n m z z' r LE H K HK H1 H2. apply (H K); auto.
  transitivity (Zpos (ZnZ.digits (dom_op n))); auto.
  apply digits_dom_op_incr; auto.
 clear x p.
 intros n x p K HK Hx Hp. simpl. rewrite spec_reduce.
 destruct (ZnZ.spec_to_Z x).
 destruct (ZnZ.spec_to_Z p).
 rewrite ZnZ.spec_add_mul_div by (omega with *).
 rewrite ZnZ.spec_0, Zdiv_0_l, Z.add_0_r.
 apply Zmod_small. unfold base.
 split; auto with zarith.
 rewrite Z.mul_comm.
 apply Z.lt_le_trans with (2^(ZnZ.to_Z p + K)).
 rewrite Zpower_exp; auto with zarith.
 apply Z.mul_lt_mono_pos_l; auto with zarith.
 apply Z.pow_le_mono_r; auto with zarith.
 Qed.

 Theorem spec_unsafe_shiftl: forall x p,
  [p] <= [head0 x] -> [unsafe_shiftl x p] = [x] * 2 ^ [p].
 Proof.
 intros.
 destruct (Z.eq_dec [x] 0) as [EQ|NEQ].
 (* [x] = 0 *)
 apply spec_unsafe_shiftl_aux with 0; auto with zarith.
 now rewrite EQ.
 rewrite spec_head00 in *; auto with zarith.
 (* [x] <> 0 *)
 apply spec_unsafe_shiftl_aux with ([log2 x] + 1); auto with zarith.
 generalize (spec_pos (log2 x)); auto with zarith.
 destruct (spec_log2_pos x); auto with zarith.
 rewrite log2_digits_head0; auto with zarith.
 generalize (spec_pos x); auto with zarith.
 Qed.

 (** Then we define a function doubling the size of the representation
     but without changing the value of the number. *)

 Local Notation double_size_n := (fun n =>
  let zero := ZnZ.zero in
  fun x => mk_t_S n (WW zero x)).

 Definition double_size : t -> t := Eval red_t in
   iter_t double_size_n.

 Lemma double_size_fold : double_size = iter_t double_size_n.
 Proof. red_t; reflexivity. Qed.

 Lemma double_size_level : forall x, level (double_size x) = S (level x).
 Proof.
 intros x. rewrite double_size_fold; unfold level at 2. destr_t x as (n,x).
 apply mk_t_S_level.
 Qed.

 Theorem spec_double_size_digits:
   forall x, Zpos (digits (double_size x)) = 2 * (Zpos (digits x)).
 Proof.
 intros x. rewrite ! digits_level, double_size_level.
 rewrite 2 digits_dom_op, 2 Pshiftl_nat_Zpower,
         Nat2Z.inj_succ, Z.pow_succ_r; auto with zarith.
 ring.
 Qed.

 Theorem spec_double_size: forall x, [double_size x] = [x].
 Proof.
 intros x. rewrite double_size_fold. destr_t x as (n,x).
 rewrite spec_mk_t_S. simpl. rewrite ZnZ.spec_0. auto with zarith.
 Qed.

 Theorem spec_double_size_head0:
   forall x, 2 * [head0 x] <= [head0 (double_size x)].
 Proof.
 intros x.
 assert (F1:= spec_pos (head0 x)).
 assert (F2: 0 < Zpos (digits x)).
   red; auto.
 assert (HH := spec_pos x). Z.le_elim HH.
 generalize HH; rewrite <- (spec_double_size x); intros HH1.
 case (spec_head0 x HH); intros _ HH2.
 case (spec_head0 _ HH1).
 rewrite (spec_double_size x); rewrite (spec_double_size_digits x).
 intros HH3 _.
 case (Z.le_gt_cases ([head0 (double_size x)]) (2 * [head0 x])); auto; intros HH4.
 absurd (2 ^ (2 * [head0 x] )* [x] < 2 ^ [head0 (double_size x)] * [x]); auto.
 apply Z.le_ngt.
 apply Z.mul_le_mono_nonneg_r; auto with zarith.
 apply Z.pow_le_mono_r; auto; auto with zarith.
 assert (HH5: 2 ^[head0 x] <= 2 ^(Zpos (digits x) - 1)).
 { apply Z.le_succ_l in HH. change (1 <= [x]) in HH.
   Z.le_elim HH.
   - apply Z.mul_le_mono_pos_r with (2 ^ 1); auto with zarith.
     rewrite <- (fun x y z => Z.pow_add_r x (y - z)); auto with zarith.
     rewrite Z.sub_add.
     apply Z.le_trans with (2 := Z.lt_le_incl _ _ HH2).
     apply Z.mul_le_mono_nonneg_l; auto with zarith.
     rewrite Z.pow_1_r; auto with zarith.
   - apply Z.pow_le_mono_r; auto with zarith.
     case (Z.le_gt_cases (Zpos (digits x)) [head0 x]); auto with zarith; intros HH6.
     absurd (2 ^ Zpos (digits x) <= 2 ^ [head0 x] * [x]); auto with zarith.
     rewrite <- HH; rewrite Z.mul_1_r.
     apply Z.pow_le_mono_r; auto with zarith. }
 rewrite (Z.mul_comm 2).
 rewrite Z.pow_mul_r; auto with zarith.
 rewrite Z.pow_2_r.
 apply Z.lt_le_trans with (2 := HH3).
 rewrite <- Z.mul_assoc.
 replace (2 * Zpos (digits x) - 1) with
   ((Zpos (digits x) - 1) + (Zpos (digits x))).
 rewrite Zpower_exp; auto with zarith.
 apply Zmult_lt_compat2; auto with zarith.
 split; auto with zarith.
 apply Z.mul_pos_pos; auto with zarith.
 rewrite Pos2Z.inj_xO; ring.
 apply Z.lt_le_incl; auto.
 repeat rewrite spec_head00; auto.
 rewrite spec_double_size_digits.
 rewrite Pos2Z.inj_xO; auto with zarith.
 rewrite spec_double_size; auto.
 Qed.

 Theorem spec_double_size_head0_pos:
   forall x, 0 < [head0 (double_size x)].
 Proof.
 intros x.
 assert (F := Pos2Z.is_pos (digits x)).
 assert (F0 := spec_pos (head0 (double_size x))).
 Z.le_elim F0; auto.
 assert (F1 := spec_pos (head0 x)).
 Z.le_elim F1.
  apply Z.lt_le_trans with (2 := (spec_double_size_head0 x)); auto with zarith.
 assert (F3 := spec_pos x).
 Z.le_elim F3.
 generalize F3; rewrite <- (spec_double_size x); intros F4.
 absurd (2 ^ (Zpos (xO (digits x)) - 1) < 2 ^ (Zpos (digits x))).
 { apply Z.le_ngt.
   apply Z.pow_le_mono_r; auto with zarith.
   rewrite Pos2Z.inj_xO; auto with zarith. }
 case (spec_head0 x F3).
 rewrite <- F1; rewrite Z.pow_0_r; rewrite Z.mul_1_l; intros _ HH.
 apply Z.le_lt_trans with (2 := HH).
 case (spec_head0 _ F4).
 rewrite (spec_double_size x); rewrite (spec_double_size_digits x).
 rewrite <- F0; rewrite Z.pow_0_r; rewrite Z.mul_1_l; auto.
 generalize F1; rewrite (spec_head00 _ (eq_sym F3)); auto with zarith.
 Qed.

 (** Finally we iterate [double_size] enough before [unsafe_shiftl]
     in order to get a fully correct [shiftl]. *)

 Definition shiftl_aux_body cont x n :=
   match compare n (head0 x) with
      Gt => cont (double_size x) n
   |  _ => unsafe_shiftl x n
   end.

 Theorem spec_shiftl_aux_body: forall n x p cont,
       2^ Zpos p  <=  [head0 x]  ->
      (forall x, 2 ^ (Zpos p + 1) <= [head0 x]->
         [cont x n] = [x] * 2 ^ [n]) ->
      [shiftl_aux_body cont x n] = [x] * 2 ^ [n].
 Proof.
 intros n x p cont H1 H2; unfold shiftl_aux_body.
 rewrite spec_compare; case Z.compare_spec; intros H.
  apply spec_unsafe_shiftl; auto with zarith.
  apply spec_unsafe_shiftl; auto with zarith.
 rewrite H2.
 rewrite spec_double_size; auto.
 rewrite Z.add_comm; rewrite Zpower_exp; auto with zarith.
 apply Z.le_trans with (2 := spec_double_size_head0 x).
 rewrite Z.pow_1_r; apply Z.mul_le_mono_nonneg_l; auto with zarith.
 Qed.

 Fixpoint shiftl_aux p cont x n :=
   shiftl_aux_body
       (fun x n => match p with
        | xH => cont x n
        | xO p => shiftl_aux p (shiftl_aux p cont) x n
        | xI p => shiftl_aux p (shiftl_aux p cont) x n
        end) x n.

 Theorem spec_shiftl_aux: forall p q x n cont,
    2 ^ (Zpos q) <= [head0 x] ->
      (forall x, 2 ^ (Zpos p + Zpos q) <= [head0 x] ->
         [cont x n] = [x] * 2 ^ [n]) ->
      [shiftl_aux p cont x n] = [x] * 2 ^ [n].
 Proof.
 intros p; elim p; unfold shiftl_aux; fold shiftl_aux; clear p.
 intros p Hrec q x n cont H1 H2.
 apply spec_shiftl_aux_body with (q); auto.
 intros x1 H3; apply Hrec with (q + 1)%positive; auto.
 intros x2 H4; apply Hrec with (p + q + 1)%positive; auto.
 rewrite <- Pos.add_assoc.
 rewrite Pos2Z.inj_add; auto.
 intros x3 H5; apply H2.
 rewrite Pos2Z.inj_xI.
 replace (2 * Zpos p + 1 + Zpos q) with (Zpos p + Zpos (p + q + 1));
   auto.
 rewrite !Pos2Z.inj_add; ring.
 intros p Hrec q n x cont H1 H2.
 apply spec_shiftl_aux_body with (q); auto.
 intros x1 H3; apply Hrec with (q); auto.
 apply Z.le_trans with (2 := H3); auto with zarith.
 apply Z.pow_le_mono_r; auto with zarith.
 intros x2 H4; apply Hrec with (p + q)%positive; auto.
 intros x3 H5; apply H2.
 rewrite (Pos2Z.inj_xO p).
 replace (2 * Zpos p + Zpos q) with (Zpos p + Zpos (p + q));
   auto.
 rewrite Pos2Z.inj_add; ring.
 intros q n x cont H1 H2.
 apply spec_shiftl_aux_body with (q); auto.
 rewrite Z.add_comm; auto.
 Qed.

 Definition shiftl x n :=
  shiftl_aux_body
   (shiftl_aux_body
    (shiftl_aux (digits n) unsafe_shiftl)) x n.

 Theorem spec_shiftl_pow2 : forall x n,
   [shiftl x n] = [x] * 2 ^ [n].
 Proof.
 intros x n; unfold shiftl, shiftl_aux_body.
 rewrite spec_compare; case Z.compare_spec; intros H.
  apply spec_unsafe_shiftl; auto with zarith.
  apply spec_unsafe_shiftl; auto with zarith.
 rewrite <- (spec_double_size x).
 rewrite spec_compare; case Z.compare_spec; intros H1.
  apply spec_unsafe_shiftl; auto with zarith.
  apply spec_unsafe_shiftl; auto with zarith.
 rewrite <- (spec_double_size (double_size x)).
 apply spec_shiftl_aux with 1%positive.
 apply Z.le_trans with (2 := spec_double_size_head0 (double_size x)).
 replace (2 ^ 1) with (2 * 1).
 apply Z.mul_le_mono_nonneg_l; auto with zarith.
 generalize (spec_double_size_head0_pos x); auto with zarith.
 rewrite Z.pow_1_r; ring.
 intros x1 H2; apply spec_unsafe_shiftl.
 apply Z.le_trans with (2 := H2).
 apply Z.le_trans with (2 ^ Zpos (digits n)); auto with zarith.
 case (spec_digits n); auto with zarith.
 apply Z.pow_le_mono_r; auto with zarith.
 Qed.

 Lemma spec_shiftl: forall x p, [shiftl x p] = Z.shiftl [x] [p].
 Proof.
  intros.
  now rewrite spec_shiftl_pow2, Z.shiftl_mul_pow2 by apply spec_pos.
 Qed.

 (** Other bitwise operations *)

 Definition testbit x n := odd (shiftr x n).

 Lemma spec_testbit: forall x p, testbit x p = Z.testbit [x] [p].
 Proof.
  intros. unfold testbit. symmetry.
  rewrite spec_odd, spec_shiftr. apply Z.testbit_odd.
 Qed.

 Definition div2 x := shiftr x one.

 Lemma spec_div2: forall x, [div2 x] = Z.div2 [x].
 Proof.
  intros. unfold div2. symmetry.
  rewrite spec_shiftr, spec_1. apply Z.div2_spec.
 Qed.

 Local Notation lorn := (fun n =>
  let op := dom_op n in
  let lor := ZnZ.lor in
  fun x y => reduce n (lor x y)).

 Definition lor : t -> t -> t := Eval red_t in same_level lorn.

 Lemma lor_fold : lor = same_level lorn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_lor x y : [lor x y] = Z.lor [x] [y].
 Proof.
  rewrite lor_fold. apply spec_same_level; clear x y.
  intros n x y. simpl. rewrite spec_reduce. apply ZnZ.spec_lor.
 Qed.

 Local Notation landn := (fun n =>
  let op := dom_op n in
  let land := ZnZ.land in
  fun x y => reduce n (land x y)).

 Definition land : t -> t -> t := Eval red_t in same_level landn.

 Lemma land_fold : land = same_level landn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_land x y : [land x y] = Z.land [x] [y].
 Proof.
  rewrite land_fold. apply spec_same_level; clear x y.
  intros n x y. simpl. rewrite spec_reduce. apply ZnZ.spec_land.
 Qed.

 Local Notation lxorn := (fun n =>
  let op := dom_op n in
  let lxor := ZnZ.lxor in
  fun x y => reduce n (lxor x y)).

 Definition lxor : t -> t -> t := Eval red_t in same_level lxorn.

 Lemma lxor_fold : lxor = same_level lxorn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_lxor x y : [lxor x y] = Z.lxor [x] [y].
 Proof.
  rewrite lxor_fold. apply spec_same_level; clear x y.
  intros n x y. simpl. rewrite spec_reduce. apply ZnZ.spec_lxor.
 Qed.

 Local Notation ldiffn := (fun n =>
  let op := dom_op n in
  let lxor := ZnZ.lxor in
  let land := ZnZ.land in
  let m1 := ZnZ.minus_one in
  fun x y => reduce n (land x (lxor y m1))).

 Definition ldiff : t -> t -> t := Eval red_t in same_level ldiffn.

 Lemma ldiff_fold : ldiff = same_level ldiffn.
 Proof. red_t; reflexivity. Qed.

 Lemma ldiff_alt x y p :
  0 <= x < 2^p -> 0 <= y < 2^p ->
  Z.ldiff x y = Z.land x (Z.lxor y (2^p - 1)).
 Proof.
  intros (Hx,Hx') (Hy,Hy').
  destruct p as [|p|p].
  - simpl in *; replace x with 0; replace y with 0; auto with zarith.
  - rewrite <- Z.shiftl_1_l. change (_ - 1) with (Z.ones (Z.pos p)).
    rewrite <- Z.ldiff_ones_l_low; trivial.
    rewrite !Z.ldiff_land, Z.land_assoc. f_equal.
    rewrite Z.land_ones; try easy.
    symmetry. apply Z.mod_small; now split.
    Z.le_elim Hy.
    + now apply Z.log2_lt_pow2.
    + now subst.
  - simpl in *; omega.
 Qed.

 Theorem spec_ldiff x y : [ldiff x y] = Z.ldiff [x] [y].
 Proof.
  rewrite ldiff_fold. apply spec_same_level; clear x y.
  intros n x y. simpl. rewrite spec_reduce.
  rewrite ZnZ.spec_land, ZnZ.spec_lxor, ZnZ.spec_m1.
  symmetry. apply ldiff_alt; apply ZnZ.spec_to_Z.
 Qed.

End Make.
