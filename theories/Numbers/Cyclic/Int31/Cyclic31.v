(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** * Int31 numbers defines indeed a cyclic structure : Z/(2^31)Z *)

(**
Author: Arnaud Spiwack (+ Pierre Letouzey)
*)

Require Import List.
Require Import Min.
Require Export Int31.
Require Import Znumtheory.
Require Import Zgcd_alt.
Require Import Zpow_facts.
Require Import BigNumPrelude.
Require Import CyclicAxioms.
Require Import ROmega.

Local Open Scope nat_scope.
Local Open Scope int31_scope.

Section Basics.

 (** * Basic results about [iszero], [shiftl], [shiftr] *)

 Lemma iszero_eq0 : forall x, iszero x = true -> x=0.
 Proof.
 destruct x; simpl; intros.
 repeat
   match goal with H:(if ?d then _ else _) = true |- _ =>
     destruct d; try discriminate
   end.
 reflexivity.
 Qed.

 Lemma iszero_not_eq0 : forall x, iszero x = false -> x<>0.
 Proof.
 intros x H Eq; rewrite Eq in H; simpl in *; discriminate.
 Qed.

 Lemma sneakl_shiftr : forall x,
  x = sneakl (firstr x) (shiftr x).
 Proof.
 destruct x; simpl; auto.
 Qed.

 Lemma sneakr_shiftl : forall x,
  x = sneakr (firstl x) (shiftl x).
 Proof.
 destruct x; simpl; auto.
 Qed.

 Lemma twice_zero : forall x,
  twice x = 0 <-> twice_plus_one x = 1.
 Proof.
 destruct x; simpl in *; split;
 intro H; injection H; intros; subst; auto.
 Qed.

 Lemma twice_or_twice_plus_one : forall x,
  x = twice (shiftr x) \/ x = twice_plus_one (shiftr x).
 Proof.
 intros; case_eq (firstr x); intros.
 destruct x; simpl in *; rewrite H; auto.
 destruct x; simpl in *; rewrite H; auto.
 Qed.



 (** * Iterated shift to the right *)

 Definition nshiftr n x := iter_nat n _ shiftr x.

 Lemma nshiftr_S :
  forall n x, nshiftr (S n) x = shiftr (nshiftr n x).
 Proof.
 reflexivity.
 Qed.

 Lemma nshiftr_S_tail :
  forall n x, nshiftr (S n) x = nshiftr n (shiftr x).
 Proof.
 induction n; simpl; auto.
 intros; rewrite nshiftr_S, IHn, nshiftr_S; auto.
 Qed.

 Lemma nshiftr_n_0 : forall n, nshiftr n 0 = 0.
 Proof.
 induction n; simpl; auto.
 rewrite nshiftr_S, IHn; auto.
 Qed.

 Lemma nshiftr_size : forall x, nshiftr size x = 0.
 Proof.
 destruct x; simpl; auto.
 Qed.

 Lemma nshiftr_above_size : forall k x, size<=k ->
  nshiftr k x = 0.
 Proof.
 intros.
 replace k with ((k-size)+size)%nat by omega.
 induction (k-size)%nat; auto.
  rewrite nshiftr_size; auto.
  simpl; rewrite nshiftr_S, IHn; auto.
 Qed.

 (** * Iterated shift to the left *)

 Definition nshiftl n x := iter_nat n _ shiftl x.

 Lemma nshiftl_S :
  forall n x, nshiftl (S n) x = shiftl (nshiftl n x).
 Proof.
 reflexivity.
 Qed.

 Lemma nshiftl_S_tail :
  forall n x, nshiftl (S n) x = nshiftl n (shiftl x).
 Proof.
 induction n; simpl; auto.
 intros; rewrite nshiftl_S, IHn, nshiftl_S; auto.
 Qed.

 Lemma nshiftl_n_0 : forall n, nshiftl n 0 = 0.
 Proof.
 induction n; simpl; auto.
 rewrite nshiftl_S, IHn; auto.
 Qed.

 Lemma nshiftl_size : forall x, nshiftl size x = 0.
 Proof.
 destruct x; simpl; auto.
 Qed.

 Lemma nshiftl_above_size : forall k x, size<=k ->
  nshiftl k x = 0.
 Proof.
 intros.
 replace k with ((k-size)+size)%nat by omega.
 induction (k-size)%nat; auto.
  rewrite nshiftl_size; auto.
  simpl; rewrite nshiftl_S, IHn; auto.
 Qed.

 Lemma firstr_firstl :
  forall x, firstr x = firstl (nshiftl (pred size) x).
 Proof.
 destruct x; simpl; auto.
 Qed.

 Lemma firstl_firstr :
  forall x, firstl x = firstr (nshiftr (pred size) x).
 Proof.
 destruct x; simpl; auto.
 Qed.

 (** More advanced results about [nshiftr] *)

 Lemma nshiftr_predsize_0_firstl : forall x,
  nshiftr (pred size) x = 0 -> firstl x = D0.
 Proof.
 destruct x; compute; intros H; injection H; intros; subst; auto.
 Qed.

 Lemma nshiftr_0_propagates : forall n p x, n <= p ->
  nshiftr n x = 0 -> nshiftr p x = 0.
 Proof.
 intros.
 replace p with ((p-n)+n)%nat by omega.
 induction (p-n)%nat.
 simpl; auto.
 simpl; rewrite nshiftr_S; rewrite IHn0; auto.
 Qed.

 Lemma nshiftr_0_firstl : forall n x, n < size ->
  nshiftr n x = 0 -> firstl x = D0.
 Proof.
 intros.
 apply nshiftr_predsize_0_firstl.
 apply nshiftr_0_propagates with n; auto; omega.
 Qed.

 (** * Some induction principles over [int31] *)

 (** Not used for the moment. Are they really useful ? *)

 Lemma int31_ind_sneakl : forall P : int31->Prop,
  P 0 ->
  (forall x d, P x -> P (sneakl d x)) ->
  forall x, P x.
 Proof.
 intros.
 assert (forall n, n<=size -> P (nshiftr (size - n) x)).
 induction n; intros.
 rewrite nshiftr_size; auto.
 rewrite sneakl_shiftr.
 apply H0.
 change (P (nshiftr (S (size - S n)) x)).
 replace (S (size - S n))%nat with (size - n)%nat by omega.
 apply IHn; omega.
 change x with (nshiftr (size-size) x); auto.
 Qed.

 Lemma int31_ind_twice : forall P : int31->Prop,
  P 0 ->
  (forall x, P x -> P (twice x)) ->
  (forall x, P x -> P (twice_plus_one x)) ->
  forall x, P x.
 Proof.
 induction x using int31_ind_sneakl; auto.
 destruct d; auto.
 Qed.


 (** * Some generic results about [recr] *)

 Section Recr.

 (** [recr] satisfies the fixpoint equation used for its definition. *)

 Variable (A:Type)(case0:A)(caserec:digits->int31->A->A).

 Lemma recr_aux_eqn : forall n x, iszero x = false ->
   recr_aux (S n) A case0 caserec x =
   caserec (firstr x) (shiftr x) (recr_aux n A case0 caserec (shiftr x)).
 Proof.
 intros; simpl; rewrite H; auto.
 Qed.

 Lemma recr_aux_converges :
  forall n p x, n <= size -> n <= p ->
  recr_aux n A case0 caserec (nshiftr (size - n) x) =
  recr_aux p A case0 caserec (nshiftr (size - n) x).
 Proof.
 induction n.
 simpl; intros.
 rewrite nshiftr_size; destruct p; simpl; auto.
 intros.
 destruct p.
 inversion H0.
 unfold recr_aux; fold recr_aux.
 destruct (iszero (nshiftr (size - S n) x)); auto.
 f_equal.
 change (shiftr (nshiftr (size - S n) x)) with (nshiftr (S (size - S n)) x).
 replace (S (size - S n))%nat with (size - n)%nat by omega.
 apply IHn; auto with arith.
 Qed.

 Lemma recr_eqn : forall x, iszero x = false ->
  recr A case0 caserec x =
  caserec (firstr x) (shiftr x) (recr A case0 caserec (shiftr x)).
 Proof.
 intros.
 unfold recr.
 change x with (nshiftr (size - size) x).
 rewrite (recr_aux_converges size (S size)); auto with arith.
 rewrite recr_aux_eqn; auto.
 Qed.

 (** [recr] is usually equivalent to a variant [recrbis]
     written without [iszero] check. *)

 Fixpoint recrbis_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int31->A->A)
 (i:int31) : A :=
  match n with
  | O => case0
  | S next =>
      let si := shiftr i in
      caserec (firstr i) si (recrbis_aux next A case0 caserec si)
  end.

 Definition recrbis := recrbis_aux size.

 Hypothesis case0_caserec : caserec D0 0 case0 = case0.

 Lemma recrbis_aux_equiv : forall n x,
   recrbis_aux n A case0 caserec x = recr_aux n A case0 caserec x.
 Proof.
 induction n; simpl; auto; intros.
 case_eq (iszero x); intros; [ | f_equal; auto ].
 rewrite (iszero_eq0 _ H); simpl; auto.
 replace (recrbis_aux n A case0 caserec 0) with case0; auto.
 clear H IHn; induction n; simpl; congruence.
 Qed.

 Lemma recrbis_equiv : forall x,
   recrbis A case0 caserec x = recr A case0 caserec x.
 Proof.
 intros; apply recrbis_aux_equiv; auto.
 Qed.

 End Recr.

 (** * Incrementation *)

 Section Incr.

 (** Variant of [incr] via [recrbis] *)

 Let Incr (b : digits) (si rec : int31) :=
  match b with
   | D0 => sneakl D1 si
   | D1 => sneakl D0 rec
  end.

 Definition incrbis_aux n x := recrbis_aux n _ In Incr x.

 Lemma incrbis_aux_equiv : forall x, incrbis_aux size x = incr x.
 Proof.
 unfold incr, recr, incrbis_aux; fold Incr; intros.
 apply recrbis_aux_equiv; auto.
 Qed.

 (** Recursive equations satisfied by [incr] *)

 Lemma incr_eqn1 :
  forall x, firstr x = D0 -> incr x = twice_plus_one (shiftr x).
 Proof.
 intros.
 case_eq (iszero x); intros.
 rewrite (iszero_eq0 _ H0); simpl; auto.
 unfold incr; rewrite recr_eqn; fold incr; auto.
 rewrite H; auto.
 Qed.

 Lemma incr_eqn2 :
  forall x, firstr x = D1 -> incr x = twice (incr (shiftr x)).
 Proof.
 intros.
 case_eq (iszero x); intros.
 rewrite (iszero_eq0 _ H0) in H; simpl in H; discriminate.
 unfold incr; rewrite recr_eqn; fold incr; auto.
 rewrite H; auto.
 Qed.

 Lemma incr_twice : forall x, incr (twice x) = twice_plus_one x.
 Proof.
 intros.
 rewrite incr_eqn1; destruct x; simpl; auto.
 Qed.

 Lemma incr_twice_plus_one_firstl :
  forall x, firstl x = D0 -> incr (twice_plus_one x) = twice (incr x).
 Proof.
 intros.
 rewrite incr_eqn2; [ | destruct x; simpl; auto ].
 f_equal; f_equal.
 destruct x; simpl in *; rewrite H; auto.
 Qed.

 (** The previous result is actually true even without the
     constraint on [firstl], but this is harder to prove
     (see later). *)

 End Incr.

 (** * Conversion to [Z] : the [phi] function *)

 Section Phi.

 (** Variant of [phi] via [recrbis] *)

 Let Phi := fun b (_:int31) =>
       match b with D0 => Zdouble | D1 => Zdouble_plus_one end.

 Definition phibis_aux n x := recrbis_aux n _ Z0 Phi x.

 Lemma phibis_aux_equiv : forall x, phibis_aux size x = phi x.
 Proof.
 unfold phi, recr, phibis_aux; fold Phi; intros.
 apply recrbis_aux_equiv; auto.
 Qed.

 (** Recursive equations satisfied by [phi] *)

 Lemma phi_eqn1 : forall x, firstr x = D0 ->
  phi x = Zdouble (phi (shiftr x)).
 Proof.
 intros.
 case_eq (iszero x); intros.
 rewrite (iszero_eq0 _ H0); simpl; auto.
 intros; unfold phi; rewrite recr_eqn; fold phi; auto.
 rewrite H; auto.
 Qed.

 Lemma phi_eqn2 : forall x, firstr x = D1 ->
  phi x = Zdouble_plus_one (phi (shiftr x)).
 Proof.
 intros.
 case_eq (iszero x); intros.
 rewrite (iszero_eq0 _ H0) in H; simpl in H; discriminate.
 intros; unfold phi; rewrite recr_eqn; fold phi; auto.
 rewrite H; auto.
 Qed.

 Lemma phi_twice_firstl : forall x, firstl x = D0 ->
  phi (twice x) = Zdouble (phi x).
 Proof.
 intros.
 rewrite phi_eqn1; auto; [ | destruct x; auto ].
 f_equal; f_equal.
 destruct x; simpl in *; rewrite H; auto.
 Qed.

 Lemma phi_twice_plus_one_firstl : forall x, firstl x = D0 ->
  phi (twice_plus_one x) = Zdouble_plus_one (phi x).
 Proof.
 intros.
 rewrite phi_eqn2; auto; [ | destruct x; auto ].
 f_equal; f_equal.
 destruct x; simpl in *; rewrite H; auto.
 Qed.

 End Phi.

 (** [phi x] is positive and lower than [2^31] *)

 Lemma phibis_aux_pos : forall n x, (0 <= phibis_aux n x)%Z.
 Proof.
 induction n.
 simpl; unfold phibis_aux; simpl; auto with zarith.
 intros.
 unfold phibis_aux, recrbis_aux; fold recrbis_aux;
  fold (phibis_aux n (shiftr x)).
 destruct (firstr x).
 specialize IHn with (shiftr x); rewrite Zdouble_mult; omega.
 specialize IHn with (shiftr x); rewrite Zdouble_plus_one_mult; omega.
 Qed.

 Lemma phibis_aux_bounded :
  forall n x, n <= size ->
  (phibis_aux n (nshiftr (size-n) x) < 2 ^ (Z_of_nat n))%Z.
 Proof.
 induction n.
 simpl; unfold phibis_aux; simpl; auto with zarith.
 intros.
 unfold phibis_aux, recrbis_aux; fold recrbis_aux;
  fold (phibis_aux n (shiftr (nshiftr (size - S n) x))).
 assert (shiftr (nshiftr (size - S n) x) =  nshiftr (size-n) x).
  replace (size - n)%nat with (S (size - (S n))) by omega.
  simpl; auto.
 rewrite H0.
 assert (H1 : n <= size) by omega.
 specialize (IHn x H1).
 set (y:=phibis_aux n (nshiftr (size - n) x)) in *.
 rewrite inj_S, Zpower_Zsucc; auto with zarith.
 case_eq (firstr (nshiftr (size - S n) x)); intros.
 rewrite Zdouble_mult; auto with zarith.
 rewrite Zdouble_plus_one_mult; auto with zarith.
 Qed.

 Lemma phi_bounded  : forall x, (0 <= phi x < 2 ^ (Z_of_nat size))%Z.
 Proof.
 intros.
 rewrite <- phibis_aux_equiv.
 split.
 apply phibis_aux_pos.
 change x with (nshiftr (size-size) x).
 apply phibis_aux_bounded; auto.
 Qed.

 Lemma phibis_aux_lowerbound :
  forall n x, firstr (nshiftr n x) = D1 ->
  (2 ^ Z_of_nat n <= phibis_aux (S n) x)%Z.
 Proof.
 induction n.
 intros.
 unfold nshiftr in H; simpl in *.
 unfold phibis_aux, recrbis_aux.
 rewrite H, Zdouble_plus_one_mult; omega.

 intros.
 remember (S n) as m.
 unfold phibis_aux, recrbis_aux; fold recrbis_aux;
  fold (phibis_aux m (shiftr x)).
 subst m.
 rewrite inj_S, Zpower_Zsucc; auto with zarith.
 assert (2^(Z_of_nat n) <= phibis_aux (S n) (shiftr x))%Z.
  apply IHn.
  rewrite <- nshiftr_S_tail; auto.
 destruct (firstr x).
 change (Zdouble (phibis_aux (S n) (shiftr x))) with
        (2*(phibis_aux (S n) (shiftr x)))%Z.
 omega.
 rewrite Zdouble_plus_one_mult; omega.
 Qed.

 Lemma phi_lowerbound :
  forall x, firstl x = D1 -> (2^(Z_of_nat (pred size)) <= phi x)%Z.
 Proof.
 intros.
 generalize (phibis_aux_lowerbound (pred size) x).
 rewrite <- firstl_firstr.
 change (S (pred size)) with size; auto.
 rewrite phibis_aux_equiv; auto.
 Qed.

 (** * Equivalence modulo [2^n] *)

 Section EqShiftL.

 (** After killing [n] bits at the left, are the numbers equal ?*)

 Definition EqShiftL n x y :=
  nshiftl n x = nshiftl n y.

 Lemma EqShiftL_zero : forall x y, EqShiftL O x y <-> x = y.
 Proof.
 unfold EqShiftL; intros; unfold nshiftl; simpl; split; auto.
 Qed.

 Lemma EqShiftL_size : forall k x y, size<=k -> EqShiftL k x y.
 Proof.
 red; intros; rewrite 2 nshiftl_above_size; auto.
 Qed.

 Lemma EqShiftL_le : forall k k' x y, k <= k' ->
   EqShiftL k x y -> EqShiftL k' x y.
 Proof.
 unfold EqShiftL; intros.
 replace k' with ((k'-k)+k)%nat by omega.
 remember (k'-k)%nat as n.
 clear Heqn H k'.
 induction n; simpl; auto.
 rewrite 2 nshiftl_S; f_equal; auto.
 Qed.

 Lemma EqShiftL_firstr : forall k x y, k < size ->
  EqShiftL k x y -> firstr x = firstr y.
 Proof.
 intros.
 rewrite 2 firstr_firstl.
 f_equal.
 apply EqShiftL_le with k; auto.
 unfold size.
 auto with arith.
 Qed.

 Lemma EqShiftL_twice : forall k x y,
  EqShiftL k (twice x) (twice y) <-> EqShiftL (S k) x y.
 Proof.
 intros; unfold EqShiftL.
 rewrite 2 nshiftl_S_tail; split; auto.
 Qed.

 (** * From int31 to list of digits. *)

 (** Lower (=rightmost) bits comes first. *)

 Definition i2l := recrbis _ nil (fun d _ rec => d::rec).

 Lemma i2l_length : forall x, length (i2l x) = size.
 Proof.
 intros; reflexivity.
 Qed.

 Fixpoint lshiftl l x :=
   match l with
     | nil => x
     | d::l => sneakl d (lshiftl l x)
   end.

 Definition l2i l := lshiftl l On.

 Lemma l2i_i2l : forall x, l2i (i2l x) = x.
 Proof.
 destruct x; compute; auto.
 Qed.

 Lemma i2l_sneakr : forall x d,
   i2l (sneakr d x) = tail (i2l x) ++ d::nil.
 Proof.
 destruct x; compute; auto.
 Qed.

 Lemma i2l_sneakl : forall x d,
   i2l (sneakl d x) = d :: removelast (i2l x).
 Proof.
 destruct x; compute; auto.
 Qed.

 Lemma i2l_l2i : forall l, length l = size ->
  i2l (l2i l) = l.
 Proof.
 repeat (destruct l as [ |? l]; [intros; discriminate | ]).
 destruct l; [ | intros; discriminate].
 intros _; compute; auto.
 Qed.

 Fixpoint cstlist (A:Type)(a:A) n :=
  match n with
   | O => nil
   | S n => a::cstlist _ a n
  end.

 Lemma i2l_nshiftl : forall n x, n<=size ->
  i2l (nshiftl n x) = cstlist _ D0 n ++ firstn (size-n) (i2l x).
 Proof.
 induction n.
 intros.
 assert (firstn (size-0) (i2l x) = i2l x).
  rewrite <- minus_n_O, <- (i2l_length x).
  induction (i2l x); simpl; f_equal; auto.
 rewrite H0; clear H0.
 reflexivity.

 intros.
 rewrite nshiftl_S.
 unfold shiftl; rewrite i2l_sneakl.
 simpl cstlist.
 rewrite <- app_comm_cons; f_equal.
 rewrite IHn; [ | omega].
 rewrite removelast_app.
 f_equal.
 replace (size-n)%nat with (S (size - S n))%nat by omega.
 rewrite removelast_firstn; auto.
 rewrite i2l_length; omega.
 generalize (firstn_length (size-n) (i2l x)).
 rewrite i2l_length.
 intros H0 H1; rewrite H1 in H0.
 rewrite min_l in H0 by omega.
 simpl length in H0.
 omega.
 Qed.

 (** [i2l] can be used to define a relation equivalent to [EqShiftL] *)

 Lemma EqShiftL_i2l : forall k x y,
   EqShiftL k x y  <-> firstn (size-k) (i2l x) = firstn (size-k) (i2l y).
 Proof.
 intros.
 destruct (le_lt_dec size k).
 split; intros.
 replace (size-k)%nat with O by omega.
 unfold firstn; auto.
 apply EqShiftL_size; auto.

 unfold EqShiftL.
 assert (k <= size) by omega.
 split; intros.
 assert (i2l (nshiftl k x) = i2l (nshiftl k y)) by (f_equal; auto).
 rewrite 2 i2l_nshiftl in H1; auto.
 eapply app_inv_head; eauto.
 assert (i2l (nshiftl k x) = i2l (nshiftl k y)).
  rewrite 2 i2l_nshiftl; auto.
  f_equal; auto.
 rewrite <- (l2i_i2l (nshiftl k x)), <- (l2i_i2l (nshiftl k y)).
 f_equal; auto.
 Qed.

 (** This equivalence allows to prove easily the following delicate
     result *)

 Lemma EqShiftL_twice_plus_one : forall k x y,
  EqShiftL k (twice_plus_one x) (twice_plus_one y) <-> EqShiftL (S k) x y.
 Proof.
 intros.
 destruct (le_lt_dec size k).
 split; intros; apply EqShiftL_size; auto.

 rewrite 2 EqShiftL_i2l.
 unfold twice_plus_one.
 rewrite 2 i2l_sneakl.
 replace (size-k)%nat with (S (size - S k))%nat by omega.
 remember (size - S k)%nat as n.
 remember (i2l x) as lx.
 remember (i2l y) as ly.
 simpl.
 rewrite 2 firstn_removelast.
 split; intros.
 injection H; auto.
 f_equal; auto.
 subst ly n; rewrite i2l_length; omega.
 subst lx n; rewrite i2l_length; omega.
 Qed.

 Lemma EqShiftL_shiftr : forall k x y, EqShiftL k x y ->
  EqShiftL (S k) (shiftr x) (shiftr y).
 Proof.
 intros.
 destruct (le_lt_dec size (S k)).
 apply EqShiftL_size; auto.
 case_eq (firstr x); intros.
 rewrite <- EqShiftL_twice.
 unfold twice; rewrite <- H0.
 rewrite <- sneakl_shiftr.
 rewrite (EqShiftL_firstr k x y); auto.
 rewrite <- sneakl_shiftr; auto.
 omega.
 rewrite <- EqShiftL_twice_plus_one.
 unfold twice_plus_one; rewrite <- H0.
 rewrite <- sneakl_shiftr.
 rewrite (EqShiftL_firstr k x y); auto.
 rewrite <- sneakl_shiftr; auto.
 omega.
 Qed.

 Lemma EqShiftL_incrbis : forall n k x y, n<=size ->
  (n+k=S size)%nat ->
  EqShiftL k x y ->
  EqShiftL k (incrbis_aux n x) (incrbis_aux n y).
 Proof.
 induction n; simpl; intros.
 red; auto.
 destruct (eq_nat_dec k size).
  subst k; apply EqShiftL_size; auto.
 unfold incrbis_aux; simpl;
  fold (incrbis_aux n (shiftr x)); fold (incrbis_aux n (shiftr y)).

 rewrite (EqShiftL_firstr k x y); auto; try omega.
 case_eq (firstr y); intros.
 rewrite EqShiftL_twice_plus_one.
 apply EqShiftL_shiftr; auto.

 rewrite EqShiftL_twice.
 apply IHn; try omega.
 apply EqShiftL_shiftr; auto.
 Qed.

 Lemma EqShiftL_incr : forall x y,
  EqShiftL 1 x y -> EqShiftL 1 (incr x) (incr y).
 Proof.
 intros.
 rewrite <- 2 incrbis_aux_equiv.
 apply EqShiftL_incrbis; auto.
 Qed.

 End EqShiftL.

 (** * More equations about [incr] *)

 Lemma incr_twice_plus_one :
  forall x, incr (twice_plus_one x) = twice (incr x).
 Proof.
 intros.
 rewrite incr_eqn2; [ | destruct x; simpl; auto].
 apply EqShiftL_incr.
 red; destruct x; simpl; auto.
 Qed.

 Lemma incr_firstr : forall x, firstr (incr x) <> firstr x.
 Proof.
 intros.
 case_eq (firstr x); intros.
 rewrite incr_eqn1; auto.
 destruct (shiftr x); simpl; discriminate.
 rewrite incr_eqn2; auto.
 destruct (incr (shiftr x)); simpl; discriminate.
 Qed.

 Lemma incr_inv : forall x y,
  incr x = twice_plus_one y -> x = twice y.
 Proof.
 intros.
 case_eq (iszero x); intros.
 rewrite (iszero_eq0 _ H0) in *; simpl in *.
 change (incr 0) with 1 in H.
 symmetry; rewrite twice_zero; auto.
 case_eq (firstr x); intros.
 rewrite incr_eqn1 in H; auto.
 clear H0; destruct x; destruct y; simpl in *.
 injection H; intros; subst; auto.
 elim (incr_firstr x).
 rewrite H1, H; destruct y; simpl; auto.
 Qed.

 (** * Conversion from [Z] : the [phi_inv] function *)

 (** First, recursive equations *)

 Lemma phi_inv_double_plus_one : forall z,
   phi_inv (Zdouble_plus_one z) = twice_plus_one (phi_inv z).
 Proof.
 destruct z; simpl; auto.
 induction p; simpl.
 rewrite 2 incr_twice; auto.
 rewrite incr_twice, incr_twice_plus_one.
 f_equal.
 apply incr_inv; auto.
 auto.
 Qed.

 Lemma phi_inv_double : forall z,
   phi_inv (Zdouble z) = twice (phi_inv z).
 Proof.
 destruct z; simpl; auto.
 rewrite incr_twice_plus_one; auto.
 Qed.

 Lemma phi_inv_incr : forall z,
  phi_inv (Zsucc z) = incr (phi_inv z).
 Proof.
 destruct z.
 simpl; auto.
 simpl; auto.
 induction p; simpl; auto.
 rewrite Pplus_one_succ_r, IHp, incr_twice_plus_one; auto.
 rewrite incr_twice; auto.
 simpl; auto.
 destruct p; simpl; auto.
 rewrite incr_twice; auto.
 f_equal.
 rewrite incr_twice_plus_one; auto.
 induction p; simpl; auto.
 rewrite incr_twice; auto.
 f_equal.
 rewrite incr_twice_plus_one; auto.
 Qed.

 (** [phi_inv o inv], the always-exact and easy-to-prove trip :
     from int31 to Z and then back to int31. *)

 Lemma phi_inv_phi_aux :
  forall n x, n <= size ->
   phi_inv (phibis_aux n (nshiftr (size-n) x)) =
   nshiftr (size-n) x.
 Proof.
 induction n.
 intros; simpl.
 rewrite nshiftr_size; auto.
 intros.
 unfold phibis_aux, recrbis_aux; fold recrbis_aux;
  fold (phibis_aux n (shiftr (nshiftr (size-S n) x))).
 assert (shiftr (nshiftr (size - S n) x) = nshiftr (size-n) x).
  replace (size - n)%nat with (S (size - (S n))); auto; omega.
 rewrite H0.
 case_eq (firstr (nshiftr (size - S n) x)); intros.

 rewrite phi_inv_double.
 rewrite IHn by omega.
 rewrite <- H0.
 remember (nshiftr (size - S n) x) as y.
 destruct y; simpl in H1; rewrite H1; auto.

 rewrite phi_inv_double_plus_one.
 rewrite IHn by omega.
 rewrite <- H0.
 remember (nshiftr (size - S n) x) as y.
 destruct y; simpl in H1; rewrite H1; auto.
 Qed.

 Lemma phi_inv_phi : forall x, phi_inv (phi x) = x.
 Proof.
 intros.
 rewrite <- phibis_aux_equiv.
 replace x with (nshiftr (size - size) x) by auto.
 apply phi_inv_phi_aux; auto.
 Qed.

 (** The other composition [phi o phi_inv] is harder to prove correct.
     In particular, an overflow can happen, so a modulo is needed.
     For the moment, we proceed via several steps, the first one
     being a detour to [positive_to_in31]. *)

 (** * [positive_to_int31] *)

 (** A variant of [p2i] with [twice] and [twice_plus_one] instead of
     [2*i] and [2*i+1] *)

 Fixpoint p2ibis n p : (N*int31)%type :=
  match n with
    | O => (Npos p, On)
    | S n => match p with
               | xO p => let (r,i) := p2ibis n p in (r, twice i)
               | xI p => let (r,i) := p2ibis n p in (r, twice_plus_one i)
               | xH => (N0, In)
             end
  end.

 Lemma p2ibis_bounded : forall n p,
  nshiftr n (snd (p2ibis n p)) = 0.
 Proof.
 induction n.
 simpl; intros; auto.
 simpl; intros.
 destruct p; simpl.

 specialize IHn with p.
 destruct (p2ibis n p); simpl in *.
 rewrite nshiftr_S_tail.
 destruct (le_lt_dec size n).
 rewrite nshiftr_above_size; auto.
 assert (H:=nshiftr_0_firstl _ _ l IHn).
 replace (shiftr (twice_plus_one i)) with i; auto.
 destruct i; simpl in *; rewrite H; auto.

 specialize IHn with p.
 destruct (p2ibis n p); simpl in *.
 rewrite nshiftr_S_tail.
 destruct (le_lt_dec size n).
 rewrite nshiftr_above_size; auto.
 assert (H:=nshiftr_0_firstl _ _ l IHn).
 replace (shiftr (twice i)) with i; auto.
 destruct i; simpl in *; rewrite H; auto.

 rewrite nshiftr_S_tail; auto.
 replace (shiftr In) with 0; auto.
 apply nshiftr_n_0.
 Qed.

 Lemma p2ibis_spec : forall n p, n<=size ->
    Zpos p = ((Z_of_N (fst (p2ibis n p)))*2^(Z_of_nat n) +
             phi (snd (p2ibis n p)))%Z.
 Proof.
 induction n; intros.
 simpl; rewrite Pmult_1_r; auto.
 replace (2^(Z_of_nat (S n)))%Z with (2*2^(Z_of_nat n))%Z by
  (rewrite <- Zpower_Zsucc, <- Zpos_P_of_succ_nat;
   auto with zarith).
 rewrite (Zmult_comm 2).
 assert (n<=size) by omega.
 destruct p; simpl; [ | | auto];
  specialize (IHn p H0);
  generalize (p2ibis_bounded n p);
  destruct (p2ibis n p) as (r,i); simpl in *; intros.

 change (Zpos p~1) with (2*Zpos p + 1)%Z.
 rewrite phi_twice_plus_one_firstl, Zdouble_plus_one_mult.
 rewrite IHn; ring.
 apply (nshiftr_0_firstl n); auto; try omega.

 change (Zpos p~0) with (2*Zpos p)%Z.
 rewrite phi_twice_firstl.
 change (Zdouble (phi i)) with (2*(phi i))%Z.
 rewrite IHn; ring.
 apply (nshiftr_0_firstl n); auto; try omega.
 Qed.

 (** We now prove that this [p2ibis] is related to [phi_inv_positive] *)

 Lemma phi_inv_positive_p2ibis : forall n p, (n<=size)%nat ->
  EqShiftL (size-n) (phi_inv_positive p) (snd (p2ibis n p)).
 Proof.
 induction n.
 intros.
 apply EqShiftL_size; auto.
 intros.
 simpl p2ibis; destruct p; [ | | red; auto];
  specialize IHn with p;
  destruct (p2ibis n p); simpl snd in *; simpl phi_inv_positive;
  rewrite ?EqShiftL_twice_plus_one, ?EqShiftL_twice;
  replace (S (size - S n))%nat with (size - n)%nat by omega;
  apply IHn; omega.
 Qed.

 (** This gives the expected result about [phi o phi_inv], at least
     for the positive case. *)

 Lemma phi_phi_inv_positive : forall p,
  phi (phi_inv_positive p) = (Zpos p) mod (2^(Z_of_nat size)).
 Proof.
 intros.
 replace (phi_inv_positive p) with (snd (p2ibis size p)).
 rewrite (p2ibis_spec size p) by auto.
 rewrite Zplus_comm, Z_mod_plus.
 symmetry; apply Zmod_small.
 apply phi_bounded.
 auto with zarith.
 symmetry.
 rewrite <- EqShiftL_zero.
 apply (phi_inv_positive_p2ibis size p); auto.
 Qed.

 (** Moreover, [p2ibis] is also related with [p2i] and hence with
    [positive_to_int31]. *)

 Lemma double_twice_firstl : forall x, firstl x = D0 -> Twon*x = twice x.
 Proof.
 intros.
 unfold mul31.
 rewrite <- Zdouble_mult, <- phi_twice_firstl, phi_inv_phi; auto.
 Qed.

 Lemma double_twice_plus_one_firstl : forall x, firstl x = D0 ->
  Twon*x+In = twice_plus_one x.
 Proof.
 intros.
 rewrite double_twice_firstl; auto.
 unfold add31.
 rewrite phi_twice_firstl, <- Zdouble_plus_one_mult,
   <- phi_twice_plus_one_firstl, phi_inv_phi; auto.
 Qed.

 Lemma p2i_p2ibis : forall n p, (n<=size)%nat ->
  p2i n p = p2ibis n p.
 Proof.
 induction n; simpl; auto; intros.
 destruct p; auto; specialize IHn with p;
  generalize (p2ibis_bounded n p);
  rewrite IHn; try omega; destruct (p2ibis n p); simpl; intros;
  f_equal; auto.
 apply double_twice_plus_one_firstl.
 apply (nshiftr_0_firstl n); auto; omega.
 apply double_twice_firstl.
 apply (nshiftr_0_firstl n); auto; omega.
 Qed.

 Lemma positive_to_int31_phi_inv_positive : forall p,
   snd (positive_to_int31 p) = phi_inv_positive p.
 Proof.
 intros; unfold positive_to_int31.
 rewrite p2i_p2ibis; auto.
 symmetry.
 rewrite <- EqShiftL_zero.
 apply (phi_inv_positive_p2ibis size); auto.
 Qed.

 Lemma positive_to_int31_spec : forall p,
    Zpos p = ((Z_of_N (fst (positive_to_int31 p)))*2^(Z_of_nat size) +
               phi (snd (positive_to_int31 p)))%Z.
 Proof.
 unfold positive_to_int31.
 intros; rewrite p2i_p2ibis; auto.
 apply p2ibis_spec; auto.
 Qed.

 (** Thanks to the result about [phi o phi_inv_positive], we can
     now establish easily the most general results about
     [phi o twice] and so one. *)

 Lemma phi_twice : forall x,
   phi (twice x) = (Zdouble (phi x)) mod 2^(Z_of_nat size).
 Proof.
 intros.
 pattern x at 1; rewrite <- (phi_inv_phi x).
 rewrite <- phi_inv_double.
 assert (0 <= Zdouble (phi x))%Z.
  rewrite Zdouble_mult; generalize (phi_bounded x); omega.
 destruct (Zdouble (phi x)).
 simpl; auto.
 apply phi_phi_inv_positive.
 compute in H; elim H; auto.
 Qed.

 Lemma phi_twice_plus_one : forall x,
   phi (twice_plus_one x) = (Zdouble_plus_one (phi x)) mod 2^(Z_of_nat size).
 Proof.
 intros.
 pattern x at 1; rewrite <- (phi_inv_phi x).
 rewrite <- phi_inv_double_plus_one.
 assert (0 <= Zdouble_plus_one (phi x))%Z.
  rewrite Zdouble_plus_one_mult; generalize (phi_bounded x); omega.
 destruct (Zdouble_plus_one (phi x)).
 simpl; auto.
 apply phi_phi_inv_positive.
 compute in H; elim H; auto.
 Qed.

 Lemma phi_incr : forall x,
   phi (incr x) = (Zsucc (phi x)) mod 2^(Z_of_nat size).
 Proof.
 intros.
 pattern x at 1; rewrite <- (phi_inv_phi x).
 rewrite <- phi_inv_incr.
 assert (0 <= Zsucc (phi x))%Z.
  change (Zsucc (phi x)) with ((phi x)+1)%Z;
   generalize (phi_bounded x); omega.
 destruct (Zsucc (phi x)).
 simpl; auto.
 apply phi_phi_inv_positive.
 compute in H; elim H; auto.
 Qed.

 (** With the previous results, we can deal with [phi o phi_inv] even
    in the negative case *)

 Lemma phi_phi_inv_negative :
  forall p, phi (incr (complement_negative p)) = (Zneg p) mod 2^(Z_of_nat size).
 Proof.
 induction p.

 simpl complement_negative.
 rewrite phi_incr in IHp.
 rewrite incr_twice, phi_twice_plus_one.
 remember (phi (complement_negative p)) as q.
 rewrite Zdouble_plus_one_mult.
 replace (2*q+1)%Z with (2*(Zsucc q)-1)%Z by omega.
 rewrite <- Zminus_mod_idemp_l, <- Zmult_mod_idemp_r, IHp.
 rewrite Zmult_mod_idemp_r, Zminus_mod_idemp_l; auto with zarith.

 simpl complement_negative.
 rewrite incr_twice_plus_one, phi_twice.
 remember (phi (incr (complement_negative p))) as q.
 rewrite Zdouble_mult, IHp, Zmult_mod_idemp_r; auto with zarith.

 simpl; auto.
 Qed.

 Lemma phi_phi_inv :
  forall z, phi (phi_inv z) = z mod 2 ^ (Z_of_nat size).
 Proof.
 destruct z.
 simpl; auto.
 apply phi_phi_inv_positive.
 apply phi_phi_inv_negative.
 Qed.

End Basics.


Section Int31_Op.

(** Nullity test *)
Let w_iszero i := match i ?= 0 with Eq => true | _ => false end.

(** Modulo [2^p] *)
Let w_pos_mod p i :=
  match compare31 p 31 with
    | Lt => addmuldiv31 p 0 (addmuldiv31 (31-p) i 0)
    | _ => i
  end.

(** Parity test *)
Let w_iseven i :=
 let (_,r) := i/2 in
 match r ?= 0 with Eq => true | _ => false end.

Definition int31_op := (mk_znz_op
 31%positive (* number of digits *)
 31 (* number of digits *)
 phi (* conversion to Z *)
 positive_to_int31 (* positive -> N*int31 :  p => N,i where p = N*2^31+phi i *)
 head031  (* number of head 0 *)
 tail031  (* number of tail 0 *)
 (* Basic constructors *)
 0
 1
 Tn (* 2^31 - 1 *)
 (* Comparison *)
 compare31
 w_iszero
 (* Basic arithmetic operations *)
 (fun i => 0 -c i)
 opp31
 (fun i => 0-i-1)
 (fun i => i +c 1)
 add31c
 add31carryc
 (fun i => i + 1)
 add31
 (fun i j => i + j + 1)
 (fun i => i -c 1)
 sub31c
 sub31carryc
 (fun i => i - 1)
 sub31
 (fun i j => i - j - 1)
 mul31c
 mul31
 (fun x => x *c x)
 (* special (euclidian) division operations *)
 div3121
 div31 (* this is supposed to be the special case of division a/b where a > b *)
 div31
 (* euclidian division remainder *)
 (* again special case for a > b *)
 (fun i j => let (_,r) := i/j in r)
 (fun i j => let (_,r) := i/j in r)
 gcd31 (*gcd_gt*)
 gcd31 (*gcd*)
 (* shift operations *)
 addmuldiv31 (*add_mul_div  *)
 (* modulo 2^p *)
 w_pos_mod
 (* is i even ? *)
 w_iseven
 (* square root operations *)
 sqrt312 (* sqrt2 *)
 sqrt31 (* sqrt *)
).

End Int31_Op.

Section Int31_Spec.

 Local Open Scope Z_scope.

 Notation "[| x |]" := (phi x)  (at level 0, x at level 99).

 Local Notation wB := (2 ^ (Z_of_nat size)).

 Lemma wB_pos : wB > 0.
 Proof.
  auto with zarith.
 Qed.

 Notation "[+| c |]" :=
   (interp_carry 1 wB phi c)  (at level 0, x at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) wB phi c)  (at level 0, x at level 99).

 Notation "[|| x ||]" :=
   (zn2z_to_Z wB phi x)  (at level 0, x at level 99).

 Lemma spec_zdigits : [| 31 |] = 31.
 Proof.
  reflexivity.
 Qed.

 Lemma spec_more_than_1_digit: 1 < 31.
 Proof.
  auto with zarith.
 Qed.

 Lemma spec_0   : [| 0 |] = 0.
 Proof.
  reflexivity.
 Qed.

 Lemma spec_1   : [| 1 |] = 1.
 Proof.
  reflexivity.
 Qed.

 Lemma spec_Bm1 : [| Tn |] = wB - 1.
 Proof.
  reflexivity.
 Qed.

 Lemma spec_compare : forall x y,
   match (x ?= y)%int31 with
     | Eq => [|x|] = [|y|]
     | Lt => [|x|] < [|y|]
     | Gt => [|x|] > [|y|]
   end.
 Proof.
 clear; unfold compare31; simpl; intros.
 case_eq ([|x|] ?= [|y|]); auto.
 intros; apply Zcompare_Eq_eq; auto.
 Qed.

 (** Addition *)

 Lemma spec_add_c  : forall x y, [+|add31c x y|] = [|x|] + [|y|].
 Proof.
 intros; unfold add31c, add31, interp_carry; rewrite phi_phi_inv.
 generalize (phi_bounded x)(phi_bounded y); intros.
 set (X:=[|x|]) in *; set (Y:=[|y|]) in *; clearbody X Y.

 assert ((X+Y) mod wB ?= X+Y <> Eq -> [+|C1 (phi_inv (X+Y))|] = X+Y).
  unfold interp_carry; rewrite phi_phi_inv, Zcompare_Eq_iff_eq; intros.
  destruct (Z_lt_le_dec (X+Y) wB).
  contradict H1; auto using Zmod_small with zarith.
  rewrite <- (Z_mod_plus_full (X+Y) (-1) wB).
  rewrite Zmod_small; romega.

 generalize (Zcompare_Eq_eq ((X+Y) mod wB) (X+Y)); intros Heq.
 destruct Zcompare; intros;
  [ rewrite phi_phi_inv; auto | now apply H1 | now apply H1].
 Qed.

 Lemma spec_succ_c : forall x, [+|add31c x 1|] = [|x|] + 1.
 Proof.
 intros; apply spec_add_c.
 Qed.

 Lemma spec_add_carry_c : forall x y, [+|add31carryc x y|] = [|x|] + [|y|] + 1.
 Proof.
 intros.
 unfold add31carryc, interp_carry; rewrite phi_phi_inv.
 generalize (phi_bounded x)(phi_bounded y); intros.
 set (X:=[|x|]) in *; set (Y:=[|y|]) in *; clearbody X Y.

 assert ((X+Y+1) mod wB ?= X+Y+1 <> Eq -> [+|C1 (phi_inv (X+Y+1))|] = X+Y+1).
  unfold interp_carry; rewrite phi_phi_inv, Zcompare_Eq_iff_eq; intros.
  destruct (Z_lt_le_dec (X+Y+1) wB).
  contradict H1; auto using Zmod_small with zarith.
  rewrite <- (Z_mod_plus_full (X+Y+1) (-1) wB).
  rewrite Zmod_small; romega.

 generalize (Zcompare_Eq_eq ((X+Y+1) mod wB) (X+Y+1)); intros Heq.
 destruct Zcompare; intros;
  [ rewrite phi_phi_inv; auto | now apply H1 | now apply H1].
 Qed.

 Lemma spec_add : forall x y, [|x+y|] = ([|x|] + [|y|]) mod wB.
 Proof.
 intros; apply phi_phi_inv.
 Qed.

 Lemma spec_add_carry :
	 forall x y, [|x+y+1|] = ([|x|] + [|y|] + 1) mod wB.
 Proof.
 unfold add31; intros.
 repeat rewrite phi_phi_inv.
 apply Zplus_mod_idemp_l.
 Qed.

 Lemma spec_succ : forall x, [|x+1|] = ([|x|] + 1) mod wB.
 Proof.
 intros; rewrite <- spec_1; apply spec_add.
 Qed.

 (** Substraction *)

 Lemma spec_sub_c : forall x y, [-|sub31c x y|] = [|x|] - [|y|].
 Proof.
 unfold sub31c, sub31, interp_carry; intros.
 rewrite phi_phi_inv.
 generalize (phi_bounded x)(phi_bounded y); intros.
 set (X:=[|x|]) in *; set (Y:=[|y|]) in *; clearbody X Y.

 assert ((X-Y) mod wB ?= X-Y <> Eq -> [-|C1 (phi_inv (X-Y))|] = X-Y).
  unfold interp_carry; rewrite phi_phi_inv, Zcompare_Eq_iff_eq; intros.
  destruct (Z_lt_le_dec (X-Y) 0).
  rewrite <- (Z_mod_plus_full (X-Y) 1 wB).
  rewrite Zmod_small; romega.
  contradict H1; apply Zmod_small; romega.

 generalize (Zcompare_Eq_eq ((X-Y) mod wB) (X-Y)); intros Heq.
 destruct Zcompare; intros;
  [ rewrite phi_phi_inv; auto | now apply H1 | now apply H1].
 Qed.

 Lemma spec_sub_carry_c : forall x y, [-|sub31carryc x y|] = [|x|] - [|y|] - 1.
 Proof.
 unfold sub31carryc, sub31, interp_carry; intros.
 rewrite phi_phi_inv.
 generalize (phi_bounded x)(phi_bounded y); intros.
 set (X:=[|x|]) in *; set (Y:=[|y|]) in *; clearbody X Y.

 assert ((X-Y-1) mod wB ?= X-Y-1 <> Eq -> [-|C1 (phi_inv (X-Y-1))|] = X-Y-1).
  unfold interp_carry; rewrite phi_phi_inv, Zcompare_Eq_iff_eq; intros.
  destruct (Z_lt_le_dec (X-Y-1) 0).
  rewrite <- (Z_mod_plus_full (X-Y-1) 1 wB).
  rewrite Zmod_small; romega.
  contradict H1; apply Zmod_small; romega.

 generalize (Zcompare_Eq_eq ((X-Y-1) mod wB) (X-Y-1)); intros Heq.
 destruct Zcompare; intros;
  [ rewrite phi_phi_inv; auto | now apply H1 | now apply H1].
 Qed.

 Lemma spec_sub : forall x y, [|x-y|] = ([|x|] - [|y|]) mod wB.
 Proof.
 intros; apply phi_phi_inv.
 Qed.

 Lemma spec_sub_carry :
   forall x y, [|x-y-1|] = ([|x|] - [|y|] - 1) mod wB.
 Proof.
 unfold sub31; intros.
 repeat rewrite phi_phi_inv.
 apply Zminus_mod_idemp_l.
 Qed.

 Lemma spec_opp_c : forall x, [-|sub31c 0 x|] = -[|x|].
 Proof.
 intros; apply spec_sub_c.
 Qed.

 Lemma spec_opp : forall x, [|0 - x|] = (-[|x|]) mod wB.
 Proof.
 intros; apply phi_phi_inv.
 Qed.

 Lemma spec_opp_carry : forall x, [|0 - x - 1|] = wB - [|x|] - 1.
 Proof.
 unfold sub31; intros.
 repeat rewrite phi_phi_inv.
 change [|1|] with 1; change [|0|] with 0.
 rewrite <- (Z_mod_plus_full (0-[|x|]) 1 wB).
 rewrite Zminus_mod_idemp_l.
 rewrite Zmod_small; generalize (phi_bounded x); romega.
 Qed.

 Lemma spec_pred_c : forall x, [-|sub31c x 1|] = [|x|] - 1.
 Proof.
 intros; apply spec_sub_c.
 Qed.

 Lemma spec_pred : forall x, [|x-1|] = ([|x|] - 1) mod wB.
 Proof.
 intros; apply spec_sub.
 Qed.

 (** Multiplication *)

 Lemma phi2_phi_inv2 : forall x, [||phi_inv2 x||] = x mod (wB^2).
 Proof.
 assert (forall z, (z / wB) mod wB * wB + z mod wB = z mod wB ^ 2).
  intros.
  assert ((z/wB) mod wB = z/wB - (z/wB/wB)*wB).
   rewrite (Z_div_mod_eq (z/wB) wB wB_pos) at 2; ring.
  assert (z mod wB = z - (z/wB)*wB).
   rewrite (Z_div_mod_eq z wB wB_pos) at 2; ring.
  rewrite H.
  rewrite H0 at 1.
  ring_simplify.
  rewrite Zdiv_Zdiv; auto with zarith.
  rewrite (Z_div_mod_eq z (wB*wB)) at 2; auto with zarith.
  change (wB*wB) with (wB^2); ring.

 unfold phi_inv2.
 destruct x; unfold zn2z_to_Z; rewrite ?phi_phi_inv;
  change base with wB; auto.
 Qed.

 Lemma spec_mul_c : forall x y, [|| mul31c x y ||] = [|x|] * [|y|].
 Proof.
 unfold mul31c; intros.
 rewrite phi2_phi_inv2.
 apply Zmod_small.
 generalize (phi_bounded x)(phi_bounded y); intros.
 change (wB^2) with (wB * wB).
 auto using Zmult_lt_compat with zarith.
 Qed.

 Lemma spec_mul : forall x y, [|x*y|] = ([|x|] * [|y|]) mod wB.
 Proof.
 intros; apply phi_phi_inv.
 Qed.

 Lemma spec_square_c : forall x, [|| mul31c x x ||] = [|x|] * [|x|].
 Proof.
 intros; apply spec_mul_c.
 Qed.

 (** Division *)

 Lemma spec_div21 : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := div3121 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 unfold div3121; intros.
 generalize (phi_bounded a1)(phi_bounded a2)(phi_bounded b); intros.
 assert ([|b|]>0) by (auto with zarith).
 generalize (Z_div_mod (phi2 a1 a2) [|b|] H4) (Z_div_pos (phi2 a1 a2) [|b|] H4).
 unfold Zdiv; destruct (Zdiv_eucl (phi2 a1 a2) [|b|]); simpl.
 rewrite ?phi_phi_inv.
 destruct 1; intros.
 unfold phi2 in *.
 change base with wB; change base with wB in H5.
 change (Zpower_pos 2 31) with wB; change (Zpower_pos 2 31) with wB in H.
 rewrite H5, Zmult_comm.
 replace (z0 mod wB) with z0 by (symmetry; apply Zmod_small; omega).
 replace (z mod wB) with z; auto with zarith.
  symmetry; apply Zmod_small.
  split.
  apply H7; change base with wB; auto with zarith.
  apply Zmult_gt_0_lt_reg_r with [|b|].
  omega.
  rewrite Zmult_comm.
  apply Zle_lt_trans with ([|b|]*z+z0).
  omega.
  rewrite <- H5.
  apply Zle_lt_trans with ([|a1|]*wB+(wB-1)).
  omega.
  replace ([|a1|]*wB+(wB-1)) with (wB*([|a1|]+1)-1) by ring.
  assert (wB*([|a1|]+1) <= wB*[|b|]); try omega.
  apply Zmult_le_compat; omega.
 Qed.

 Lemma spec_div : forall a b, 0 < [|b|] ->
      let (q,r) := div31 a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
 unfold div31; intros.
 assert ([|b|]>0) by (auto with zarith).
 generalize (Z_div_mod [|a|] [|b|] H0) (Z_div_pos [|a|] [|b|] H0).
 unfold Zdiv; destruct (Zdiv_eucl [|a|] [|b|]); simpl.
 rewrite ?phi_phi_inv.
 destruct 1; intros.
 rewrite H1, Zmult_comm.
 generalize (phi_bounded a)(phi_bounded b); intros.
 replace (z0 mod wB) with z0 by (symmetry; apply Zmod_small; omega).
 replace (z mod wB) with z; auto with zarith.
  symmetry; apply Zmod_small.
  split; auto with zarith.
  apply Zle_lt_trans with [|a|]; auto with zarith.
  rewrite H1.
  apply Zle_trans with ([|b|]*z); try omega.
  rewrite <- (Zmult_1_l z) at 1.
  apply Zmult_le_compat; auto with zarith.
 Qed.

 Lemma spec_mod :  forall a b, 0 < [|b|] ->
      [|let (_,r) := (a/b)%int31 in r|] = [|a|] mod [|b|].
 Proof.
 unfold div31; intros.
 assert ([|b|]>0) by (auto with zarith).
 unfold Zmod.
 generalize (Z_div_mod [|a|] [|b|] H0).
 destruct (Zdiv_eucl [|a|] [|b|]); simpl.
 rewrite ?phi_phi_inv.
 destruct 1; intros.
 generalize (phi_bounded b); intros.
 apply Zmod_small; omega.
 Qed.

 Lemma phi_gcd : forall i j,
  [|gcd31 i j|] = Zgcdn (2*size) [|j|] [|i|].
 Proof.
  unfold gcd31.
  induction (2*size)%nat; intros.
  reflexivity.
  simpl.
  unfold compare31.
  change [|On|] with 0.
  generalize (phi_bounded j)(phi_bounded i); intros.
  case_eq [|j|]; intros.
  simpl; intros.
  generalize (Zabs_spec [|i|]); omega.
  simpl.
  rewrite IHn, H1; f_equal.
  rewrite spec_mod, H1; auto.
  rewrite H1; compute; auto.
  rewrite H1 in H; destruct H as [H _]; compute in H; elim H; auto.
 Qed.

 Lemma spec_gcd : forall a b, Zis_gcd [|a|] [|b|] [|gcd31 a b|].
 Proof.
 intros.
 rewrite phi_gcd.
 apply Zis_gcd_sym.
 apply Zgcdn_is_gcd.
 unfold Zgcd_bound.
 generalize (phi_bounded b).
 destruct [|b|].
 unfold size; auto with zarith.
 intros (_,H).
 cut (Psize p <= size)%nat; [ omega | rewrite <- Zpower2_Psize; auto].
 intros (H,_); compute in H; elim H; auto.
 Qed.

 Lemma iter_int31_iter_nat : forall A f i a,
  iter_int31 i A f a = iter_nat (Zabs_nat [|i|]) A f a.
 Proof.
 intros.
 unfold iter_int31.
 rewrite <- recrbis_equiv; auto; unfold recrbis.
 rewrite <- phibis_aux_equiv.

 revert i a; induction size.
 simpl; auto.
 simpl; intros.
 case_eq (firstr i); intros H; rewrite 2 IHn;
  unfold phibis_aux; simpl; rewrite H; fold (phibis_aux n (shiftr i));
  generalize (phibis_aux_pos n (shiftr i)); intros;
  set (z := phibis_aux n (shiftr i)) in *; clearbody z;
  rewrite <- iter_nat_plus.

 f_equal.
 rewrite Zdouble_mult, Zmult_comm, <- Zplus_diag_eq_mult_2.
 symmetry; apply Zabs_nat_Zplus; auto with zarith.

 change (iter_nat (S (Zabs_nat z + Zabs_nat z)) A f a =
         iter_nat (Zabs_nat (Zdouble_plus_one z)) A f a); f_equal.
 rewrite Zdouble_plus_one_mult, Zmult_comm, <- Zplus_diag_eq_mult_2.
 rewrite Zabs_nat_Zplus; auto with zarith.
 rewrite Zabs_nat_Zplus; auto with zarith.
 change (Zabs_nat 1) with 1%nat; omega.
 Qed.

 Fixpoint addmuldiv31_alt n i j :=
  match n with
    | O => i
    | S n => addmuldiv31_alt n (sneakl (firstl j) i) (shiftl j)
  end.

 Lemma addmuldiv31_equiv : forall p x y,
  addmuldiv31 p x y = addmuldiv31_alt (Zabs_nat [|p|]) x y.
 Proof.
 intros.
 unfold addmuldiv31.
 rewrite iter_int31_iter_nat.
 set (n:=Zabs_nat [|p|]); clearbody n; clear p.
 revert x y; induction n.
 simpl; auto.
 intros.
 simpl addmuldiv31_alt.
 replace (S n) with (n+1)%nat by (rewrite plus_comm; auto).
 rewrite iter_nat_plus; simpl; auto.
 Qed.

 Lemma spec_add_mul_div : forall x y p, [|p|] <= Zpos 31 ->
   [| addmuldiv31 p x y |] =
   ([|x|] * (2 ^ [|p|]) + [|y|] / (2 ^ ((Zpos 31) - [|p|]))) mod wB.
 Proof.
 intros.
 rewrite addmuldiv31_equiv.
 assert ([|p|] = Z_of_nat (Zabs_nat [|p|])).
  rewrite inj_Zabs_nat; symmetry; apply Zabs_eq.
  destruct (phi_bounded p); auto.
 rewrite H0; rewrite H0 in H; clear H0; rewrite Zabs_nat_Z_of_nat.
 set (n := Zabs_nat [|p|]) in *; clearbody n.
 assert (n <= 31)%nat.
  rewrite inj_le_iff; auto with zarith.
 clear p H; revert x y.

 induction n.
 simpl; intros.
 change (Zpower_pos 2 31) with (2^31).
 rewrite Zmult_1_r.
 replace ([|y|] / 2^31) with 0.
 rewrite Zplus_0_r.
 symmetry; apply Zmod_small; apply phi_bounded.
 symmetry; apply Zdiv_small; apply phi_bounded.

 simpl addmuldiv31_alt; intros.
 rewrite IHn; [ | omega ].
 case_eq (firstl y); intros.

 rewrite phi_twice, Zdouble_mult.
 rewrite phi_twice_firstl; auto.
 change (Zdouble [|y|]) with (2*[|y|]).
 rewrite inj_S, Zpower_Zsucc; auto with zarith.
 rewrite Zplus_mod; rewrite Zmult_mod_idemp_l; rewrite <- Zplus_mod.
 f_equal.
 apply Zplus_eq_compat.
 ring.
 replace (31-Z_of_nat n) with (Zsucc(31-Zsucc(Z_of_nat n))) by ring.
 rewrite Zpower_Zsucc, <- Zdiv_Zdiv; auto with zarith.
 rewrite Zmult_comm, Z_div_mult; auto with zarith.

 rewrite phi_twice_plus_one, Zdouble_plus_one_mult.
 rewrite phi_twice; auto.
 change (Zdouble [|y|]) with (2*[|y|]).
 rewrite inj_S, Zpower_Zsucc; auto with zarith.
 rewrite Zplus_mod; rewrite Zmult_mod_idemp_l; rewrite <- Zplus_mod.
 rewrite Zmult_plus_distr_l, Zmult_1_l, <- Zplus_assoc.
 f_equal.
 apply Zplus_eq_compat.
 ring.
 assert ((2*[|y|]) mod wB = 2*[|y|] - wB).
  clear - H. symmetry. apply Zmod_unique with 1; [ | ring ].
  generalize (phi_lowerbound  _ H) (phi_bounded y).
  set (wB' := 2^Z_of_nat (pred size)).
  replace wB with (2*wB'); [ omega | ].
  unfold wB'. rewrite <- Zpower_Zsucc, <- inj_S by (auto with zarith).
  f_equal.
 rewrite H1.
 replace wB with (2^(Z_of_nat n)*2^(31-Z_of_nat n)) by
  (rewrite <- Zpower_exp; auto with zarith; f_equal; unfold size; ring).
 unfold Zminus; rewrite Zopp_mult_distr_l.
 rewrite Z_div_plus; auto with zarith.
 ring_simplify.
 replace (31+-Z_of_nat n) with (Zsucc(31-Zsucc(Z_of_nat n))) by ring.
 rewrite Zpower_Zsucc, <- Zdiv_Zdiv; auto with zarith.
 rewrite Zmult_comm, Z_div_mult; auto with zarith.
 Qed.

 Let w_pos_mod     := int31_op.(znz_pos_mod).

 Lemma spec_pos_mod : forall w p,
       [|w_pos_mod p w|] = [|w|] mod (2 ^ [|p|]).
 Proof.
 unfold w_pos_mod, znz_pos_mod, int31_op, compare31.
 change [|31|] with 31%Z.
 assert (forall w p, 31<=p -> [|w|] = [|w|] mod 2^p).
  intros.
  generalize (phi_bounded w).
  symmetry; apply Zmod_small.
  split; auto with zarith.
  apply Zlt_le_trans with wB; auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
 intros.
 case_eq ([|p|] ?= 31); intros;
  [ apply H; rewrite (Zcompare_Eq_eq _ _ H0); auto with zarith | |
    apply H; change ([|p|]>31)%Z in H0; auto with zarith ].
 change ([|p|]<31) in H0.
 rewrite spec_add_mul_div by auto with zarith.
 change [|0|] with 0%Z; rewrite Zmult_0_l, Zplus_0_l.
 generalize (phi_bounded p)(phi_bounded w); intros.
 assert (31-[|p|]<wB).
  apply Zle_lt_trans with 31%Z; auto with zarith.
  compute; auto.
 assert ([|31-p|]=31-[|p|]).
  unfold sub31; rewrite phi_phi_inv.
  change [|31|] with 31%Z.
  apply Zmod_small; auto with zarith.
 rewrite spec_add_mul_div by (rewrite H4; auto with zarith).
 change [|0|] with 0%Z; rewrite Zdiv_0_l, Zplus_0_r.
 rewrite H4.
 apply shift_unshift_mod_2; auto with zarith.
 Qed.


 (** Shift operations *)

 Lemma spec_head00:  forall x, [|x|] = 0 -> [|head031 x|] = Zpos 31.
 Proof.
  intros.
  generalize (phi_inv_phi x).
  rewrite H; simpl.
  intros H'; rewrite <- H'.
  simpl; auto.
 Qed.

 Fixpoint head031_alt n x :=
  match n with
    | O => 0%nat
    | S n => match firstl x with
               | D0 => S (head031_alt n (shiftl x))
               | D1 => 0%nat
             end
  end.

 Lemma head031_equiv :
   forall x, [|head031 x|] = Z_of_nat (head031_alt size x).
 Proof.
 intros.
 case_eq (iszero x); intros.
 rewrite (iszero_eq0 _ H).
 simpl; auto.

 unfold head031, recl.
 change On with (phi_inv (Z_of_nat (31-size))).
 replace (head031_alt size x) with
   (head031_alt size x + (31 - size))%nat by (apply plus_0_r; auto).
 assert (size <= 31)%nat by auto with arith.

 revert x H; induction size; intros.
 simpl; auto.
 unfold recl_aux; fold recl_aux.
 unfold head031_alt; fold head031_alt.
 rewrite H.
 assert ([|phi_inv (Z_of_nat (31-S n))|] = Z_of_nat (31 - S n)).
  rewrite phi_phi_inv.
  apply Zmod_small.
  split.
  change 0 with (Z_of_nat O); apply inj_le; omega.
  apply Zle_lt_trans with (Z_of_nat 31).
  apply inj_le; omega.
  compute; auto.
 case_eq (firstl x); intros; auto.
 rewrite plus_Sn_m, plus_n_Sm.
 replace (S (31 - S n)) with (31 - n)%nat by omega.
 rewrite <- IHn; [ | omega | ].
 f_equal; f_equal.
 unfold add31.
 rewrite H1.
 f_equal.
 change [|In|] with 1.
 replace (31-n)%nat with (S (31 - S n))%nat by omega.
 rewrite inj_S; ring.

 clear - H H2.
 rewrite (sneakr_shiftl x) in H.
 rewrite H2 in H.
 case_eq (iszero (shiftl x)); intros; auto.
 rewrite (iszero_eq0 _ H0) in H; discriminate.
 Qed.

 Lemma phi_nz : forall x, 0 < [|x|] <-> x <> 0%int31.
 Proof.
 split; intros.
 red; intro; subst x; discriminate.
 assert ([|x|]<>0%Z).
 contradict H.
 rewrite <- (phi_inv_phi x); rewrite H; auto.
 generalize (phi_bounded x); auto with zarith.
 Qed.

 Lemma spec_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ ([|head031 x|]) * [|x|] < wB.
 Proof.
 intros.
 rewrite head031_equiv.
 assert (nshiftl size x = 0%int31).
  apply nshiftl_size.
 revert x H H0.
 unfold size at 2 5.
 induction size.
 simpl Z_of_nat.
 intros.
 compute in H0; rewrite H0 in H; discriminate.

 intros.
 simpl head031_alt.
 case_eq (firstl x); intros.
 rewrite (inj_S (head031_alt n (shiftl x))), Zpower_Zsucc; auto with zarith.
 rewrite <- Zmult_assoc, Zmult_comm, <- Zmult_assoc, <-(Zmult_comm 2).
 rewrite <- Zdouble_mult, <- (phi_twice_firstl _ H1).
 apply IHn.

 rewrite phi_nz; rewrite phi_nz in H; contradict H.
 change twice with shiftl in H.
 rewrite (sneakr_shiftl x), H1, H; auto.

 rewrite <- nshiftl_S_tail; auto.

 change (2^(Z_of_nat 0)) with 1; rewrite Zmult_1_l.
 generalize (phi_bounded x); unfold size; split; auto with zarith.
 change (2^(Z_of_nat 31)/2) with (2^(Z_of_nat (pred size))).
 apply phi_lowerbound; auto.
 Qed.

 Lemma spec_tail00:  forall x, [|x|] = 0 -> [|tail031 x|] = Zpos 31.
 Proof.
  intros.
  generalize (phi_inv_phi x).
  rewrite H; simpl.
  intros H'; rewrite <- H'.
  simpl; auto.
 Qed.

 Fixpoint tail031_alt n x :=
  match n with
    | O => 0%nat
    | S n => match firstr x with
               | D0 => S (tail031_alt n (shiftr x))
               | D1 => 0%nat
             end
  end.

 Lemma tail031_equiv :
   forall x, [|tail031 x|] = Z_of_nat (tail031_alt size x).
 Proof.
 intros.
 case_eq (iszero x); intros.
 rewrite (iszero_eq0 _ H).
 simpl; auto.

 unfold tail031, recr.
 change On with (phi_inv (Z_of_nat (31-size))).
 replace (tail031_alt size x) with
   (tail031_alt size x + (31 - size))%nat by (apply plus_0_r; auto).
 assert (size <= 31)%nat by auto with arith.

 revert x H; induction size; intros.
 simpl; auto.
 unfold recr_aux; fold recr_aux.
 unfold tail031_alt; fold tail031_alt.
 rewrite H.
 assert ([|phi_inv (Z_of_nat (31-S n))|] = Z_of_nat (31 - S n)).
  rewrite phi_phi_inv.
  apply Zmod_small.
  split.
  change 0 with (Z_of_nat O); apply inj_le; omega.
  apply Zle_lt_trans with (Z_of_nat 31).
  apply inj_le; omega.
  compute; auto.
 case_eq (firstr x); intros; auto.
 rewrite plus_Sn_m, plus_n_Sm.
 replace (S (31 - S n)) with (31 - n)%nat by omega.
 rewrite <- IHn; [ | omega | ].
 f_equal; f_equal.
 unfold add31.
 rewrite H1.
 f_equal.
 change [|In|] with 1.
 replace (31-n)%nat with (S (31 - S n))%nat by omega.
 rewrite inj_S; ring.

 clear - H H2.
 rewrite (sneakl_shiftr x) in H.
 rewrite H2 in H.
 case_eq (iszero (shiftr x)); intros; auto.
 rewrite (iszero_eq0 _ H0) in H; discriminate.
 Qed.

 Lemma spec_tail0  : forall x, 0 < [|x|] ->
         exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|tail031 x|]).
 Proof.
 intros.
 rewrite tail031_equiv.
 assert (nshiftr size x = 0%int31).
  apply nshiftr_size.
 revert x H H0.
 induction size.
 simpl Z_of_nat.
 intros.
 compute in H0; rewrite H0 in H; discriminate.

 intros.
 simpl tail031_alt.
 case_eq (firstr x); intros.
 rewrite (inj_S (tail031_alt n (shiftr x))), Zpower_Zsucc; auto with zarith.
 destruct (IHn (shiftr x)) as (y & Hy1 & Hy2).

 rewrite phi_nz; rewrite phi_nz in H; contradict H.
 rewrite (sneakl_shiftr x), H1, H; auto.

 rewrite <- nshiftr_S_tail; auto.

 exists y; split; auto.
 rewrite phi_eqn1; auto.
 rewrite Zdouble_mult, Hy2; ring.

 exists [|shiftr x|].
 split.
 generalize (phi_bounded (shiftr x)); auto with zarith.
 rewrite phi_eqn2; auto.
 rewrite Zdouble_plus_one_mult; simpl; ring.
 Qed.

 (* Sqrt *)

 (* Direct transcription of an old proof
     of a fortran program in boyer-moore *)

 Lemma quotient_by_2 a: a - 1 <= (a/2) + (a/2).
 Proof.
 case (Z_mod_lt a 2); auto with zarith.
 intros H1; rewrite Zmod_eq_full; auto with zarith.
 Qed.

 Lemma sqrt_main_trick j k: 0 <= j -> 0 <= k ->
   (j * k) + j <= ((j + k)/2 + 1)  ^ 2.
 Proof.
 intros Hj; generalize Hj k; pattern j; apply natlike_ind;
   auto; clear k j Hj.
 intros _ k Hk; repeat rewrite Zplus_0_l.
 apply  Zmult_le_0_compat; generalize (Z_div_pos k 2); auto with zarith.
 intros j Hj Hrec _ k Hk; pattern k; apply natlike_ind; auto; clear k Hk.
 rewrite Zmult_0_r, Zplus_0_r, Zplus_0_l.
 generalize (sqr_pos (Zsucc j / 2)) (quotient_by_2 (Zsucc j));
   unfold Zsucc.
 rewrite Zpower_2, Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
 auto with zarith.
 intros k Hk _.
 replace ((Zsucc j + Zsucc k) / 2) with ((j + k)/2 + 1).
 generalize (Hrec Hj k Hk) (quotient_by_2 (j + k)).
 unfold Zsucc; repeat rewrite Zpower_2;
   repeat rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
 repeat rewrite Zmult_1_l; repeat rewrite Zmult_1_r.
 auto with zarith.
 rewrite Zplus_comm, <- Z_div_plus_full_l; auto with zarith.
 apply f_equal2 with (f := Zdiv); auto with zarith.
 Qed.

 Lemma sqrt_main i j: 0 <= i -> 0 < j -> i < ((j + (i/j))/2 + 1) ^ 2.
 Proof.
 intros Hi Hj.
 assert (Hij: 0 <= i/j) by (apply Z_div_pos; auto with zarith).
 apply Zlt_le_trans with (2 := sqrt_main_trick _ _ (Zlt_le_weak _ _ Hj) Hij).
 pattern i at 1; rewrite (Z_div_mod_eq i j); case (Z_mod_lt i j); auto with zarith.
 Qed.

 Lemma sqrt_init i: 1 < i -> i < (i/2 + 1) ^ 2.
 Proof.
 intros Hi.
 assert (H1: 0 <= i - 2) by auto with zarith.
 assert (H2: 1 <= (i / 2) ^ 2); auto with zarith.
   replace i with (1* 2 + (i - 2)); auto with zarith.
   rewrite Zpower_2, Z_div_plus_full_l; auto with zarith.
   generalize (sqr_pos ((i - 2)/ 2)) (Z_div_pos (i - 2) 2).
   rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
   auto with zarith.
 generalize (quotient_by_2 i).
 rewrite Zpower_2 in H2 |- *;
   repeat (rewrite Zmult_plus_distr_l ||
           rewrite Zmult_plus_distr_r ||
           rewrite Zmult_1_l || rewrite Zmult_1_r).
   auto with zarith.
 Qed.

 Lemma sqrt_test_true i j: 0 <= i -> 0 < j -> i/j >= j -> j ^ 2 <= i.
 Proof.
 intros Hi Hj Hd; rewrite Zpower_2.
 apply Zle_trans with (j * (i/j)); auto with zarith.
 apply Z_mult_div_ge; auto with zarith.
 Qed.

 Lemma sqrt_test_false i j: 0 <= i -> 0 < j -> i/j < j ->  (j + (i/j))/2 < j.
 Proof.
 intros Hi Hj H; case (Zle_or_lt j ((j + (i/j))/2)); auto.
 intros H1; contradict H; apply Zle_not_lt.
 assert (2 * j <= j + (i/j)); auto with zarith.
 apply Zle_trans with (2 * ((j + (i/j))/2)); auto with zarith.
 apply Z_mult_div_ge; auto with zarith.
 Qed.

 (* George's trick *)
 Inductive ZcompareSpec (i j: Z): comparison -> Prop :=
   ZcompareSpecEq: i = j -> ZcompareSpec i j Eq
 | ZcompareSpecLt: i < j -> ZcompareSpec i j Lt
 | ZcompareSpecGt: j < i -> ZcompareSpec i j Gt.

 Lemma Zcompare_spec i j: ZcompareSpec i j (i ?= j).
 Proof.
 case_eq (Zcompare i j); intros H.
 apply ZcompareSpecEq; apply Zcompare_Eq_eq; auto.
 apply ZcompareSpecLt; auto.
 apply ZcompareSpecGt; apply Zgt_lt; auto.
 Qed.

 Lemma sqrt31_step_def rec i j:
   sqrt31_step rec i j =
   match (fst (i/j) ?= j)%int31 with
     Lt => rec i (fst ((j + fst(i/j))/2))%int31
   | _ =>  j
   end.
 Proof.
 unfold sqrt31_step; case div31; intros.
 simpl; case compare31; auto.
 Qed.

 Lemma div31_phi i j: 0 < [|j|] -> [|fst (i/j)%int31|] = [|i|]/[|j|].
 intros Hj; generalize (spec_div i j Hj).
 case div31; intros q r; simpl fst.
 intros (H1,H2); apply Zdiv_unique with [|r|]; auto with zarith.
 rewrite H1; ring.
 Qed.

 Lemma sqrt31_step_correct rec i j:
  0 < [|i|] -> 0 < [|j|] -> [|i|] < ([|j|] + 1) ^ 2 ->
   2 * [|j|] < wB ->
  (forall j1 : int31,
    0 < [|j1|] < [|j|] -> [|i|] < ([|j1|] + 1) ^ 2 ->
    [|rec i j1|] ^ 2 <= [|i|] < ([|rec i j1|] + 1) ^ 2) ->
  [|sqrt31_step rec i j|] ^ 2 <= [|i|] < ([|sqrt31_step rec i j|] + 1) ^ 2.
 Proof.
 assert (Hp2: 0 < [|2|]) by exact (refl_equal Lt).
 intros Hi Hj Hij H31 Hrec; rewrite sqrt31_step_def.
 generalize (spec_compare (fst (i/j)%int31) j); case compare31;
   rewrite div31_phi; auto; intros Hc;
   try (split; auto; apply sqrt_test_true; auto with zarith; fail).
 apply Hrec; repeat rewrite div31_phi; auto with zarith.
 replace [|(j + fst (i / j)%int31)|] with ([|j|] + [|i|] / [|j|]).
 split.
 case (Zle_lt_or_eq 1 [|j|]); auto with zarith; intros Hj1.
 replace ([|j|] + [|i|]/[|j|]) with
        (1 * 2 + (([|j|] - 2) + [|i|] / [|j|])); try ring.
 rewrite Z_div_plus_full_l; auto with zarith.
 assert (0 <= [|i|]/ [|j|]) by (apply Z_div_pos; auto with zarith).
 assert (0 <= ([|j|] - 2 + [|i|] / [|j|]) / [|2|]) ; auto with zarith.
 rewrite <- Hj1, Zdiv_1_r.
 replace (1 + [|i|])%Z with (1 * 2 + ([|i|] - 1))%Z; try ring.
 rewrite Z_div_plus_full_l; auto with zarith.
 assert (0 <= ([|i|] - 1) /2)%Z by (apply Z_div_pos; auto with zarith).
 change ([|2|]) with 2%Z; auto with zarith.
 apply sqrt_test_false; auto with zarith.
 rewrite spec_add, div31_phi; auto.
 apply sym_equal; apply Zmod_small.
 split; auto with zarith.
 replace [|j + fst (i / j)%int31|] with ([|j|] + [|i|] / [|j|]).
 apply sqrt_main; auto with zarith.
 rewrite spec_add, div31_phi; auto.
 apply sym_equal; apply Zmod_small.
 split; auto with zarith.
 Qed.

 Lemma iter31_sqrt_correct n rec i j: 0 < [|i|] -> 0 < [|j|] ->
  [|i|] < ([|j|] + 1) ^ 2 -> 2 * [|j|] < 2 ^ (Z_of_nat size) ->
  (forall j1, 0 < [|j1|] -> 2^(Z_of_nat n) + [|j1|] <= [|j|] ->
      [|i|] < ([|j1|] + 1) ^ 2 -> 2 * [|j1|] < 2 ^ (Z_of_nat size) ->
       [|rec i j1|] ^ 2 <= [|i|] < ([|rec i j1|] + 1) ^ 2) ->
  [|iter31_sqrt n rec i j|] ^ 2 <= [|i|] < ([|iter31_sqrt n rec i j|] + 1) ^ 2.
 Proof.
 revert rec i j; elim n; unfold iter31_sqrt; fold iter31_sqrt; clear n.
 intros rec i j Hi Hj Hij H31 Hrec; apply sqrt31_step_correct; auto with zarith.
 intros; apply Hrec; auto with zarith.
 rewrite Zpower_0_r; auto with zarith.
 intros n Hrec rec i j Hi Hj Hij H31 HHrec.
 apply sqrt31_step_correct; auto.
 intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
 intros j2 Hj2 H2j2 Hjp2 Hj31; apply Hrec; auto with zarith.
 intros j3 Hj3 Hpj3.
 apply HHrec; auto.
 rewrite inj_S, Zpower_Zsucc.
 apply Zle_trans with (2 ^Z_of_nat n + [|j2|]); auto with zarith.
 apply Zle_0_nat.
 Qed.

 Lemma spec_sqrt : forall x,
       [|sqrt31 x|] ^ 2 <= [|x|] < ([|sqrt31 x|] + 1) ^ 2.
 Proof.
 intros i; unfold sqrt31.
 generalize (spec_compare 1 i); case compare31; change [|1|] with 1;
   intros Hi; auto with zarith.
 repeat rewrite Zpower_2; auto with zarith.
 apply iter31_sqrt_correct; auto with zarith.
  rewrite div31_phi; change ([|2|]) with 2;  auto with zarith.
  replace ([|i|]) with (1 * 2 + ([|i|] - 2))%Z; try ring.
  assert (0 <= ([|i|] - 2)/2)%Z by (apply Z_div_pos; auto with zarith).
  rewrite Z_div_plus_full_l; auto with zarith.
  rewrite div31_phi; change ([|2|]) with 2; auto with zarith.
  apply sqrt_init; auto.
 rewrite div31_phi; change ([|2|]) with 2; auto with zarith.
 apply Zle_lt_trans with ([|i|]).
 apply Z_mult_div_ge; auto with zarith.
 case (phi_bounded i); auto.
 intros j2 H1 H2; contradict H2; apply Zlt_not_le.
 rewrite div31_phi; change ([|2|]) with 2; auto with zarith.
 apply Zle_lt_trans with ([|i|]); auto with zarith.
 assert (0 <= [|i|]/2)%Z by (apply Z_div_pos; auto with zarith).
 apply Zle_trans with (2 * ([|i|]/2)); auto with zarith.
 apply Z_mult_div_ge; auto with zarith.
 case (phi_bounded i); unfold size; auto with zarith.
 change [|0|] with 0; auto with zarith.
 case (phi_bounded i); repeat rewrite Zpower_2; auto with zarith.
 Qed.

 Lemma sqrt312_step_def rec ih il j:
   sqrt312_step rec ih il j =
   match (ih ?= j)%int31 with
      Eq => j
    | Gt => j
    | _ =>
       match (fst (div3121 ih il j) ?= j)%int31 with
         Lt => let m := match j +c fst (div3121 ih il j) with
                       C0 m1 => fst (m1/2)%int31
                     | C1 m1 => (fst (m1/2) + v30)%int31
                     end in rec ih il m
       | _ =>  j
       end
   end.
 Proof.
 unfold sqrt312_step; case div3121; intros.
 simpl; case compare31; auto.
 Qed.

 Lemma sqrt312_lower_bound ih il j:
   phi2 ih  il  < ([|j|] + 1) ^ 2 -> [|ih|] <= [|j|].
 Proof.
 intros H1.
 case (phi_bounded j); intros Hbj _.
 case (phi_bounded il); intros Hbil _.
 case (phi_bounded ih); intros Hbih Hbih1.
 assert (([|ih|] < [|j|] + 1)%Z); auto with zarith.
 apply Zlt_square_simpl; auto with zarith.
 repeat rewrite <-Zpower_2; apply Zle_lt_trans with (2 := H1).
 apply Zle_trans with ([|ih|] * base)%Z; unfold phi2, base;
  try rewrite Zpower_2; auto with zarith.
 Qed.

 Lemma div312_phi ih il j: (2^30 <= [|j|] -> [|ih|] < [|j|] ->
  [|fst (div3121 ih il j)|] = phi2 ih il/[|j|])%Z.
 Proof.
 intros Hj Hj1.
 generalize (spec_div21 ih il j Hj Hj1).
 case div3121; intros q r (Hq, Hr).
 apply Zdiv_unique with (phi r); auto with zarith.
 simpl fst; apply trans_equal with (1 := Hq); ring.
 Qed.

 Lemma sqrt312_step_correct rec ih il j:
  2 ^ 29 <= [|ih|] -> 0 < [|j|] -> phi2 ih il < ([|j|] + 1) ^ 2 ->
  (forall j1, 0 < [|j1|] < [|j|] ->  phi2 ih il < ([|j1|] + 1) ^ 2 ->
     [|rec ih il j1|] ^ 2 <= phi2 ih il < ([|rec ih il j1|] + 1) ^ 2) ->
  [|sqrt312_step rec ih il  j|] ^ 2 <= phi2 ih il
      < ([|sqrt312_step rec ih il j|] + 1) ^  2.
 Proof.
 assert (Hp2: (0 < [|2|])%Z) by exact (refl_equal Lt).
 intros Hih Hj Hij Hrec; rewrite sqrt312_step_def.
 assert (H1: ([|ih|] <= [|j|])%Z) by (apply sqrt312_lower_bound with il; auto).
 case (phi_bounded ih); intros Hih1 _.
 case (phi_bounded il); intros Hil1 _.
 case (phi_bounded j); intros _ Hj1.
 assert (Hp3: (0 < phi2 ih il)).
 unfold phi2; apply Zlt_le_trans with ([|ih|] * base)%Z; auto with zarith.
 apply Zmult_lt_0_compat; auto with zarith.
 apply Zlt_le_trans with (2:= Hih); auto with zarith.
 generalize (spec_compare ih j); case compare31; intros Hc1.
 split; auto.
 apply sqrt_test_true; auto.
 unfold phi2, base; auto with zarith.
 unfold phi2; rewrite Hc1.
 assert (0 <= [|il|]/[|j|]) by (apply Z_div_pos; auto with zarith).
 rewrite Zmult_comm, Z_div_plus_full_l; unfold base; auto with zarith.
 unfold Zpower, Zpower_pos in Hj1; simpl in Hj1; auto with zarith.
 case (Zle_or_lt (2 ^ 30) [|j|]); intros Hjj.
 generalize (spec_compare (fst (div3121 ih il j)) j); case compare31;
  rewrite div312_phi; auto; intros Hc;
  try (split; auto; apply sqrt_test_true; auto with zarith; fail).
 apply Hrec.
 assert (Hf1: 0 <= phi2 ih il/ [|j|]) by (apply Z_div_pos; auto with zarith).
 case (Zle_lt_or_eq 1 ([|j|])); auto with zarith; intros Hf2.
 2: contradict Hc; apply Zle_not_lt; rewrite <- Hf2, Zdiv_1_r; auto with zarith.
 assert (Hf3: 0 < ([|j|] + phi2 ih il / [|j|]) / 2).
 replace ([|j|] + phi2 ih il/ [|j|])%Z with
        (1 * 2 + (([|j|] - 2) + phi2 ih il / [|j|])); try ring.
 rewrite Z_div_plus_full_l; auto with zarith.
 assert (0 <= ([|j|] - 2 + phi2 ih il / [|j|]) / 2) ; auto with zarith.
 assert (Hf4: ([|j|] + phi2 ih il / [|j|]) / 2 < [|j|]).
 apply sqrt_test_false; auto with zarith.
 generalize (spec_add_c j (fst (div3121 ih il j))).
 unfold interp_carry;  case add31c; intros r;
  rewrite div312_phi; auto with zarith.
 rewrite div31_phi; change [|2|] with 2%Z; auto with zarith.
 intros HH; rewrite HH; clear HH; auto with zarith.
 rewrite spec_add, div31_phi; change [|2|] with 2%Z; auto.
 rewrite Zmult_1_l; intros HH.
 rewrite Zplus_comm, <- Z_div_plus_full_l; auto with zarith.
 change (phi v30 * 2) with (2 ^ Z_of_nat size).
 rewrite HH, Zmod_small; auto with zarith.
 replace (phi
    match j +c fst (div3121 ih il j) with
    | C0 m1 => fst (m1 / 2)%int31
    | C1 m1 => fst (m1 / 2)%int31 + v30
    end) with ((([|j|] + (phi2 ih il)/([|j|]))/2)).
 apply sqrt_main; auto with zarith.
 generalize (spec_add_c j (fst (div3121 ih il j))).
 unfold interp_carry;  case add31c; intros r;
  rewrite div312_phi; auto with zarith.
 rewrite div31_phi; auto with zarith.
 intros HH; rewrite HH; auto with zarith.
 intros HH; rewrite <- HH.
 change (1 * 2 ^ Z_of_nat size) with (phi (v30) * 2).
 rewrite Z_div_plus_full_l; auto with zarith.
 rewrite Zplus_comm.
 rewrite spec_add, Zmod_small.
 rewrite div31_phi; auto.
 split; auto with zarith.
 case (phi_bounded (fst (r/2)%int31));
   case (phi_bounded v30); auto with zarith.
 rewrite div31_phi; change (phi 2) with 2%Z; auto.
 change (2 ^Z_of_nat size) with (base/2 + phi v30).
 assert (phi r / 2 < base/2); auto with zarith.
 apply Zmult_gt_0_lt_reg_r with 2; auto with zarith.
 change (base/2 * 2) with base.
 apply Zle_lt_trans with (phi r).
 rewrite Zmult_comm; apply Z_mult_div_ge; auto with zarith.
 case (phi_bounded r); auto with zarith.
 contradict Hij; apply Zle_not_lt.
 assert ((1 + [|j|]) <= 2 ^ 30); auto with zarith.
 apply Zle_trans with ((2 ^ 30) * (2 ^ 30)); auto with zarith.
 assert (0 <= 1 + [|j|]); auto with zarith.
 apply Zmult_le_compat; auto with zarith.
 change ((2 ^ 30) * (2 ^ 30)) with ((2 ^ 29) * base).
 apply Zle_trans with ([|ih|] * base); auto with zarith.
 unfold phi2, base; auto with zarith.
 split; auto.
 apply sqrt_test_true; auto.
 unfold phi2, base; auto with zarith.
 apply Zle_ge; apply Zle_trans with (([|j|] * base)/[|j|]).
 rewrite Zmult_comm, Z_div_mult; auto with zarith.
 apply Zge_le; apply Z_div_ge; auto with zarith.
 Qed.

 Lemma iter312_sqrt_correct n rec ih il j:
  2^29 <= [|ih|] ->  0 < [|j|] -> phi2 ih il < ([|j|] + 1) ^ 2 ->
  (forall j1, 0 < [|j1|] -> 2^(Z_of_nat n) + [|j1|] <= [|j|] ->
      phi2 ih il < ([|j1|] + 1) ^ 2 ->
       [|rec ih il j1|] ^ 2 <= phi2 ih il < ([|rec ih il j1|] + 1) ^ 2)  ->
  [|iter312_sqrt n rec ih il j|] ^ 2 <= phi2 ih il
      < ([|iter312_sqrt n rec ih il j|] + 1) ^ 2.
 Proof.
 revert rec ih il j; elim n; unfold iter312_sqrt; fold iter312_sqrt; clear n.
 intros rec ih il j Hi Hj Hij Hrec; apply sqrt312_step_correct; auto with zarith.
 intros; apply Hrec; auto with zarith.
 rewrite Zpower_0_r; auto with zarith.
 intros n Hrec rec ih il j Hi Hj Hij HHrec.
 apply sqrt312_step_correct; auto.
 intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
 intros j2 Hj2 H2j2 Hjp2; apply Hrec; auto with zarith.
 intros j3 Hj3 Hpj3.
 apply HHrec; auto.
 rewrite inj_S, Zpower_Zsucc.
 apply Zle_trans with (2 ^Z_of_nat n + [|j2|])%Z; auto with zarith.
 apply Zle_0_nat.
 Qed.

 Lemma spec_sqrt2 : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := sqrt312 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
 Proof.
 intros ih il Hih; unfold sqrt312.
 change [||WW ih il||] with (phi2 ih il).
 assert (Hbin: forall s, s * s + 2* s + 1 = (s + 1) ^ 2) by
  (intros s; ring).
 assert (Hb: 0 <= base) by (red; intros HH; discriminate).
 assert (Hi2: phi2 ih il < (phi Tn + 1) ^ 2).
   change ((phi Tn + 1) ^ 2) with (2^62).
  apply Zle_lt_trans with ((2^31 -1) * base + (2^31 - 1)); auto with zarith.
  2: simpl; unfold Zpower_pos; simpl; auto with zarith.
  case (phi_bounded ih); case (phi_bounded il); intros H1 H2 H3 H4.
  unfold base, Zpower, Zpower_pos in H2,H4; simpl in H2,H4.
  unfold phi2,Zpower, Zpower_pos; simpl iter_pos; auto with zarith.
 case (iter312_sqrt_correct 31 (fun _ _ j => j) ih il Tn); auto with zarith.
 change [|Tn|] with 2147483647; auto with zarith.
 intros j1 _ HH; contradict HH.
 apply Zlt_not_le.
 change [|Tn|] with 2147483647; auto with zarith.
 change (2 ^ Z_of_nat 31) with 2147483648; auto with zarith.
 case (phi_bounded j1); auto with zarith.
 set (s := iter312_sqrt 31 (fun _ _ j : int31 => j) ih il Tn).
 intros Hs1 Hs2.
 generalize (spec_mul_c s s); case mul31c.
 simpl zn2z_to_Z; intros HH.
 assert ([|s|] = 0).
 case (Zmult_integral _ _ (sym_equal HH)); auto.
 contradict Hs2; apply Zle_not_lt; rewrite H.
 change ((0 + 1) ^ 2) with 1.
 apply Zle_trans with (2 ^ Z_of_nat size / 4 * base).
 simpl; auto with zarith.
 apply Zle_trans with ([|ih|] * base); auto with zarith.
 unfold phi2; case (phi_bounded il); auto with zarith.
 intros ih1 il1.
 change [||WW ih1 il1||] with (phi2 ih1 il1).
 intros Hihl1.
 generalize (spec_sub_c il il1).
 case sub31c; intros il2 Hil2.
 simpl interp_carry in Hil2.
 generalize (spec_compare ih ih1); case compare31.
 unfold interp_carry.
 intros H1; split.
 rewrite Zpower_2, <- Hihl1.
 unfold phi2; ring[Hil2 H1].
 replace [|il2|] with (phi2 ih il - phi2 ih1 il1).
 rewrite Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold phi2; rewrite H1, Hil2; ring.
 unfold interp_carry.
 intros H1; contradict Hs1.
 apply Zlt_not_le; rewrite Zpower_2, <-Hihl1.
 unfold phi2.
 case (phi_bounded il); intros _ H2.
 apply Zlt_le_trans with (([|ih|] + 1) * base + 0).
 rewrite Zmult_plus_distr_l, Zplus_0_r; auto with zarith.
 case (phi_bounded il1); intros H3 _.
 apply Zplus_le_compat; auto with zarith.
 unfold interp_carry; change (1 * 2 ^ Z_of_nat size) with base.
 rewrite Zpower_2, <- Hihl1, Hil2.
 intros H1.
 case (Zle_lt_or_eq ([|ih1|] + 1) ([|ih|])); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with (phi2 ih1 il1 + 2 * [|s|] + 1).
 unfold phi2.
 case (phi_bounded il); intros Hpil _.
 assert (Hl1l: [|il1|] <= [|il|]).
  case (phi_bounded il2); rewrite Hil2; auto with zarith.
 assert ([|ih1|] * base + 2 * [|s|] + 1 <= [|ih|] * base); auto with zarith.
 case (phi_bounded s);  change (2 ^ Z_of_nat size) with base; intros _ Hps.
 case (phi_bounded ih1); intros Hpih1 _; auto with zarith.
 apply Zle_trans with (([|ih1|] + 2) * base); auto with zarith.
 rewrite Zmult_plus_distr_l.
 assert (2 * [|s|] + 1 <= 2 * base); auto with zarith.
 rewrite Hihl1, Hbin; auto.
 intros H2; split.
 unfold phi2; rewrite <- H2; ring.
 replace (base + ([|il|] - [|il1|])) with (phi2 ih il - ([|s|] * [|s|])).
 rewrite <-Hbin in Hs2; auto with zarith.
 rewrite <- Hihl1; unfold phi2; rewrite <- H2; ring.
 unfold interp_carry in Hil2 |- *.
 unfold interp_carry; change (1 * 2 ^ Z_of_nat size) with base.
 assert (Hsih: [|ih - 1|] = [|ih|] - 1).
  rewrite spec_sub, Zmod_small; auto; change [|1|] with 1.
  case (phi_bounded ih); intros H1 H2.
  generalize Hih; change (2 ^ Z_of_nat size / 4) with 536870912.
  split; auto with zarith.
 generalize (spec_compare (ih - 1) ih1); case compare31.
 rewrite Hsih.
 intros H1; split.
 rewrite Zpower_2, <- Hihl1.
 unfold phi2; rewrite <-H1.
 apply trans_equal with ([|ih|] * base + [|il1|] + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2.
 change (2 ^ Z_of_nat size) with base; ring.
 replace [|il2|] with (phi2 ih il - phi2 ih1 il1).
 rewrite Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold phi2.
 rewrite <-H1.
 ring_simplify.
 apply trans_equal with (base + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2.
 change (2 ^ Z_of_nat size) with base; ring.
 rewrite Hsih; intros H1.
 assert (He: [|ih|] = [|ih1|]).
   apply Zle_antisym; auto with zarith.
   case (Zle_or_lt [|ih1|] [|ih|]); auto; intros H2.
   contradict Hs1; apply Zlt_not_le; rewrite Zpower_2, <-Hihl1.
  unfold phi2.
  case (phi_bounded il); change (2 ^ Z_of_nat size) with base;
    intros _ Hpil1.
  apply Zlt_le_trans with (([|ih|] + 1) * base).
  rewrite Zmult_plus_distr_l, Zmult_1_l; auto with zarith.
  case (phi_bounded il1); intros Hpil2 _.
  apply Zle_trans with (([|ih1|]) * base); auto with zarith.
 rewrite Zpower_2, <-Hihl1; unfold phi2; rewrite <-He.
 contradict Hs1; apply Zlt_not_le; rewrite Zpower_2, <-Hihl1.
 unfold phi2; rewrite He.
 assert (phi il - phi il1 < 0); auto with zarith.
 rewrite <-Hil2.
 case (phi_bounded il2); auto with zarith.
 intros H1.
 rewrite Zpower_2, <-Hihl1.
 case (Zle_lt_or_eq ([|ih1|] + 2) [|ih|]); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with (phi2 ih1 il1 + 2 * [|s|] + 1).
 unfold phi2.
 assert ([|ih1|] * base + 2 * phi s + 1 <= [|ih|] * base + ([|il|] - [|il1|]));
  auto with zarith.
 rewrite <-Hil2.
 change (-1 * 2 ^ Z_of_nat size) with (-base).
 case (phi_bounded il2); intros Hpil2 _.
 apply Zle_trans with ([|ih|] * base + - base); auto with zarith.
 case (phi_bounded s);  change (2 ^ Z_of_nat size) with base; intros _ Hps.
 assert (2 * [|s|] + 1 <= 2 * base); auto with zarith.
 apply Zle_trans with ([|ih1|] * base + 2 * base); auto with zarith.
 assert (Hi: ([|ih1|] + 3) * base <= [|ih|] * base); auto with zarith.
 rewrite Zmult_plus_distr_l in Hi; auto with zarith.
 rewrite Hihl1, Hbin; auto.
 intros H2; unfold phi2; rewrite <-H2.
 split.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2.
 change (-1 * 2 ^ Z_of_nat size) with (-base); ring.
 replace (base + [|il2|]) with (phi2 ih il - phi2 ih1 il1).
 rewrite Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold phi2; rewrite <-H2.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2.
 change (-1 * 2 ^ Z_of_nat size) with (-base); ring.
 Qed.

 (** [iszero] *)

 Let w_eq0         := int31_op.(znz_eq0).

 Lemma spec_eq0 : forall x, w_eq0 x = true -> [|x|] = 0.
 Proof.
 clear; unfold w_eq0, znz_eq0; simpl.
 unfold compare31; simpl; intros.
 change [|0|] with 0 in H.
 apply Zcompare_Eq_eq.
 now destruct ([|x|] ?= 0).
 Qed.

 (* Even *)

 Let w_is_even     := int31_op.(znz_is_even).

 Lemma spec_is_even : forall x,
      if w_is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1.
 Proof.
 unfold w_is_even; simpl; intros.
 generalize (spec_div x 2).
 destruct (x/2)%int31 as (q,r); intros.
 unfold compare31.
 change [|2|] with 2 in H.
 change [|0|] with 0.
 destruct H; auto with zarith.
 replace ([|x|] mod 2) with [|r|].
 destruct H; auto with zarith.
 case_eq ([|r|] ?= 0)%Z; intros.
 apply Zcompare_Eq_eq; auto.
 change ([|r|] < 0)%Z in H; auto with zarith.
 change ([|r|] > 0)%Z in H; auto with zarith.
 apply Zmod_unique with [|q|]; auto with zarith.
 Qed.

 Definition int31_spec : znz_spec int31_op.
  split.
  exact phi_bounded.
  exact positive_to_int31_spec.
  exact spec_zdigits.
  exact spec_more_than_1_digit.

  exact spec_0.
  exact spec_1.
  exact spec_Bm1.

  exact spec_compare.
  exact spec_eq0.

  exact spec_opp_c.
  exact spec_opp.
  exact spec_opp_carry.

  exact spec_succ_c.
  exact spec_add_c.
  exact spec_add_carry_c.
  exact spec_succ.
  exact spec_add.
  exact spec_add_carry.

  exact spec_pred_c.
  exact spec_sub_c.
  exact spec_sub_carry_c.
  exact spec_pred.
  exact spec_sub.
  exact spec_sub_carry.

  exact spec_mul_c.
  exact spec_mul.
  exact spec_square_c.

  exact spec_div21.
  intros; apply spec_div; auto.
  exact spec_div.

  intros; unfold int31_op; simpl; apply spec_mod; auto.
  exact spec_mod.

  intros; apply spec_gcd; auto.
  exact spec_gcd.

  exact spec_head00.
  exact spec_head0.
  exact spec_tail00.
  exact spec_tail0.

  exact spec_add_mul_div.
  exact spec_pos_mod.

  exact spec_is_even.
  exact spec_sqrt2.
  exact spec_sqrt.
 Qed.

End Int31_Spec.


Module Int31Cyclic <: CyclicType.
  Definition w := int31.
  Definition w_op := int31_op.
  Definition w_spec := int31_spec.
End Int31Cyclic.
