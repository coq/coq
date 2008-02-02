(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * Finite sets library *)

(** This functor derives additional properties from [FSetInterface.S].
    Contrary to the functor in [FSetEqProperties] it uses 
    predicates over sets instead of sets operations, i.e.
    [In x s] instead of [mem x s=true], 
    [Equal s s'] instead of [equal s s'=true], etc. *)

Require Export FSetInterface. 
Require Import DecidableTypeEx FSetFacts FSetDecide.
Set Implicit Arguments.
Unset Strict Implicit.

Hint Unfold transpose compat_op compat_nat.
Hint Extern 1 (Setoid_Theory _ _) => constructor; congruence.

(** First, the properties that do not rely on the element ordering 
    are imported verbatim from FSetWeakProperties *)

Require FSetWeakProperties.

Module Properties (M:S).
  Module D := OT_as_DT M.E.
  Include FSetWeakProperties.Properties M D.
End Properties.

(** Now comes some properties specific to the element ordering, 
    invalid in FSetWeak. *)

Module OrdProperties (M:S).
  Module ME:=OrderedTypeFacts(M.E).
  Module Import P := Properties M.
  Import FM.
  Import M.E.
  Import M.

  (* First, a specialized version of SortA_equivlistA_eqlistA: *)
  Lemma sort_equivlistA_eqlistA : forall l l' : list elt,
   sort E.lt l -> sort E.lt l' -> equivlistA E.eq l l' -> eqlistA E.eq l l'.
  Proof.
  apply SortA_equivlistA_eqlistA; eauto.
  Qed.

  Definition gtb x y := match E.compare x y with GT _ => true | _ => false end.
  Definition leb x := fun y => negb (gtb x y).

  Definition elements_lt x s := List.filter (gtb x) (elements s).
  Definition elements_ge x s := List.filter (leb x) (elements s).

  Lemma gtb_1 : forall x y, gtb x y = true <-> E.lt y x.
  Proof.
   intros; unfold gtb; destruct (E.compare x y); intuition; try discriminate; ME.order.
  Qed.

  Lemma leb_1 : forall x y, leb x y = true <-> ~E.lt y x.
  Proof.
   intros; unfold leb, gtb; destruct (E.compare x y); intuition; try discriminate; ME.order.
  Qed.

  Lemma gtb_compat : forall x, compat_bool E.eq (gtb x).
  Proof.
   red; intros x a b H.
   generalize (gtb_1 x a)(gtb_1 x b); destruct (gtb x a); destruct (gtb x b); auto.
   intros.
   symmetry; rewrite H1.
   apply ME.eq_lt with a; auto.
   rewrite <- H0; auto.
   intros.
   rewrite H0.
   apply ME.eq_lt with b; auto.
   rewrite <- H1; auto.
  Qed.

  Lemma leb_compat : forall x, compat_bool E.eq (leb x).
  Proof.
   red; intros x a b H; unfold leb.
   f_equal; apply gtb_compat; auto.
  Qed.
  Hint Resolve gtb_compat leb_compat.

  Lemma elements_split : forall x s, 
   elements s = elements_lt x s ++ elements_ge x s.
  Proof.
  unfold elements_lt, elements_ge, leb; intros.
  eapply (@filter_split _ E.eq); eauto with set. ME.order. ME.order. ME.order.
  intros.
  rewrite gtb_1 in H.
  assert (~E.lt y x).
   unfold gtb in *; destruct (E.compare x y); intuition; try discriminate; ME.order.
  ME.order.
  Qed.

  Lemma elements_Add : forall s s' x, ~In x s -> Add x s s' -> 
    eqlistA E.eq (elements s') (elements_lt x s ++ x :: elements_ge x s). 
  Proof.
  intros; unfold elements_ge, elements_lt.
  apply sort_equivlistA_eqlistA; auto with set.
  apply (@SortA_app _ E.eq); auto.
  apply (@filter_sort _ E.eq); auto with set; eauto with set.
  constructor; auto.
  apply (@filter_sort _ E.eq); auto with set; eauto with set.
  rewrite ME.Inf_alt; auto; intros.
  apply (@filter_sort _ E.eq); auto with set; eauto with set.
  rewrite filter_InA in H1; auto; destruct H1.
  rewrite leb_1 in H2.
  rewrite <- elements_iff in H1.
  assert (~E.eq x y).
   contradict H; rewrite H; auto.
  ME.order.
  intros.
  rewrite filter_InA in H1; auto; destruct H1.
  rewrite gtb_1 in H3.
  inversion_clear H2.
  ME.order.
  rewrite filter_InA in H4; auto; destruct H4.
  rewrite leb_1 in H4.
  ME.order.
  red; intros a.
  rewrite InA_app_iff; rewrite InA_cons.
  do 2 (rewrite filter_InA; auto).
  do 2 rewrite <- elements_iff.
  rewrite leb_1; rewrite gtb_1.
  rewrite (H0 a); intuition.
  destruct (E.compare a x); intuition.
  right; right; split; auto.
  ME.order.
  Qed.

  Definition Above x s := forall y, In y s -> E.lt y x.
  Definition Below x s := forall y, In y s -> E.lt x y.

  Lemma elements_Add_Above : forall s s' x, 
   Above x s -> Add x s s' -> 
     eqlistA E.eq (elements s') (elements s ++ x::nil).
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with set.
  apply (@SortA_app _ E.eq); auto with set.
  intros.
  inversion_clear H2.
  rewrite <- elements_iff in H1.
  apply ME.lt_eq with x; auto.
  inversion H3.
  red; intros a.
  rewrite InA_app_iff; rewrite InA_cons; rewrite InA_nil.
  do 2 rewrite <- elements_iff; rewrite (H0 a); intuition.
  Qed.

  Lemma elements_Add_Below : forall s s' x, 
   Below x s -> Add x s s' -> 
     eqlistA E.eq (elements s') (x::elements s).
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with set.
  change (sort E.lt ((x::nil) ++ elements s)).
  apply (@SortA_app _ E.eq); auto with set.
  intros.
  inversion_clear H1.
  rewrite <- elements_iff in H2.
  apply ME.eq_lt with x; auto.
  inversion H3.
  red; intros a.
  rewrite InA_cons.
  do 2 rewrite <- elements_iff; rewrite (H0 a); intuition.
  Qed.

  (** Two other induction principles on sets: we can be more restrictive 
      on the element we add at each step.  *)

  Lemma set_induction_max :
   forall P : t -> Type,
   (forall s : t, Empty s -> P s) ->
   (forall s s', P s -> forall x, Above x s -> Add x s s' -> P s') ->
   forall s : t, P s.
  Proof.
  intros; remember (cardinal s) as n; revert s Heqn; induction n; intros; auto.
  case_eq (max_elt s); intros.
  apply X0 with (remove e s) e; auto with set.
  apply IHn.
  assert (S n = S (cardinal (remove e s))).
   rewrite Heqn; apply cardinal_2 with e; auto with set.
  inversion H0; auto.
  red; intros.
  rewrite remove_iff in H0; destruct H0.
  generalize (@max_elt_2 s e y H H0); ME.order.

  assert (H0:=max_elt_3 H).
  rewrite cardinal_Empty in H0; rewrite H0 in Heqn; inversion Heqn.
  Qed.

  Lemma set_induction_min :
   forall P : t -> Type,
   (forall s : t, Empty s -> P s) ->
   (forall s s', P s -> forall x, Below x s -> Add x s s' -> P s') ->
   forall s : t, P s.
  Proof.
  intros; remember (cardinal s) as n; revert s Heqn; induction n; intros; auto.
  case_eq (min_elt s); intros.
  apply X0 with (remove e s) e; auto with set.
  apply IHn.
  assert (S n = S (cardinal (remove e s))).
   rewrite Heqn; apply cardinal_2 with e; auto with set.
  inversion H0; auto.
  red; intros.
  rewrite remove_iff in H0; destruct H0.
  generalize (@min_elt_2 s e y H H0); ME.order.

  assert (H0:=min_elt_3 H).
  rewrite cardinal_Empty in H0; auto; rewrite H0 in Heqn; inversion Heqn.
  Qed.

  (** More properties of [fold] : behavior with respect to Above/Below *)

  Lemma fold_3 :
   forall s s' x (A : Set) (eqA : A -> A -> Prop)
     (st : Setoid_Theory A eqA) (i : A) (f : elt -> A -> A),
   compat_op E.eq eqA f ->
   Above x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
  Proof.
  intros.
  do 2 rewrite M.fold_1.
  do 2 rewrite <- fold_left_rev_right.
  change (f x (fold_right f i (rev (elements s)))) with
    (fold_right f i (rev (x::nil)++rev (elements s))).
  apply (@fold_right_eqlistA E.t E.eq A eqA st); auto.
  rewrite <- distr_rev.
  apply eqlistA_rev.
  apply elements_Add_Above; auto.
  Qed.

  Lemma fold_4 :
   forall s s' x (A : Set) (eqA : A -> A -> Prop)
     (st : Setoid_Theory A eqA) (i : A) (f : elt -> A -> A),
   compat_op E.eq eqA f ->
   Below x s -> Add x s s' -> eqA (fold f s' i) (fold f s (f x i)).
  Proof.
  intros.
  do 2 rewrite M.fold_1.
  set (g:=fun (a : A) (e : elt) => f e a).
  change (eqA (fold_left g (elements s') i) (fold_left g (x::elements s) i)).
  unfold g.
  do 2 rewrite <- fold_left_rev_right.
  apply (@fold_right_eqlistA E.t E.eq A eqA st); auto.
  apply eqlistA_rev.
  apply elements_Add_Below; auto.
  Qed.

  (** The following results have already been proved earlier, 
    but we can now prove them with one hypothesis less:
    no need for [(transpose eqA f)]. *)

  Section FoldOpt. 
  Variables (A:Set)(eqA:A->A->Prop)(st:Setoid_Theory _ eqA).
  Variables (f:elt->A->A)(Comp:compat_op E.eq eqA f).

  Lemma fold_equal : 
   forall i s s', s[=]s' -> eqA (fold f s i) (fold f s' i).
  Proof.
  intros; do 2 rewrite M.fold_1.
  do 2 rewrite <- fold_left_rev_right.
  apply (@fold_right_eqlistA E.t E.eq A eqA st); auto.
  apply eqlistA_rev.
  apply sort_equivlistA_eqlistA; auto with set.
  red; intro a; do 2 rewrite <- elements_iff; auto.
  Qed.

  Lemma fold_init : forall i i' s, eqA i i' -> 
   eqA (fold f s i) (fold f s i').
  Proof. 
  intros; do 2 rewrite M.fold_1.
  do 2 rewrite <- fold_left_rev_right.
  induction (rev (elements s)); simpl; auto.
  Qed.

  Lemma add_fold : forall i s x, In x s -> 
   eqA (fold f (add x s) i) (fold f s i).
  Proof.
  intros; apply fold_equal; auto with set.
  Qed.

  Lemma remove_fold_2: forall i s x, ~In x s -> 
   eqA (fold f (remove x s) i) (fold f s i).
  Proof.
  intros.
  apply fold_equal; auto with set.
  Qed.

  End FoldOpt.

End OrdProperties.
