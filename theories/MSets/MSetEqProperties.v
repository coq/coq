(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite sets library *)

(** This module proves many properties of finite sets that
    are consequences of the axiomatization in [FsetInterface]
    Contrary to the functor in [FsetProperties] it uses
    sets operations instead of predicates over sets, i.e.
    [mem x s=true] instead of [In x s],
    [equal s s'=true] instead of [Equal s s'], etc. *)

Require Import MSetProperties Zerob Sumbool Omega DecidableTypeEx.

Module WEqPropertiesOn (Import E:DecidableType)(M:WSetsOn E).
Module Import MP := WPropertiesOn E M.
Import FM Dec.F.
Import M.

Definition Add := MP.Add.

Section BasicProperties.

(** Some old specifications written with boolean equalities. *)

Variable s s' s'': t.
Variable x y z : elt.

Lemma mem_eq:
  E.eq x y -> mem x s=mem y s.
Proof.
intro H; rewrite H; auto.
Qed.

Lemma equal_mem_1:
  (forall a, mem a s=mem a s') -> equal s s'=true.
Proof.
intros; apply equal_1; unfold Equal; intros.
do 2 rewrite mem_iff; rewrite H; tauto.
Qed.

Lemma equal_mem_2:
  equal s s'=true -> forall a, mem a s=mem a s'.
Proof.
intros; rewrite (equal_2 H); auto.
Qed.

Lemma subset_mem_1:
  (forall a, mem a s=true->mem a s'=true) -> subset s s'=true.
Proof.
intros; apply subset_1; unfold Subset; intros a.
do 2 rewrite mem_iff; auto.
Qed.

Lemma subset_mem_2:
  subset s s'=true -> forall a, mem a s=true -> mem a s'=true.
Proof.
intros H a; do 2 rewrite <- mem_iff; apply subset_2; auto.
Qed.

Lemma empty_mem: mem x empty=false.
Proof.
rewrite <- not_mem_iff; auto with set.
Qed.

Lemma is_empty_equal_empty: is_empty s = equal s empty.
Proof.
apply bool_1; split; intros.
auto with set.
rewrite <- is_empty_iff; auto with set.
Qed.

Lemma choose_mem_1: choose s=Some x -> mem x s=true.
Proof.
auto with set.
Qed.

Lemma choose_mem_2: choose s=None -> is_empty s=true.
Proof.
auto with set.
Qed.

Lemma add_mem_1: mem x (add x s)=true.
Proof.
auto with set relations.
Qed.

Lemma add_mem_2: ~E.eq x y -> mem y (add x s)=mem y s.
Proof.
apply add_neq_b.
Qed.

Lemma remove_mem_1: mem x (remove x s)=false.
Proof.
rewrite <- not_mem_iff; auto with set relations.
Qed.

Lemma remove_mem_2: ~E.eq x y -> mem y (remove x s)=mem y s.
Proof.
apply remove_neq_b.
Qed.

Lemma singleton_equal_add:
  equal (singleton x) (add x empty)=true.
Proof.
rewrite (singleton_equal_add x); auto with set.
Qed.

Lemma union_mem:
  mem x (union s s')=mem x s || mem x s'.
Proof.
apply union_b.
Qed.

Lemma inter_mem:
  mem x (inter s s')=mem x s && mem x s'.
Proof.
apply inter_b.
Qed.

Lemma diff_mem:
  mem x (diff s s')=mem x s && negb (mem x s').
Proof.
apply diff_b.
Qed.

(** properties of [mem] *)

Lemma mem_3 : ~In x s -> mem x s=false.
Proof.
intros; rewrite <- not_mem_iff; auto.
Qed.

Lemma mem_4 : mem x s=false -> ~In x s.
Proof.
intros; rewrite not_mem_iff; auto.
Qed.

(** Properties of [equal] *)

Lemma equal_refl: equal s s=true.
Proof.
auto with set.
Qed.

Lemma equal_sym: equal s s'=equal s' s.
Proof.
intros; apply bool_1; do 2 rewrite <- equal_iff; intuition.
Qed.

Lemma equal_trans:
 equal s s'=true -> equal s' s''=true -> equal s s''=true.
Proof.
intros; rewrite (equal_2 H); auto.
Qed.

Lemma equal_equal:
 equal s s'=true -> equal s s''=equal s' s''.
Proof.
intros; rewrite (equal_2 H); auto.
Qed.

Lemma equal_cardinal:
 equal s s'=true -> cardinal s=cardinal s'.
Proof.
auto with set.
Qed.

(* Properties of [subset] *)

Lemma subset_refl: subset s s=true.
Proof.
auto with set.
Qed.

Lemma subset_antisym:
 subset s s'=true -> subset s' s=true -> equal s s'=true.
Proof.
auto with set.
Qed.

Lemma subset_trans:
 subset s s'=true -> subset s' s''=true -> subset s s''=true.
Proof.
do 3 rewrite <- subset_iff; intros.
apply subset_trans with s'; auto.
Qed.

Lemma subset_equal:
 equal s s'=true -> subset s s'=true.
Proof.
auto with set.
Qed.

(** Properties of [choose] *)

Lemma choose_mem_3:
 is_empty s=false -> {x:elt|choose s=Some x /\ mem x s=true}.
Proof.
intros.
generalize (@choose_1 s) (@choose_2 s).
destruct (choose s);intros.
exists e;auto with set.
generalize (H1 (eq_refl None)); clear H1.
intros; rewrite (is_empty_1 H1) in H; discriminate.
Qed.

Lemma choose_mem_4: choose empty=None.
Proof.
generalize (@choose_1 empty).
case (@choose empty);intros;auto.
elim (@empty_1 e); auto.
Qed.

(** Properties of [add] *)

Lemma add_mem_3:
 mem y s=true -> mem y (add x s)=true.
Proof.
auto with set.
Qed.

Lemma add_equal:
 mem x s=true -> equal (add x s) s=true.
Proof.
auto with set.
Qed.

(** Properties of [remove] *)

Lemma remove_mem_3:
 mem y (remove x s)=true -> mem y s=true.
Proof.
rewrite remove_b; intros H;destruct (andb_prop _ _ H); auto.
Qed.

Lemma remove_equal:
 mem x s=false -> equal (remove x s) s=true.
Proof.
intros; apply equal_1; apply remove_equal.
rewrite not_mem_iff; auto.
Qed.

Lemma add_remove:
 mem x s=true -> equal (add x (remove x s)) s=true.
Proof.
intros; apply equal_1; apply add_remove; auto with set.
Qed.

Lemma remove_add:
 mem x s=false -> equal (remove x (add x s)) s=true.
Proof.
intros; apply equal_1; apply remove_add; auto.
rewrite not_mem_iff; auto.
Qed.

(** Properties of [is_empty] *)

Lemma is_empty_cardinal: is_empty s = zerob (cardinal s).
Proof.
intros; apply bool_1; split; intros.
rewrite MP.cardinal_1; simpl; auto with set.
assert (cardinal s = 0) by (apply zerob_true_elim; auto).
auto with set.
Qed.

(** Properties of [singleton] *)

Lemma singleton_mem_1: mem x (singleton x)=true.
Proof.
auto with set relations.
Qed.

Lemma singleton_mem_2: ~E.eq x y -> mem y (singleton x)=false.
Proof.
intros; rewrite singleton_b.
unfold eqb; destruct (E.eq_dec x y); intuition.
Qed.

Lemma singleton_mem_3: mem y (singleton x)=true -> E.eq x y.
Proof.
intros; apply singleton_1; auto with set.
Qed.

(** Properties of [union] *)

Lemma union_sym:
 equal (union s s') (union s' s)=true.
Proof.
auto with set.
Qed.

Lemma union_subset_equal:
 subset s s'=true -> equal (union s s') s'=true.
Proof.
auto with set.
Qed.

Lemma union_equal_1:
 equal s s'=true-> equal (union s s'') (union s' s'')=true.
Proof.
auto with set.
Qed.

Lemma union_equal_2:
 equal s' s''=true-> equal (union s s') (union s s'')=true.
Proof.
auto with set.
Qed.

Lemma union_assoc:
 equal (union (union s s') s'') (union s (union s' s''))=true.
Proof.
auto with set.
Qed.

Lemma add_union_singleton:
 equal (add x s) (union (singleton x) s)=true.
Proof.
auto with set.
Qed.

Lemma union_add:
 equal (union (add x s) s') (add x (union s s'))=true.
Proof.
auto with set.
Qed.

(* characterisation of [union] via [subset] *)

Lemma union_subset_1: subset s (union s s')=true.
Proof.
auto with set.
Qed.

Lemma union_subset_2: subset s' (union s s')=true.
Proof.
auto with set.
Qed.

Lemma union_subset_3:
 subset s s''=true -> subset s' s''=true ->
  subset (union s s') s''=true.
Proof.
intros; apply subset_1; apply union_subset_3; auto with set.
Qed.

(** Properties of [inter] *)

Lemma inter_sym: equal (inter s s') (inter s' s)=true.
Proof.
auto with set.
Qed.

Lemma inter_subset_equal:
 subset s s'=true -> equal (inter s s') s=true.
Proof.
auto with set.
Qed.

Lemma inter_equal_1:
 equal s s'=true -> equal (inter s s'') (inter s' s'')=true.
Proof.
auto with set.
Qed.

Lemma inter_equal_2:
 equal s' s''=true -> equal (inter s s') (inter s s'')=true.
Proof.
auto with set.
Qed.

Lemma inter_assoc:
 equal (inter (inter s s') s'') (inter s (inter s' s''))=true.
Proof.
auto with set.
Qed.

Lemma union_inter_1:
 equal (inter (union s s') s'') (union (inter s s'') (inter s' s''))=true.
Proof.
auto with set.
Qed.

Lemma union_inter_2:
 equal (union (inter s s') s'') (inter (union s s'') (union s' s''))=true.
Proof.
auto with set.
Qed.

Lemma inter_add_1: mem x s'=true ->
 equal (inter (add x s) s') (add x (inter s s'))=true.
Proof.
auto with set.
Qed.

Lemma inter_add_2: mem x s'=false ->
 equal (inter (add x s) s') (inter s s')=true.
Proof.
intros; apply equal_1; apply inter_add_2.
rewrite not_mem_iff; auto.
Qed.

(* characterisation of [union] via [subset] *)

Lemma inter_subset_1: subset (inter s s') s=true.
Proof.
auto with set.
Qed.

Lemma inter_subset_2: subset (inter s s') s'=true.
Proof.
auto with set.
Qed.

Lemma inter_subset_3:
 subset s'' s=true -> subset s'' s'=true ->
  subset s'' (inter s s')=true.
Proof.
intros; apply subset_1; apply inter_subset_3; auto with set.
Qed.

(** Properties of [diff] *)

Lemma diff_subset: subset (diff s s') s=true.
Proof.
auto with set.
Qed.

Lemma diff_subset_equal:
 subset s s'=true -> equal (diff s s') empty=true.
Proof.
auto with set.
Qed.

Lemma remove_inter_singleton:
 equal (remove x s) (diff s (singleton x))=true.
Proof.
auto with set.
Qed.

Lemma diff_inter_empty:
 equal (inter (diff s s') (inter s s')) empty=true.
Proof.
auto with set.
Qed.

Lemma diff_inter_all:
 equal (union (diff s s') (inter s s')) s=true.
Proof.
auto with set.
Qed.

End BasicProperties.

Hint Immediate empty_mem is_empty_equal_empty add_mem_1
   remove_mem_1 singleton_equal_add union_mem inter_mem
   diff_mem equal_sym add_remove remove_add : set.
Hint Resolve equal_mem_1 subset_mem_1 choose_mem_1
   choose_mem_2 add_mem_2 remove_mem_2 equal_refl equal_equal
   subset_refl subset_equal subset_antisym
   add_mem_3 add_equal remove_mem_3 remove_equal : set.


(** General recursion principle *)

Lemma set_rec:  forall (P:t->Type),
 (forall s s', equal s s'=true -> P s -> P s') ->
 (forall s x, mem x s=false -> P s -> P (add x s)) ->
 P empty -> forall s, P s.
Proof.
intros.
apply set_induction; auto; intros.
apply X with empty; auto with set.
apply X with (add x s0); auto with set.
apply equal_1; intro a; rewrite add_iff; rewrite (H0 a); tauto.
apply X0; auto with set; apply mem_3; auto.
Qed.

(** Properties of [fold] *)

Lemma exclusive_set : forall s s' x,
 ~(In x s/\In x s') <-> mem x s && mem x s'=false.
Proof.
intros; do 2 rewrite mem_iff.
destruct (mem x s); destruct (mem x s'); intuition.
Qed.

Section Fold.
Variables (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA).
Variables (f:elt->A->A)(Comp:Proper (E.eq==>eqA==>eqA) f)(Ass:transpose eqA f).
Variables (i:A).
Variables (s s':t)(x:elt).

Lemma fold_empty: (fold f empty i) = i.
Proof.
apply fold_empty; auto.
Qed.

Lemma fold_equal:
 equal s s'=true -> eqA (fold f s i) (fold f s' i).
Proof.
intros; apply fold_equal with (eqA:=eqA); auto with set.
Qed.

Lemma fold_add:
 mem x s=false -> eqA (fold f (add x s) i) (f x (fold f s i)).
Proof.
intros; apply fold_add with (eqA:=eqA); auto.
rewrite not_mem_iff; auto.
Qed.

Lemma add_fold:
  mem x s=true -> eqA (fold f (add x s) i) (fold f s i).
Proof.
intros; apply add_fold with (eqA:=eqA); auto with set.
Qed.

Lemma remove_fold_1:
 mem x s=true -> eqA (f x (fold f (remove x s) i)) (fold f s i).
Proof.
intros; apply remove_fold_1 with (eqA:=eqA); auto with set.
Qed.

Lemma remove_fold_2:
 mem x s=false -> eqA (fold f (remove x s) i) (fold f s i).
Proof.
intros; apply remove_fold_2 with (eqA:=eqA); auto.
rewrite not_mem_iff; auto.
Qed.

Lemma fold_union:
 (forall x, mem x s && mem x s'=false) ->
 eqA (fold f (union s s') i) (fold f s (fold f s' i)).
Proof.
intros; apply fold_union with (eqA:=eqA); auto.
intros; rewrite exclusive_set; auto.
Qed.

End Fold.

(** Properties of [cardinal] *)

Lemma add_cardinal_1:
 forall s x, mem x s=true -> cardinal (add x s)=cardinal s.
Proof.
auto with set.
Qed.

Lemma add_cardinal_2:
 forall s x, mem x s=false -> cardinal (add x s)=S (cardinal s).
Proof.
intros; apply add_cardinal_2; auto.
rewrite not_mem_iff; auto.
Qed.

Lemma remove_cardinal_1:
 forall s x, mem x s=true -> S (cardinal (remove x s))=cardinal s.
Proof.
intros; apply remove_cardinal_1; auto with set.
Qed.

Lemma remove_cardinal_2:
 forall s x, mem x s=false -> cardinal (remove x s)=cardinal s.
Proof.
intros; apply Equal_cardinal; apply equal_2; auto with set.
Qed.

Lemma union_cardinal:
 forall s s', (forall x, mem x s && mem x s'=false) ->
 cardinal (union s s')=cardinal s+cardinal s'.
Proof.
intros; apply union_cardinal; auto; intros.
rewrite exclusive_set; auto.
Qed.

Lemma subset_cardinal:
 forall s s', subset s s'=true -> cardinal s<=cardinal s'.
Proof.
intros; apply subset_cardinal; auto with set.
Qed.

Section Bool.

(** Properties of [filter] *)

Variable f:elt->bool.
Variable Comp: Proper (E.eq==>Logic.eq) f.

Let Comp' : Proper (E.eq==>Logic.eq) (fun x =>negb (f x)).
Proof.
repeat red; intros; f_equal; auto.
Qed.

Lemma filter_mem: forall s x, mem x (filter f s)=mem x s && f x.
Proof.
intros; apply filter_b; auto.
Qed.

Lemma for_all_filter:
 forall s, for_all f s=is_empty (filter (fun x => negb (f x)) s).
Proof.
intros; apply bool_1; split; intros.
apply is_empty_1.
unfold Empty; intros.
rewrite filter_iff; auto.
red; destruct 1.
rewrite <- (@for_all_iff s f) in H; auto.
rewrite (H a H0) in H1; discriminate.
apply for_all_1; auto; red; intros.
revert H; rewrite <- is_empty_iff.
unfold Empty; intro H; generalize (H x); clear H.
rewrite filter_iff; auto.
destruct (f x); auto.
Qed.

Lemma exists_filter :
 forall s, exists_ f s=negb (is_empty (filter f s)).
Proof.
intros; apply bool_1; split; intros.
destruct (exists_2 Comp H) as (a,(Ha1,Ha2)).
apply bool_6.
red; intros; apply (@is_empty_2 _ H0 a); auto with set.
generalize (@choose_1 (filter f s)) (@choose_2 (filter f s)).
destruct (choose (filter f s)).
intros H0 _; apply exists_1; auto.
exists e; generalize (H0 e); rewrite filter_iff; auto.
intros _ H0.
rewrite (is_empty_1 (H0 (eq_refl None))) in H; auto; discriminate.
Qed.

Lemma partition_filter_1:
 forall s, equal (fst (partition f s)) (filter f s)=true.
Proof.
auto with set.
Qed.

Lemma partition_filter_2:
 forall s, equal (snd (partition f s)) (filter (fun x => negb (f x)) s)=true.
Proof.
auto with set.
Qed.

Lemma filter_add_1 : forall s x, f x = true ->
 filter f (add x s) [=] add x (filter f s).
Proof.
red; intros; set_iff; do 2 (rewrite filter_iff; auto); set_iff.
intuition.
rewrite <- H; apply Comp; auto with relations.
Qed.

Lemma filter_add_2 : forall s x, f x = false ->
 filter f (add x s) [=] filter f s.
Proof.
red; intros; do 2 (rewrite filter_iff; auto); set_iff.
intuition.
assert (f x = f a) by (apply Comp; auto).
rewrite H in H1; rewrite H2 in H1; discriminate.
Qed.

Lemma add_filter_1 : forall s s' x,
 f x=true -> (Add x s s') -> (Add x (filter f s) (filter f s')).
Proof.
unfold Add, MP.Add; intros.
repeat rewrite filter_iff; auto.
rewrite H0; clear H0.
intuition.
setoid_replace y with x; auto with relations.
Qed.

Lemma add_filter_2 : forall s s' x,
 f x=false -> (Add x s s') -> filter f s [=] filter f s'.
Proof.
unfold Add, MP.Add, Equal; intros.
repeat rewrite filter_iff; auto.
rewrite H0; clear H0.
intuition.
setoid_replace x with a in H; auto. congruence.
Qed.

Lemma union_filter: forall f g,
  Proper (E.eq==>Logic.eq) f -> Proper (E.eq==>Logic.eq) g ->
  forall s, union (filter f s) (filter g s) [=] filter (fun x=>orb (f x) (g x)) s.
Proof.
clear Comp' Comp f.
intros.
assert (Proper (E.eq==>Logic.eq) (fun x => orb (f x) (g x))).
  repeat red; intros.
  rewrite (H x y H1);  rewrite (H0 x y H1); auto.
unfold Equal; intros; set_iff; repeat rewrite filter_iff; auto.
assert (f a || g a = true <-> f a = true \/ g a = true).
  split; auto with bool.
  intro H3; destruct (orb_prop _ _ H3); auto.
tauto.
Qed.

Lemma filter_union: forall s s', filter f (union s s') [=] union (filter f s) (filter f s').
Proof.
unfold Equal; intros; set_iff; repeat rewrite filter_iff; auto; set_iff; tauto.
Qed.

(** Properties of [for_all] *)

Lemma for_all_mem_1: forall s,
 (forall x, (mem x s)=true->(f x)=true) -> (for_all f s)=true.
Proof.
intros.
rewrite for_all_filter; auto.
rewrite is_empty_equal_empty.
apply equal_mem_1;intros.
rewrite filter_b; auto.
rewrite empty_mem.
generalize (H a); case (mem a s);intros;auto.
rewrite H0;auto.
Qed.

Lemma for_all_mem_2: forall s,
 (for_all f s)=true -> forall x,(mem x s)=true -> (f x)=true.
Proof.
intros.
rewrite for_all_filter in H; auto.
rewrite is_empty_equal_empty in H.
generalize (equal_mem_2 _ _ H x).
rewrite filter_b; auto.
rewrite empty_mem.
rewrite H0; simpl;intros.
rewrite <- negb_false_iff; auto.
Qed.

Lemma for_all_mem_3:
 forall s x,(mem x s)=true -> (f x)=false -> (for_all f s)=false.
Proof.
intros.
apply (bool_eq_ind (for_all f s));intros;auto.
rewrite for_all_filter in H1; auto.
rewrite is_empty_equal_empty in H1.
generalize (equal_mem_2 _ _ H1 x).
rewrite filter_b; auto.
rewrite empty_mem.
rewrite H.
rewrite H0.
simpl;auto.
Qed.

Lemma for_all_mem_4:
 forall s, for_all f s=false -> {x:elt | mem x s=true /\ f x=false}.
Proof.
intros.
rewrite for_all_filter in H; auto.
destruct (choose_mem_3 _ H) as (x,(H0,H1));intros.
exists x.
rewrite filter_b in H1; auto.
elim (andb_prop _ _ H1).
split;auto.
rewrite <- negb_true_iff; auto.
Qed.

(** Properties of [exists] *)

Lemma for_all_exists:
 forall s, exists_ f s = negb (for_all (fun x =>negb (f x)) s).
Proof.
intros.
rewrite for_all_b; auto.
rewrite exists_b; auto.
induction (elements s); simpl; auto.
destruct (f a); simpl; auto.
Qed.

End Bool.
Section Bool'.

Variable f:elt->bool.
Variable Comp: Proper (E.eq==>Logic.eq) f.

Let Comp' : Proper (E.eq==>Logic.eq) (fun x => negb (f x)).
Proof.
repeat red; intros; f_equal; auto.
Qed.

Lemma exists_mem_1:
 forall s, (forall x, mem x s=true->f x=false) -> exists_ f s=false.
Proof.
intros.
rewrite for_all_exists; auto.
rewrite for_all_mem_1;auto with bool.
intros;generalize (H x H0);intros.
rewrite negb_true_iff; auto.
Qed.

Lemma exists_mem_2:
 forall s, exists_ f s=false -> forall x, mem x s=true -> f x=false.
Proof.
intros.
rewrite for_all_exists in H; auto.
rewrite negb_false_iff in H.
rewrite <- negb_true_iff.
apply for_all_mem_2 with (2:=H); auto.
Qed.

Lemma exists_mem_3:
 forall s x, mem x s=true -> f x=true -> exists_ f s=true.
Proof.
intros.
rewrite for_all_exists; auto.
rewrite negb_true_iff.
apply for_all_mem_3 with x;auto.
rewrite negb_false_iff; auto.
Qed.

Lemma exists_mem_4:
 forall s, exists_ f s=true -> {x:elt | (mem x s)=true /\ (f x)=true}.
Proof.
intros.
rewrite for_all_exists in H; auto.
rewrite negb_true_iff in H.
destruct (@for_all_mem_4 (fun x =>negb (f x)) Comp' s) as (x,[]); auto.
exists x;split;auto.
rewrite <-negb_false_iff; auto.
Qed.

End Bool'.

Section Sum.

(** Adding a valuation function on all elements of a set. *)

Definition sum (f:elt -> nat)(s:t) := fold (fun x => plus (f x)) s 0.
Notation compat_opL := (Proper (E.eq==>Logic.eq==>Logic.eq)).
Notation transposeL := (transpose Logic.eq).

Lemma sum_plus :
  forall f g,
  Proper (E.eq==>Logic.eq) f -> Proper (E.eq==>Logic.eq) g ->
    forall s, sum (fun x =>f x+g x) s = sum f s + sum g s.
Proof.
unfold sum.
intros f g Hf Hg.
assert (fc : compat_opL (fun x:elt =>plus (f x))) by
 (repeat red; intros; rewrite Hf; auto).
assert (ft : transposeL (fun x:elt =>plus (f x))) by (red; intros; omega).
assert (gc : compat_opL (fun x:elt => plus (g x))) by
 (repeat red; intros; rewrite Hg; auto).
assert (gt : transposeL (fun x:elt =>plus (g x))) by (red; intros; omega).
assert (fgc : compat_opL (fun x:elt =>plus ((f x)+(g x)))) by
  (repeat red; intros; rewrite Hf,Hg; auto).
assert (fgt : transposeL (fun x:elt=>plus ((f x)+(g x)))) by (red; intros; omega).
intros s;pattern s; apply set_rec.
intros.
rewrite <- (fold_equal _ _ _ _ fc ft 0 _ _ H).
rewrite <- (fold_equal _ _ _ _ gc gt 0 _ _ H).
rewrite <- (fold_equal _ _ _ _ fgc fgt 0 _ _ H); auto.
intros. do 3 (rewrite fold_add; auto with *).
do 3 rewrite fold_empty;auto.
Qed.

Lemma sum_filter : forall f : elt -> bool, Proper (E.eq==>Logic.eq) f ->
  forall s, (sum (fun x => if f x then 1 else 0) s) = (cardinal (filter f s)).
Proof.
unfold sum; intros f Hf.
assert (st : Equivalence (@Logic.eq nat)) by (split; congruence).
assert (cc : compat_opL (fun x => plus (if f x then 1 else 0))) by
 (repeat red; intros; rewrite Hf; auto).
assert (ct : transposeL (fun x => plus (if f x then 1 else 0))) by
 (red; intros; omega).
intros s;pattern s; apply set_rec.
intros.
change elt with E.t.
rewrite <- (fold_equal _ _ st _ cc ct 0 _ _ H).
apply equal_2 in H; rewrite <- H, <-H0; auto.
intros; rewrite (fold_add _ _ st _ cc ct); auto.
generalize (@add_filter_1 f Hf s0 (add x s0) x) (@add_filter_2 f Hf s0 (add x s0) x) .
assert (~ In x (filter f s0)).
 intro H1; rewrite (mem_1 (filter_1 Hf H1)) in H; discriminate H.
case (f x); simpl; intros.
rewrite (MP.cardinal_2 H1 (H2 (eq_refl true) (MP.Add_add s0 x))); auto.
rewrite <- (MP.Equal_cardinal (H3 (eq_refl false) (MP.Add_add s0 x))); auto.
intros; rewrite fold_empty;auto.
rewrite MP.cardinal_1; auto.
unfold Empty; intros.
rewrite filter_iff; auto; set_iff; tauto.
Qed.

Lemma fold_compat :
  forall (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)
  (f g:elt->A->A),
  Proper (E.eq==>eqA==>eqA) f -> transpose eqA f ->
  Proper (E.eq==>eqA==>eqA) g -> transpose eqA g ->
  forall (i:A)(s:t),(forall x:elt, (In x s) -> forall y, (eqA (f x y) (g x y))) ->
  (eqA (fold f s i) (fold g s i)).
Proof.
intros A eqA st f g fc ft gc gt i.
intro s; pattern s; apply set_rec; intros.
transitivity (fold f s0 i).
apply fold_equal with (eqA:=eqA); auto.
rewrite equal_sym; auto.
transitivity (fold g s0 i).
apply H0; intros; apply H1; auto with set.
elim  (equal_2 H x); auto with set; intros.
apply fold_equal with (eqA:=eqA); auto with set.
transitivity (f x (fold f s0 i)).
apply fold_add with (eqA:=eqA); auto with set.
transitivity (g x (fold f s0 i)); auto with set relations.
transitivity (g x (fold g s0 i)); auto with set relations.
apply gc; auto with set relations.
symmetry; apply fold_add with (eqA:=eqA); auto.
do 2 rewrite fold_empty; reflexivity.
Qed.

Lemma sum_compat :
  forall f g, Proper (E.eq==>Logic.eq) f -> Proper (E.eq==>Logic.eq) g ->
  forall s, (forall x, In x s -> f x=g x) -> sum f s=sum g s.
intros.
unfold sum; apply (@fold_compat _ (@Logic.eq nat));
 repeat red; auto with *.
Qed.

End Sum.

End WEqPropertiesOn.

(** Now comes variants for self-contained weak sets and for full sets.
    For these variants, only one argument is necessary. Thanks to
    the subtyping [WS<=S], the [EqProperties] functor which is meant to be
    used on modules [(M:S)] can simply be an alias of [WEqProperties]. *)

Module WEqProperties (M:WSets) := WEqPropertiesOn M.E M.
Module EqProperties := WEqProperties.
