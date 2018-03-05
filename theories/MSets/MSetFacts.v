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

(** This functor derives additional facts from [MSetInterface.S]. These
  facts are mainly the specifications of [MSetInterface.S] written using
  different styles: equivalence and boolean equalities.
  Moreover, we prove that [E.Eq] and [Equal] are setoid equalities.
*)

Require Import DecidableTypeEx.
Require Export MSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.

(** First, a functor for Weak Sets in functorial version. *)

Module WFactsOn (Import E : DecidableType)(Import M : WSetsOn E).

Notation eq_dec := E.eq_dec.
Definition eqb x y := if eq_dec x y then true else false.

(** * Specifications written using implications :
      this used to be the default interface. *)

Section ImplSpec.
Variable s s' : t.
Variable x y : elt.

Lemma In_1 : E.eq x y -> In x s -> In y s.
Proof. intros E; rewrite E; auto. Qed.

Lemma mem_1 : In x s -> mem x s = true.
Proof. intros; apply <- mem_spec; auto. Qed.
Lemma mem_2 : mem x s = true -> In x s.
Proof. intros; apply -> mem_spec; auto. Qed.

Lemma equal_1 : Equal s s' -> equal s s' = true.
Proof. intros; apply <- equal_spec; auto. Qed.
Lemma equal_2 : equal s s' = true -> Equal s s'.
Proof. intros; apply -> equal_spec; auto. Qed.

Lemma subset_1 : Subset s s' -> subset s s' = true.
Proof. intros; apply <- subset_spec; auto. Qed.
Lemma subset_2 : subset s s' = true -> Subset s s'.
Proof. intros; apply -> subset_spec; auto. Qed.

Lemma is_empty_1 : Empty s -> is_empty s = true.
Proof. intros; apply <- is_empty_spec; auto. Qed.
Lemma is_empty_2 : is_empty s = true -> Empty s.
Proof. intros; apply -> is_empty_spec; auto. Qed.

Lemma add_1 : E.eq x y -> In y (add x s).
Proof. intros; apply <- add_spec. auto with relations. Qed.
Lemma add_2 : In y s -> In y (add x s).
Proof. intros; apply <- add_spec; auto. Qed.
Lemma add_3 : ~ E.eq x y -> In y (add x s) -> In y s.
Proof. rewrite add_spec. intros H [H'|H']; auto. elim H; auto with relations. Qed.

Lemma remove_1 : E.eq x y -> ~ In y (remove x s).
Proof. intros; rewrite remove_spec; intuition. Qed.
Lemma remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
Proof. intros; apply <- remove_spec; auto with relations. Qed.
Lemma remove_3 : In y (remove x s) -> In y s.
Proof. rewrite remove_spec; intuition. Qed.

Lemma singleton_1 : In y (singleton x) -> E.eq x y.
Proof. rewrite singleton_spec; auto with relations. Qed.
Lemma singleton_2 : E.eq x y -> In y (singleton x).
Proof. rewrite singleton_spec; auto with relations. Qed.

Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
Proof. rewrite union_spec; auto. Qed.
Lemma union_2 : In x s -> In x (union s s').
Proof. rewrite union_spec; auto. Qed.
Lemma union_3 : In x s' -> In x (union s s').
Proof. rewrite union_spec; auto. Qed.

Lemma inter_1 : In x (inter s s') -> In x s.
Proof. rewrite inter_spec; intuition. Qed.
Lemma inter_2 : In x (inter s s') -> In x s'.
Proof. rewrite inter_spec; intuition. Qed.
Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
Proof. rewrite inter_spec; intuition. Qed.

Lemma diff_1 : In x (diff s s') -> In x s.
Proof. rewrite diff_spec; intuition. Qed.
Lemma diff_2 : In x (diff s s') -> ~ In x s'.
Proof. rewrite diff_spec; intuition. Qed.
Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
Proof. rewrite diff_spec; auto. Qed.

Variable f : elt -> bool.
Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

Lemma filter_1 : compatb f -> In x (filter f s) -> In x s.
Proof. intros P; rewrite filter_spec; intuition. Qed.
Lemma filter_2 : compatb f -> In x (filter f s) -> f x = true.
Proof. intros P; rewrite filter_spec; intuition. Qed.
Lemma filter_3 : compatb f -> In x s -> f x = true -> In x (filter f s).
Proof. intros P; rewrite filter_spec; intuition. Qed.

Lemma for_all_1 : compatb f ->
      For_all (fun x => f x = true) s -> for_all f s = true.
Proof. intros; apply <- for_all_spec; auto. Qed.
Lemma for_all_2 : compatb f ->
      for_all f s = true -> For_all (fun x => f x = true) s.
Proof. intros; apply -> for_all_spec; auto. Qed.

Lemma exists_1 : compatb f ->
      Exists (fun x => f x = true) s -> exists_ f s = true.
Proof. intros; apply <- exists_spec; auto. Qed.

Lemma exists_2 : compatb f ->
      exists_ f s = true -> Exists (fun x => f x = true) s.
Proof. intros; apply -> exists_spec; auto. Qed.

Lemma elements_1 : In x s -> InA E.eq x (elements s).
Proof. intros; apply <- elements_spec1; auto. Qed.
Lemma elements_2 : InA E.eq x (elements s) -> In x s.
Proof. intros; apply -> elements_spec1; auto. Qed.

End ImplSpec.

Notation empty_1 := empty_spec (only parsing).
Notation fold_1 := fold_spec (only parsing).
Notation cardinal_1 := cardinal_spec (only parsing).
Notation partition_1 := partition_spec1 (only parsing).
Notation partition_2 := partition_spec2 (only parsing).
Notation choose_1 := choose_spec1 (only parsing).
Notation choose_2 := choose_spec2 (only parsing).
Notation elements_3w := elements_spec2w (only parsing).

Hint Resolve mem_1 equal_1 subset_1 empty_1
    is_empty_1 choose_1 choose_2 add_1 add_2 remove_1
    remove_2 singleton_2 union_1 union_2 union_3
    inter_3 diff_3 fold_1 filter_3 for_all_1 exists_1
    partition_1 partition_2 elements_1 elements_3w
    : set.
Hint Immediate In_1 mem_2 equal_2 subset_2 is_empty_2 add_3
    remove_3 singleton_1 inter_1 inter_2 diff_1 diff_2
    filter_1 filter_2 for_all_2 exists_2 elements_2
    : set.


(** * Specifications written using equivalences :
      this is now provided by the default interface. *)

Section IffSpec.
Variable s s' s'' : t.
Variable x y z : elt.

Lemma In_eq_iff : E.eq x y -> (In x s <-> In y s).
Proof.
intros E; rewrite E; intuition.
Qed.

Lemma mem_iff : In x s <-> mem x s = true.
Proof. apply iff_sym, mem_spec. Qed.

Lemma not_mem_iff : ~In x s <-> mem x s = false.
Proof.
rewrite <-mem_spec; destruct (mem x s); intuition.
Qed.

Lemma equal_iff : s[=]s' <-> equal s s' = true.
Proof. apply iff_sym, equal_spec. Qed.

Lemma subset_iff : s[<=]s' <-> subset s s' = true.
Proof. apply iff_sym, subset_spec. Qed.

Lemma empty_iff : In x empty <-> False.
Proof. intuition; apply (empty_spec H). Qed.

Lemma is_empty_iff : Empty s <-> is_empty s = true.
Proof. apply iff_sym, is_empty_spec. Qed.

Lemma singleton_iff : In y (singleton x) <-> E.eq x y.
Proof. rewrite singleton_spec; intuition. Qed.

Lemma add_iff : In y (add x s) <-> E.eq x y \/ In y s.
Proof. rewrite add_spec; intuition. Qed.

Lemma add_neq_iff : ~ E.eq x y -> (In y (add x s)  <-> In y s).
Proof. rewrite add_spec; intuition. elim H; auto with relations. Qed.

Lemma remove_iff : In y (remove x s) <-> In y s /\ ~E.eq x y.
Proof. rewrite remove_spec; intuition. Qed.

Lemma remove_neq_iff : ~ E.eq x y -> (In y (remove x s) <-> In y s).
Proof. rewrite remove_spec; intuition. Qed.

Variable f : elt -> bool.

Lemma for_all_iff : Proper (E.eq==>Logic.eq) f ->
  (For_all (fun x => f x = true) s <-> for_all f s = true).
Proof. intros; apply iff_sym, for_all_spec; auto. Qed.

Lemma exists_iff : Proper (E.eq==>Logic.eq) f ->
  (Exists (fun x => f x = true) s <-> exists_ f s = true).
Proof. intros; apply iff_sym, exists_spec; auto. Qed.

Lemma elements_iff : In x s <-> InA E.eq x (elements s).
Proof. apply iff_sym, elements_spec1. Qed.

End IffSpec.

Notation union_iff := union_spec (only parsing).
Notation inter_iff := inter_spec (only parsing).
Notation diff_iff := diff_spec (only parsing).
Notation filter_iff := filter_spec (only parsing).

(** Useful tactic for simplifying expressions like [In y (add x (union s s'))] *)

Ltac set_iff :=
 repeat (progress (
  rewrite add_iff || rewrite remove_iff || rewrite singleton_iff
  || rewrite union_iff || rewrite inter_iff || rewrite diff_iff
  || rewrite empty_iff)).

(**  * Specifications written using boolean predicates *)

Section BoolSpec.
Variable s s' s'' : t.
Variable x y z : elt.

Lemma mem_b : E.eq x y -> mem x s = mem y s.
Proof.
intros.
generalize (mem_iff s x) (mem_iff s y)(In_eq_iff s H).
destruct (mem x s); destruct (mem y s); intuition.
Qed.

Lemma empty_b : mem y empty = false.
Proof.
generalize (empty_iff y)(mem_iff empty y).
destruct (mem y empty); intuition.
Qed.

Lemma add_b : mem y (add x s) = eqb x y || mem y s.
Proof.
generalize (mem_iff (add x s) y)(mem_iff s y)(add_iff s x y); unfold eqb.
destruct (eq_dec x y); destruct (mem y s); destruct (mem y (add x s)); intuition.
Qed.

Lemma add_neq_b : ~ E.eq x y -> mem y (add x s) = mem y s.
Proof.
intros; generalize (mem_iff (add x s) y)(mem_iff s y)(add_neq_iff s H).
destruct (mem y s); destruct (mem y (add x s)); intuition.
Qed.

Lemma remove_b : mem y (remove x s) = mem y s && negb (eqb x y).
Proof.
generalize (mem_iff (remove x s) y)(mem_iff s y)(remove_iff s x y); unfold eqb.
destruct (eq_dec x y); destruct (mem y s); destruct (mem y (remove x s)); simpl; intuition.
Qed.

Lemma remove_neq_b : ~ E.eq x y -> mem y (remove x s) = mem y s.
Proof.
intros; generalize (mem_iff (remove x s) y)(mem_iff s y)(remove_neq_iff s H).
destruct (mem y s); destruct (mem y (remove x s)); intuition.
Qed.

Lemma singleton_b : mem y (singleton x) = eqb x y.
Proof.
generalize (mem_iff (singleton x) y)(singleton_iff x y); unfold eqb.
destruct (eq_dec x y); destruct (mem y (singleton x)); intuition.
Qed.

Lemma union_b : mem x (union s s') = mem x s || mem x s'.
Proof.
generalize (mem_iff (union s s') x)(mem_iff s x)(mem_iff s' x)(union_iff s s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (union s s')); intuition.
Qed.

Lemma inter_b : mem x (inter s s') = mem x s && mem x s'.
Proof.
generalize (mem_iff (inter s s') x)(mem_iff s x)(mem_iff s' x)(inter_iff s s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (inter s s')); intuition.
Qed.

Lemma diff_b : mem x (diff s s') = mem x s && negb (mem x s').
Proof.
generalize (mem_iff (diff s s') x)(mem_iff s x)(mem_iff s' x)(diff_iff s s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (diff s s')); simpl; intuition.
Qed.

Lemma elements_b : mem x s = existsb (eqb x) (elements s).
Proof.
generalize (mem_iff s x)(elements_iff s x)(existsb_exists (eqb x) (elements s)).
rewrite InA_alt.
destruct (mem x s); destruct (existsb (eqb x) (elements s)); auto; intros.
symmetry.
rewrite H1.
destruct H0 as (H0,_).
destruct H0 as (a,(Ha1,Ha2)); [ intuition |].
exists a; intuition.
unfold eqb; destruct (eq_dec x a); auto.
rewrite <- H.
rewrite H0.
destruct H1 as (H1,_).
destruct H1 as (a,(Ha1,Ha2)); [intuition|].
exists a; intuition.
unfold eqb in *; destruct (eq_dec x a); auto; discriminate.
Qed.

Variable f : elt->bool.

Lemma filter_b : Proper (E.eq==>Logic.eq) f -> mem x (filter f s) = mem x s && f x.
Proof.
intros.
generalize (mem_iff (filter f s) x)(mem_iff s x)(filter_iff s x H).
destruct (mem x s); destruct (mem x (filter f s)); destruct (f x); simpl; intuition.
Qed.

Lemma for_all_b : Proper (E.eq==>Logic.eq) f ->
  for_all f s = forallb f (elements s).
Proof.
intros.
generalize (forallb_forall f (elements s))(for_all_iff s H)(elements_iff s).
unfold For_all.
destruct (forallb f (elements s)); destruct (for_all f s); auto; intros.
rewrite <- H1; intros.
destruct H0 as (H0,_).
rewrite (H2 x0) in H3.
rewrite (InA_alt E.eq x0 (elements s)) in H3.
destruct H3 as (a,(Ha1,Ha2)).
rewrite (H _ _ Ha1).
apply H0; auto.
symmetry.
rewrite H0; intros.
destruct H1 as (_,H1).
apply H1; auto.
rewrite H2.
rewrite InA_alt. exists x0; split; auto with relations.
Qed.

Lemma exists_b : Proper (E.eq==>Logic.eq) f ->
  exists_ f s = existsb f (elements s).
Proof.
intros.
generalize (existsb_exists f (elements s))(exists_iff s H)(elements_iff s).
unfold Exists.
destruct (existsb f (elements s)); destruct (exists_ f s); auto; intros.
rewrite <- H1; intros.
destruct H0 as (H0,_).
destruct H0 as (a,(Ha1,Ha2)); auto.
exists a; split; auto.
rewrite H2; rewrite InA_alt; exists a; auto with relations.
symmetry.
rewrite H0.
destruct H1 as (_,H1).
destruct H1 as (a,(Ha1,Ha2)); auto.
rewrite (H2 a) in Ha1.
rewrite (InA_alt E.eq a (elements s)) in Ha1.
destruct Ha1 as (b,(Hb1,Hb2)).
exists b; auto.
rewrite <- (H _ _ Hb1); auto.
Qed.

End BoolSpec.

(** * Declarations of morphisms with respects to [E.eq] and [Equal] *)

Instance In_m : Proper (E.eq==>Equal==>iff) In.
Proof.
unfold Equal; intros x y H s s' H0.
rewrite (In_eq_iff s H); auto.
Qed.

Instance Empty_m : Proper (Equal==>iff) Empty.
Proof.
repeat red; unfold Empty; intros s s' E.
setoid_rewrite E; auto.
Qed.

Instance is_empty_m : Proper (Equal==>Logic.eq) is_empty.
Proof.
intros s s' H.
generalize (is_empty_iff s). rewrite H at 1. rewrite is_empty_iff.
destruct (is_empty s); destruct (is_empty s'); intuition.
Qed.

Instance mem_m : Proper (E.eq==>Equal==>Logic.eq) mem.
Proof.
intros x x' Hx s s' Hs.
generalize (mem_iff s x). rewrite Hs, Hx at 1; rewrite mem_iff.
destruct (mem x s), (mem x' s'); intuition.
Qed.

Instance singleton_m : Proper (E.eq==>Equal) singleton.
Proof.
intros x y H a. rewrite !singleton_iff, H; intuition.
Qed.

Instance add_m : Proper (E.eq==>Equal==>Equal) add.
Proof.
intros x x' Hx s s' Hs a. rewrite !add_iff, Hx, Hs; intuition.
Qed.

Instance remove_m : Proper (E.eq==>Equal==>Equal) remove.
Proof.
intros x x' Hx s s' Hs a. rewrite !remove_iff, Hx, Hs; intuition.
Qed.

Instance union_m : Proper (Equal==>Equal==>Equal) union.
Proof.
intros s1 s1' Hs1 s2 s2' Hs2 a. rewrite !union_iff, Hs1, Hs2; intuition.
Qed.

Instance inter_m : Proper (Equal==>Equal==>Equal) inter.
Proof.
intros s1 s1' Hs1 s2 s2' Hs2 a. rewrite !inter_iff, Hs1, Hs2; intuition.
Qed.

Instance diff_m : Proper (Equal==>Equal==>Equal) diff.
Proof.
intros s1 s1' Hs1 s2 s2' Hs2 a. rewrite !diff_iff, Hs1, Hs2; intuition.
Qed.

Instance Subset_m : Proper (Equal==>Equal==>iff) Subset.
Proof.
unfold Equal, Subset; firstorder.
Qed.

Instance subset_m : Proper (Equal==>Equal==>Logic.eq) subset.
Proof.
intros s1 s1' Hs1 s2 s2' Hs2.
generalize (subset_iff s1 s2). rewrite Hs1, Hs2 at 1. rewrite subset_iff.
destruct (subset s1 s2); destruct (subset s1' s2'); intuition.
Qed.

Instance equal_m : Proper (Equal==>Equal==>Logic.eq) equal.
Proof.
intros s1 s1' Hs1 s2 s2' Hs2.
generalize (equal_iff s1 s2). rewrite Hs1,Hs2 at 1. rewrite equal_iff.
destruct (equal s1 s2); destruct (equal s1' s2'); intuition.
Qed.

Instance SubsetSetoid : PreOrder Subset. (* reflexive + transitive *)
Proof. firstorder. Qed.

Definition Subset_refl := @PreOrder_Reflexive _ _ SubsetSetoid.
Definition Subset_trans := @PreOrder_Transitive _ _ SubsetSetoid.

Instance In_s_m : Morphisms.Proper (E.eq ==> Subset ++> impl) In | 1.
Proof.
  simpl_relation. eauto with set.
Qed.

Instance Empty_s_m : Proper (Subset-->impl) Empty.
Proof. firstorder. Qed.

Instance add_s_m : Proper (E.eq==>Subset++>Subset) add.
Proof.
intros x x' Hx s s' Hs a. rewrite !add_iff, Hx; intuition.
Qed.

Instance remove_s_m : Proper (E.eq==>Subset++>Subset) remove.
Proof.
intros x x' Hx s s' Hs a. rewrite !remove_iff, Hx; intuition.
Qed.

Instance union_s_m : Proper (Subset++>Subset++>Subset) union.
Proof.
intros s1 s1' Hs1 s2 s2' Hs2 a. rewrite !union_iff, Hs1, Hs2; intuition.
Qed.

Instance inter_s_m : Proper (Subset++>Subset++>Subset) inter.
Proof.
intros s1 s1' Hs1 s2 s2' Hs2 a. rewrite !inter_iff, Hs1, Hs2; intuition.
Qed.

Instance diff_s_m : Proper (Subset++>Subset-->Subset) diff.
Proof.
intros s1 s1' Hs1 s2 s2' Hs2 a. rewrite !diff_iff, Hs1, Hs2; intuition.
Qed.


(* [fold], [filter], [for_all], [exists_] and [partition] requires
  some knowledge on [f] in order to be known as morphisms. *)

Generalizable Variables f.

Instance filter_equal : forall `(Proper _ (E.eq==>Logic.eq) f),
 Proper (Equal==>Equal) (filter f).
Proof.
intros f Hf s s' Hs a. rewrite !filter_iff, Hs by auto; intuition.
Qed.

Instance filter_subset : forall `(Proper _ (E.eq==>Logic.eq) f),
 Proper (Subset==>Subset) (filter f).
Proof.
intros f Hf s s' Hs a. rewrite !filter_iff, Hs by auto; intuition.
Qed.

Lemma filter_ext : forall f f', Proper (E.eq==>Logic.eq) f -> (forall x, f x = f' x) ->
 forall s s', s[=]s' -> filter f s [=] filter f' s'.
Proof.
intros f f' Hf Hff' s s' Hss' x. rewrite 2 filter_iff; auto.
rewrite Hff', Hss'; intuition.
red; red; intros; rewrite <- 2 Hff'; auto.
Qed.

(* For [elements], [min_elt], [max_elt] and [choose], we would need setoid
   structures on [list elt] and [option elt]. *)

(* Later:
Add Morphism cardinal ; cardinal_m.
*)

End WFactsOn.

(** Now comes variants for self-contained weak sets and for full sets.
    For these variants, only one argument is necessary. Thanks to
    the subtyping [WS<=S], the [Facts] functor which is meant to be
    used on modules [(M:S)] can simply be an alias of [WFacts]. *)

Module WFacts (M:WSets) := WFactsOn M.E M.
Module Facts := WFacts.
