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

Hint Unfold transpose compat_op.
Hint Extern 1 (Setoid_Theory _ _) => constructor; congruence.

(** First, a functor for Weak Sets. Since the signature [WS] includes
    an EqualityType and not a stronger DecidableType, this functor
    should take two arguments in order to compensate this. *)

Module WProperties (Import E : DecidableType)(M : WSfun E).
  Module Import Dec := WDecide E M.
  Module Import FM := Dec.F (* FSetFacts.WFacts E M *).
  Import M.

  Lemma In_dec : forall x s, {In x s} + {~ In x s}.
  Proof.
  intros; generalize (mem_iff s x); case (mem x s); intuition.
  Qed.

  Definition Add x s s' := forall y, In y s' <-> E.eq x y \/ In y s.

  Lemma Add_Equal : forall x s s', Add x s s' <-> s' [=] add x s.
  Proof.
  unfold Add.
  split; intros.
  red; intros.
  rewrite H; clear H.
  fsetdec.
  fsetdec.
  Qed.
  
  Ltac expAdd := repeat rewrite Add_Equal.

  Section BasicProperties.

  Variable s s' s'' s1 s2 s3 : t.
  Variable x x' : elt.

  Lemma equal_refl : s[=]s.
  Proof. fsetdec. Qed.

  Lemma equal_sym : s[=]s' -> s'[=]s.
  Proof. fsetdec. Qed.

  Lemma equal_trans : s1[=]s2 -> s2[=]s3 -> s1[=]s3.
  Proof. fsetdec. Qed.

  Lemma subset_refl : s[<=]s. 
  Proof. fsetdec. Qed.

  Lemma subset_trans : s1[<=]s2 -> s2[<=]s3 -> s1[<=]s3.
  Proof. fsetdec. Qed.

  Lemma subset_antisym : s[<=]s' -> s'[<=]s -> s[=]s'.
  Proof. fsetdec. Qed.

  Lemma subset_equal : s[=]s' -> s[<=]s'.
  Proof. fsetdec. Qed.

  Lemma subset_empty : empty[<=]s.
  Proof. fsetdec. Qed.

  Lemma subset_remove_3 : s1[<=]s2 -> remove x s1 [<=] s2.
  Proof. fsetdec. Qed.

  Lemma subset_diff : s1[<=]s3 -> diff s1 s2 [<=] s3.
  Proof. fsetdec. Qed.
 
  Lemma subset_add_3 : In x s2 -> s1[<=]s2 -> add x s1 [<=] s2.
  Proof. fsetdec. Qed.

  Lemma subset_add_2 : s1[<=]s2 -> s1[<=] add x s2.
  Proof. fsetdec. Qed.

  Lemma in_subset : In x s1 -> s1[<=]s2 -> In x s2.
  Proof. fsetdec. Qed.
 
  Lemma double_inclusion : s1[=]s2 <-> s1[<=]s2 /\ s2[<=]s1.
  Proof. intuition fsetdec. Qed.

  Lemma empty_is_empty_1 : Empty s -> s[=]empty.
  Proof. fsetdec. Qed.

  Lemma empty_is_empty_2 : s[=]empty -> Empty s.
  Proof. fsetdec. Qed.

  Lemma add_equal : In x s -> add x s [=] s.
  Proof. fsetdec. Qed.
 
  Lemma add_add : add x (add x' s) [=] add x' (add x s).
  Proof. fsetdec. Qed.

  Lemma remove_equal : ~ In x s -> remove x s [=] s.
  Proof. fsetdec. Qed.

  Lemma Equal_remove : s[=]s' -> remove x s [=] remove x s'.
  Proof. fsetdec. Qed.

  Lemma add_remove : In x s -> add x (remove x s) [=] s.
  Proof. fsetdec. Qed.

  Lemma remove_add : ~In x s -> remove x (add x s) [=] s.
  Proof. fsetdec. Qed.

  Lemma singleton_equal_add : singleton x [=] add x empty.
  Proof. fsetdec. Qed.

  Lemma union_sym : union s s' [=] union s' s.
  Proof. fsetdec. Qed.

  Lemma union_subset_equal : s[<=]s' -> union s s' [=] s'.
  Proof. fsetdec. Qed.

  Lemma union_equal_1 : s[=]s' -> union s s'' [=] union s' s''.
  Proof. fsetdec. Qed.

  Lemma union_equal_2 : s'[=]s'' -> union s s' [=] union s s''.
  Proof. fsetdec. Qed.

  Lemma union_assoc : union (union s s') s'' [=] union s (union s' s'').
  Proof. fsetdec. Qed.

  Lemma add_union_singleton : add x s [=] union (singleton x) s.
  Proof. fsetdec. Qed.

  Lemma union_add : union (add x s) s' [=] add x (union s s').
  Proof. fsetdec. Qed.

  Lemma union_remove_add_1 : 
   union (remove x s) (add x s') [=] union (add x s) (remove x s').
  Proof. fsetdec. Qed.

  Lemma union_remove_add_2 : In x s -> 
   union (remove x s) (add x s') [=] union s s'.
  Proof. fsetdec. Qed.

  Lemma union_subset_1 : s [<=] union s s'.
  Proof. fsetdec. Qed.

  Lemma union_subset_2 : s' [<=] union s s'.
  Proof. fsetdec. Qed.

  Lemma union_subset_3 : s[<=]s'' -> s'[<=]s'' -> union s s' [<=] s''.
  Proof. fsetdec. Qed.

  Lemma union_subset_4 : s[<=]s' -> union s s'' [<=] union s' s''.
  Proof. fsetdec. Qed. 

  Lemma union_subset_5 : s[<=]s' -> union s'' s [<=] union s'' s'.
  Proof. fsetdec. Qed. 

  Lemma empty_union_1 : Empty s -> union s s' [=] s'.
  Proof. fsetdec. Qed.

  Lemma empty_union_2 : Empty s -> union s' s [=] s'.
  Proof. fsetdec. Qed.

  Lemma not_in_union : ~In x s -> ~In x s' -> ~In x (union s s'). 
  Proof. fsetdec. Qed.

  Lemma inter_sym : inter s s' [=] inter s' s.
  Proof. fsetdec. Qed.

  Lemma inter_subset_equal : s[<=]s' -> inter s s' [=] s.
  Proof. fsetdec. Qed.

  Lemma inter_equal_1 : s[=]s' -> inter s s'' [=] inter s' s''.
  Proof. fsetdec. Qed.

  Lemma inter_equal_2 : s'[=]s'' -> inter s s' [=] inter s s''.
  Proof. fsetdec. Qed.

  Lemma inter_assoc : inter (inter s s') s'' [=] inter s (inter s' s'').
  Proof. fsetdec. Qed.

  Lemma union_inter_1 : inter (union s s') s'' [=] union (inter s s'') (inter s' s'').
  Proof. fsetdec. Qed.

  Lemma union_inter_2 : union (inter s s') s'' [=] inter (union s s'') (union s' s'').
  Proof. fsetdec. Qed.

  Lemma inter_add_1 : In x s' -> inter (add x s) s' [=] add x (inter s s').
  Proof. fsetdec. Qed.

  Lemma inter_add_2 : ~ In x s' -> inter (add x s) s' [=] inter s s'.
  Proof. fsetdec. Qed.

  Lemma empty_inter_1 : Empty s -> Empty (inter s s').
  Proof. fsetdec. Qed.

  Lemma empty_inter_2 : Empty s' -> Empty (inter s s').
  Proof. fsetdec. Qed.

  Lemma inter_subset_1 : inter s s' [<=] s.
  Proof. fsetdec. Qed.

  Lemma inter_subset_2 : inter s s' [<=] s'.
  Proof. fsetdec. Qed.

  Lemma inter_subset_3 :
   s''[<=]s -> s''[<=]s' -> s''[<=] inter s s'.
  Proof. fsetdec. Qed.

  Lemma empty_diff_1 : Empty s -> Empty (diff s s'). 
  Proof. fsetdec. Qed.

  Lemma empty_diff_2 : Empty s -> diff s' s [=] s'.
  Proof. fsetdec. Qed.

  Lemma diff_subset : diff s s' [<=] s.
  Proof. fsetdec. Qed.

  Lemma diff_subset_equal : s[<=]s' -> diff s s' [=] empty.
  Proof. fsetdec. Qed.

  Lemma remove_diff_singleton :
   remove x s [=] diff s (singleton x).
  Proof. fsetdec. Qed.

  Lemma diff_inter_empty : inter (diff s s') (inter s s') [=] empty. 
  Proof. fsetdec. Qed.

  Lemma diff_inter_all : union (diff s s') (inter s s') [=] s.
  Proof. fsetdec. Qed.

  Lemma Add_add : Add x s (add x s).
  Proof. expAdd; fsetdec. Qed.

  Lemma Add_remove : In x s -> Add x (remove x s) s. 
  Proof. expAdd; fsetdec. Qed.

  Lemma union_Add : Add x s s' -> Add x (union s s'') (union s' s'').
  Proof. expAdd; fsetdec. Qed. 

  Lemma inter_Add :
   In x s'' -> Add x s s' -> Add x (inter s s'') (inter s' s'').
  Proof. expAdd; fsetdec. Qed. 

  Lemma union_Equal :
   In x s'' -> Add x s s' -> union s s'' [=] union s' s''.
  Proof. expAdd; fsetdec. Qed. 

  Lemma inter_Add_2 :
   ~In x s'' -> Add x s s' -> inter s s'' [=] inter s' s''.
  Proof. expAdd; fsetdec. Qed.

  End BasicProperties.

  Hint Immediate equal_sym add_remove remove_add union_sym inter_sym: set.
  Hint Resolve equal_refl equal_trans subset_refl subset_equal subset_antisym 
    subset_trans subset_empty subset_remove_3 subset_diff subset_add_3 
    subset_add_2 in_subset empty_is_empty_1 empty_is_empty_2 add_equal
    remove_equal singleton_equal_add union_subset_equal union_equal_1 
    union_equal_2 union_assoc add_union_singleton union_add union_subset_1 
    union_subset_2 union_subset_3 inter_subset_equal inter_equal_1 inter_equal_2
    inter_assoc union_inter_1 union_inter_2 inter_add_1 inter_add_2
    empty_inter_1 empty_inter_2 empty_union_1 empty_union_2 empty_diff_1 
    empty_diff_2 union_Add inter_Add union_Equal inter_Add_2 not_in_union 
    inter_subset_1 inter_subset_2 inter_subset_3 diff_subset diff_subset_equal 
    remove_diff_singleton diff_inter_empty diff_inter_all Add_add Add_remove
    Equal_remove add_add : set.

  (** * Properties of elements *)

  Lemma elements_Empty : forall s, Empty s <-> elements s = nil.
  Proof.
  intros.
  unfold Empty.
  split; intros.
  assert (forall a, ~ List.In a (elements s)).
   red; intros.
   apply (H a).
   rewrite elements_iff.
   rewrite InA_alt; exists a; auto.
  destruct (elements s); auto.
  elim (H0 e); simpl; auto.
  red; intros.
  rewrite elements_iff in H0.
  rewrite InA_alt in H0; destruct H0.
  rewrite H in H0; destruct H0 as (_,H0); inversion H0.
  Qed.

  Lemma elements_empty : elements empty = nil.
  Proof.
  rewrite <-elements_Empty; auto with set.
  Qed.

  (** * Alternative (weaker) specifications for [fold] *)

  Section Old_Spec_Now_Properties. 

  Notation NoDup := (NoDupA E.eq).

  (** When [FSets] was first designed, the order in which Ocaml's [Set.fold]
        takes the set elements was unspecified. This specification reflects this fact: 
  *)

  Lemma fold_0 : 
      forall s (A : Type) (i : A) (f : elt -> A -> A),
      exists l : list elt,
        NoDup l /\
        (forall x : elt, In x s <-> InA E.eq x l) /\
        fold f s i = fold_right f i l.
  Proof.
  intros; exists (rev (elements s)); split.
  apply NoDupA_rev; auto with set.
  exact E.eq_trans.
  split; intros.
  rewrite elements_iff; do 2 rewrite InA_alt.
  split; destruct 1; generalize (In_rev (elements s) x0); exists x0; intuition.
  rewrite fold_left_rev_right.
  apply fold_1.
  Qed.

  (** An alternate (and previous) specification for [fold] was based on 
      the recursive structure of a set. It is now lemmas [fold_1] and 
      [fold_2]. *)

  Lemma fold_1 :
   forall s (A : Type) (eqA : A -> A -> Prop) 
     (st : Setoid_Theory A eqA) (i : A) (f : elt -> A -> A),
   Empty s -> eqA (fold f s i) i.
  Proof.
  unfold Empty; intros; destruct (fold_0 s i f) as (l,(H1, (H2, H3))).
  rewrite H3; clear H3.
  generalize H H2; clear H H2; case l; simpl; intros.
  refl_st.
  elim (H e).
  elim (H2 e); intuition. 
  Qed.

  Lemma fold_2 :
   forall s s' x (A : Type) (eqA : A -> A -> Prop)
     (st : Setoid_Theory A eqA) (i : A) (f : elt -> A -> A),
   compat_op E.eq eqA f ->
   transpose eqA f ->
   ~ In x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
  Proof.
  intros; destruct (fold_0 s i f) as (l,(Hl, (Hl1, Hl2))); 
    destruct (fold_0 s' i f) as (l',(Hl', (Hl'1, Hl'2))).
  rewrite Hl2; rewrite Hl'2; clear Hl2 Hl'2.
  apply fold_right_add with (eqA:=E.eq)(eqB:=eqA); auto.
  eauto.
  rewrite <- Hl1; auto.
  intros a; rewrite InA_cons; rewrite <- Hl1; rewrite <- Hl'1; 
   rewrite (H2 a); intuition.
  Qed.

  (** In fact, [fold] on empty sets is more than equivalent to 
      the initial element, it is Leibniz-equal to it. *)

  Lemma fold_1b :
   forall s (A : Type)(i : A) (f : elt -> A -> A),
   Empty s -> (fold f s i) = i.
  Proof.
  intros.
  rewrite M.fold_1.
  rewrite elements_Empty in H; rewrite H; simpl; auto.
  Qed.

  (** Similar specifications for [cardinal]. *)

  Lemma cardinal_fold : forall s, cardinal s = fold (fun _ => S) s 0.
  Proof.
  intros; rewrite cardinal_1; rewrite M.fold_1.
  symmetry; apply fold_left_length; auto.
  Qed.

  Lemma cardinal_0 :
     forall s, exists l : list elt,
        NoDupA E.eq l /\
        (forall x : elt, In x s <-> InA E.eq x l) /\ 
        cardinal s = length l.
  Proof. 
  intros; exists (elements s); intuition; apply cardinal_1.
  Qed.

  Lemma cardinal_1 : forall s, Empty s -> cardinal s = 0.
  Proof.
  intros; rewrite cardinal_fold; apply fold_1; auto.
  Qed.

  Lemma cardinal_2 :
    forall s s' x, ~ In x s -> Add x s s' -> cardinal s' = S (cardinal s).
  Proof.
  intros; do 2 rewrite cardinal_fold.
  change S with ((fun _ => S) x).
  apply fold_2; auto.
  Qed.

  End Old_Spec_Now_Properties.

  (** * Induction principle over sets *)

  Lemma cardinal_Empty : forall s, Empty s <-> cardinal s = 0.
  Proof.
  intros.
  rewrite elements_Empty, M.cardinal_1.
  destruct (elements s); intuition; discriminate.
  Qed.

  Lemma cardinal_inv_1 : forall s, cardinal s = 0 -> Empty s. 
  Proof.
  intros; rewrite cardinal_Empty; auto. 
  Qed.
  Hint Resolve cardinal_inv_1.
 
  Lemma cardinal_inv_2 :
   forall s n, cardinal s = S n -> { x : elt | In x s }.
  Proof. 
  intros; rewrite M.cardinal_1 in H.
  generalize (elements_2 (s:=s)).
  destruct (elements s); try discriminate. 
  exists e; auto.
  Qed.

  Lemma cardinal_inv_2b :
   forall s, cardinal s <> 0 -> { x : elt | In x s }.
  Proof.
  intro; generalize (@cardinal_inv_2 s); destruct cardinal; 
   [intuition|eauto].
  Qed.

  Lemma Equal_cardinal : forall s s', s[=]s' -> cardinal s = cardinal s'.
  Proof. 
  symmetry.
  remember (cardinal s) as n; symmetry in Heqn; revert s s' Heqn H.
  induction n; intros.
  apply cardinal_1; rewrite <- H; auto.
  destruct (cardinal_inv_2 Heqn) as (x,H2).
  revert Heqn.
  rewrite (cardinal_2 (s:=remove x s) (s':=s) (x:=x)); auto with set.
  rewrite (cardinal_2 (s:=remove x s') (s':=s') (x:=x)); eauto with set.
  Qed.    

  Add Morphism cardinal : cardinal_m.
  Proof.
  exact Equal_cardinal.
  Qed.

  Hint Resolve Add_add Add_remove Equal_remove cardinal_inv_1 Equal_cardinal.

  Lemma set_induction :
   forall P : t -> Type,
   (forall s : t, Empty s -> P s) ->
   (forall s s' : t, P s -> forall x : elt, ~In x s -> Add x s s' -> P s') ->
   forall s : t, P s.
  Proof.
  intros; remember (cardinal s) as n; revert s Heqn; induction n; intros; auto.
  destruct (cardinal_inv_2 (sym_eq Heqn)) as (x,H0). 
  apply X0 with (remove x s) x; auto with set.
  apply IHn; auto.
  assert (S n = S (cardinal (remove x s))).
    rewrite Heqn; apply cardinal_2 with x; auto with set.
  inversion H; auto.
  Qed.

  (** Other properties of [fold]. *)

  Section Fold. 
  Variables (A:Type)(eqA:A->A->Prop)(st:Setoid_Theory _ eqA).
  Variables (f:elt->A->A)(Comp:compat_op E.eq eqA f)(Ass:transpose eqA f).

  Section Fold_1. 
  Variable i i':A.

  Lemma fold_empty : (fold f empty i) = i.
  Proof. 
  apply fold_1b; auto with set.
  Qed.

  Lemma fold_equal : 
   forall s s', s[=]s' -> eqA (fold f s i) (fold f s' i).
  Proof. 
  intros s; pattern s; apply set_induction; clear s; intros.
  trans_st i.
  apply fold_1; auto.
  sym_st; apply fold_1; auto.
  rewrite <- H0; auto.
  trans_st (f x (fold f s i)).
  apply fold_2 with (eqA := eqA); auto.
  sym_st; apply fold_2 with (eqA := eqA); auto.
  unfold Add in *; intros.
  rewrite <- H2; auto.
  Qed.
   
  Lemma fold_add : forall s x, ~In x s -> 
   eqA (fold f (add x s) i) (f x (fold f s i)).
  Proof. 
  intros; apply fold_2 with (eqA := eqA); auto.
  Qed.

  Lemma add_fold : forall s x, In x s -> 
   eqA (fold f (add x s) i) (fold f s i).
  Proof.
  intros; apply fold_equal; auto with set.
  Qed.

  Lemma remove_fold_1: forall s x, In x s -> 
   eqA (f x (fold f (remove x s) i)) (fold f s i).
  Proof.
  intros.
  sym_st.
  apply fold_2 with (eqA:=eqA); auto with set.
  Qed.

  Lemma remove_fold_2: forall s x, ~In x s -> 
   eqA (fold f (remove x s) i) (fold f s i).
  Proof.
  intros.
  apply fold_equal; auto with set.
  Qed.

  Lemma fold_commutes : forall s x, 
   eqA (fold f s (f x i)) (f x (fold f s i)).
  Proof.
  intros; pattern s; apply set_induction; clear s; intros.
  trans_st (f x i).
  apply fold_1; auto.
  sym_st.
  apply Comp; auto.
  apply fold_1; auto.
  trans_st (f x0 (fold f s (f x i))).
  apply fold_2 with (eqA:=eqA); auto.
  trans_st (f x0 (f x (fold f s i))).
  trans_st (f x (f x0 (fold f s i))).
  apply Comp; auto.
  sym_st.
  apply fold_2 with (eqA:=eqA); auto.
  Qed.

  Lemma fold_init : forall s, eqA i i' -> 
   eqA (fold f s i) (fold f s i').
  Proof. 
  intros; pattern s; apply set_induction; clear s; intros.
  trans_st i.
  apply fold_1; auto.
  trans_st i'.
  sym_st; apply fold_1; auto.
  trans_st (f x (fold f s i)).
  apply fold_2 with (eqA:=eqA); auto.
  trans_st (f x (fold f s i')).
  sym_st; apply fold_2 with (eqA:=eqA); auto.
  Qed.

  End Fold_1.
  Section Fold_2.
  Variable i:A.

  Lemma fold_union_inter : forall s s',
   eqA (fold f (union s s') (fold f (inter s s') i))
       (fold f s (fold f s' i)).
  Proof.
  intros; pattern s; apply set_induction; clear s; intros.
  trans_st (fold f s' (fold f (inter s s') i)).
  apply fold_equal; auto with set.
  trans_st (fold f s' i).
  apply fold_init; auto.
  apply fold_1; auto with set.
  sym_st; apply fold_1; auto.
  rename s'0 into s''.
  destruct (In_dec x s').
  (* In x s' *)   
  trans_st (fold f (union s'' s') (f x (fold f (inter s s') i))); auto with set.
  apply fold_init; auto.
  apply fold_2 with (eqA:=eqA); auto with set.
  rewrite inter_iff; intuition.
  trans_st (f x (fold f s (fold f s' i))).
  trans_st (fold f (union s s') (f x (fold f (inter s s') i))).
  apply fold_equal; auto.
  apply equal_sym; apply union_Equal with x; auto with set.
  trans_st (f x (fold f (union s s') (fold f (inter s s') i))).
  apply fold_commutes; auto.
  sym_st; apply fold_2 with (eqA:=eqA); auto.
  (* ~(In x s') *)
  trans_st (f x (fold f (union s s') (fold f (inter s'' s') i))).
  apply fold_2 with (eqA:=eqA); auto with set.
  trans_st (f x (fold f (union s s') (fold f (inter s s') i))).
  apply Comp;auto.
  apply fold_init;auto.
  apply fold_equal;auto.
  apply equal_sym; apply inter_Add_2 with x; auto with set.
  trans_st (f x (fold f s (fold f s' i))).
  sym_st; apply fold_2 with (eqA:=eqA); auto.
  Qed.

  End Fold_2.
  Section Fold_3.
  Variable i:A.

  Lemma fold_diff_inter : forall s s', 
   eqA (fold f (diff s s') (fold f (inter s s') i)) (fold f s i).
  Proof.
  intros.
  trans_st (fold f (union (diff s s') (inter s s')) 
              (fold f (inter (diff s s') (inter s s')) i)).
  sym_st; apply fold_union_inter; auto.
  trans_st (fold f s (fold f (inter (diff s s') (inter s s')) i)).
  apply fold_equal; auto with set.
  apply fold_init; auto.
  apply fold_1; auto with set.
  Qed.

  Lemma fold_union: forall s s', 
   (forall x, ~(In x s/\In x s')) ->
   eqA (fold f (union s s') i) (fold f s (fold f s' i)).
  Proof.
  intros.
  trans_st (fold f (union s s') (fold f (inter s s') i)).
  apply fold_init; auto.
  sym_st; apply fold_1; auto with set.
  unfold Empty; intro a; generalize (H a); set_iff; tauto.
  apply fold_union_inter; auto.
  Qed.

  End Fold_3.
  End Fold.

  Lemma fold_plus :
   forall s p, fold (fun _ => S) s p = fold (fun _ => S) s 0 + p.
  Proof.
  assert (st := gen_st nat).
  assert (fe : compat_op E.eq (@Logic.eq _) (fun _ => S)) by (unfold compat_op; auto). 
  assert (fp : transpose (@Logic.eq _) (fun _:elt => S)) by (unfold transpose; auto).
  intros s p; pattern s; apply set_induction; clear s; intros.
  rewrite (fold_1 st p (fun _ => S) H).
  rewrite (fold_1 st 0 (fun _ => S) H); trivial.
  assert (forall p s', Add x s s' -> fold (fun _ => S) s' p = S (fold (fun _ => S) s p)).
   change S with ((fun _ => S) x).  
   intros; apply fold_2; auto.
  rewrite H2; auto.
  rewrite (H2 0); auto.
  rewrite H.
  simpl; auto.
  Qed.

  (** more properties of [cardinal] *)

  Lemma empty_cardinal : cardinal empty = 0.
  Proof.
  rewrite cardinal_fold; apply fold_1; auto with set.
  Qed.

  Hint Immediate empty_cardinal cardinal_1 : set.

  Lemma singleton_cardinal : forall x, cardinal (singleton x) = 1.
  Proof.
  intros.
  rewrite (singleton_equal_add x).
  replace 0 with (cardinal empty); auto with set.
  apply cardinal_2 with x; auto with set.
  Qed.

  Hint Resolve singleton_cardinal: set.

  Lemma diff_inter_cardinal :
   forall s s', cardinal (diff s s') + cardinal (inter s s') = cardinal s .
  Proof.
  intros; do 3 rewrite cardinal_fold.
  rewrite <- fold_plus.
  apply fold_diff_inter with (eqA:=@Logic.eq nat); auto.
  Qed.

  Lemma union_cardinal: 
   forall s s', (forall x, ~(In x s/\In x s')) -> 
   cardinal (union s s')=cardinal s+cardinal s'.
  Proof.
  intros; do 3 rewrite cardinal_fold.
  rewrite <- fold_plus.
  apply fold_union; auto.
  Qed.

  Lemma subset_cardinal : 
   forall s s', s[<=]s' -> cardinal s <= cardinal s' .
  Proof.
  intros.
  rewrite <- (diff_inter_cardinal s' s).
  rewrite (inter_sym s' s).
  rewrite (inter_subset_equal H); auto with arith.
  Qed.

  Lemma subset_cardinal_lt : 
   forall s s' x, s[<=]s' -> In x s' -> ~In x s -> cardinal s < cardinal s'.
  Proof. 
  intros.
  rewrite <- (diff_inter_cardinal s' s).
  rewrite (inter_sym s' s).
  rewrite (inter_subset_equal H).
  generalize (@cardinal_inv_1 (diff s' s)).
  destruct (cardinal (diff s' s)).
  intro H2; destruct (H2 (refl_equal _) x).
  set_iff; auto.
  intros _.
  change (0 + cardinal s < S n + cardinal s).
  apply Plus.plus_lt_le_compat; auto with arith.
  Qed. 

  Theorem union_inter_cardinal :
   forall s s', cardinal (union s s') + cardinal (inter s s')  = cardinal s  + cardinal s' .
  Proof.
  intros.
  do 4 rewrite cardinal_fold.
  do 2 rewrite <- fold_plus.
  apply fold_union_inter with (eqA:=@Logic.eq nat); auto.
  Qed.

  Lemma union_cardinal_inter : 
   forall s s', cardinal (union s s') = cardinal s + cardinal s' - cardinal (inter s s').
  Proof.
  intros.
  rewrite <- union_inter_cardinal.
  rewrite Plus.plus_comm.
  auto with arith.
  Qed.

  Lemma union_cardinal_le : 
   forall s s', cardinal (union s s') <= cardinal s  + cardinal s'.
  Proof.
   intros; generalize (union_inter_cardinal s s').
   intros; rewrite <- H; auto with arith.
  Qed.

  Lemma add_cardinal_1 : 
   forall s x, In x s -> cardinal (add x s) = cardinal s.
  Proof.
  auto with set.  
  Qed.

  Lemma add_cardinal_2 :
   forall s x, ~In x s -> cardinal (add x s) = S (cardinal s).
  Proof.
  intros.
  do 2 rewrite cardinal_fold.
  change S with ((fun _ => S) x);
   apply fold_add with (eqA:=@Logic.eq nat); auto.
  Qed.

  Lemma remove_cardinal_1 :
   forall s x, In x s -> S (cardinal (remove x s)) = cardinal s.
  Proof.
  intros.
  do 2 rewrite cardinal_fold.
  change S with ((fun _ =>S) x).
  apply remove_fold_1 with (eqA:=@Logic.eq nat); auto.
  Qed.

  Lemma remove_cardinal_2 : 
   forall s x, ~In x s -> cardinal (remove x s) = cardinal s.
  Proof. 
  auto with set.
  Qed.

  Hint Resolve subset_cardinal union_cardinal add_cardinal_1 add_cardinal_2.

End WProperties.


(** A clone of [WProperties] working on full sets. *)

Module Properties (M:S).
  Module D := OT_as_DT M.E.
  Include WProperties D M.
End Properties.


(** Now comes some properties specific to the element ordering, 
    invalid for Weak Sets. *)

Module OrdProperties (M:S).
  Module ME:=OrderedTypeFacts(M.E).
  Module Import P := Properties M.
  Import FM.
  Import M.E.
  Import M.

  (** First, a specialized version of SortA_equivlistA_eqlistA: *)
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
  rewrite ME.Inf_alt by (apply (@filter_sort _ E.eq); eauto with set).
  intros.
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
   forall s s' x (A : Type) (eqA : A -> A -> Prop)
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
   forall s s' x (A : Type) (eqA : A -> A -> Prop)
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
  Variables (A:Type)(eqA:A->A->Prop)(st:Setoid_Theory _ eqA).
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

  (** An alternative version of [choose_3] *)

  Lemma choose_equal : forall s s', Equal s s' -> 
    match choose s, choose s' with  
      | Some x, Some x' => E.eq x x'
      | None, None => True
      | _, _ => False
     end.
  Proof.
  intros s s' H; 
  generalize (@choose_1 s)(@choose_2 s)
             (@choose_1 s')(@choose_2 s')(@choose_3 s s'); 
  destruct (choose s); destruct (choose s'); simpl; intuition.
  apply H5 with e; rewrite <-H; auto.
  apply H5 with e; rewrite H; auto.
  Qed.

End OrdProperties.
