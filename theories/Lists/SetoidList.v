(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Export List.
Require Export Sorting.
Require Export Setoid.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Logical relations over lists with respect to a setoid equality 
      or ordering. *) 

(** This can be seen as a complement of predicate [lelistA] and [sort] 
    found in [Sorting]. *)

Section Type_with_equality.
Variable A : Type.
Variable eqA : A -> A -> Prop. 

(** Being in a list modulo an equality relation over type [A]. *)

Inductive InA (x : A) : list A -> Prop :=
  | InA_cons_hd : forall y l, eqA x y -> InA x (y :: l)
  | InA_cons_tl : forall y l, InA x l -> InA x (y :: l).

Hint Constructors InA.

Lemma InA_cons : forall x y l, InA x (y::l) <-> eqA x y \/ InA x l.
Proof.
 intuition.
 inversion H; auto.
Qed.

Lemma InA_nil : forall x, InA x nil <-> False.
Proof.
 intuition.
 inversion H.
Qed.

(** An alternative definition of [InA]. *)

Lemma InA_alt : forall x l, InA x l <-> exists y, eqA x y /\ In y l.
Proof. 
 induction l; intuition.
 inversion H.
 firstorder.
 inversion H1; firstorder.
 firstorder; subst; auto.
Qed.

(** A list without redundancy modulo the equality over [A]. *)

Inductive NoDupA : list A -> Prop :=
  | NoDupA_nil : NoDupA nil
  | NoDupA_cons : forall x l, ~ InA x l -> NoDupA l -> NoDupA (x::l).

Hint Constructors NoDupA.

(** lists with same elements modulo [eqA] *)

Definition equivlistA l l' := forall x, InA x l <-> InA x l'.

(** lists with same elements modulo [eqA] at the same place *)

Inductive eqlistA : list A -> list A -> Prop :=
  | eqlistA_nil : eqlistA nil nil
  | eqlistA_cons : forall x x' l l',
      eqA x x' -> eqlistA l l' -> eqlistA (x::l) (x'::l').

Hint Constructors eqlistA.

(** Compatibility of a  boolean function with respect to an equality. *)

Definition compat_bool (f : A->bool) := forall x y, eqA x y -> f x = f y.

(** Compatibility of a function upon natural numbers. *)

Definition compat_nat (f : A->nat) := forall x y, eqA x y -> f x = f y.

(** Compatibility of a predicate with respect to an equality. *)

Definition compat_P (P : A->Prop) := forall x y, eqA x y -> P x -> P y.

(** Results concerning lists modulo [eqA] *)

Hypothesis eqA_refl : forall x, eqA x x.
Hypothesis eqA_sym : forall x y, eqA x y -> eqA y x.
Hypothesis eqA_trans : forall x y z, eqA x y -> eqA y z -> eqA x z.

Hint Resolve eqA_refl eqA_trans.
Hint Immediate eqA_sym.

Lemma InA_eqA : forall l x y, eqA x y -> InA x l -> InA y l.
Proof. 
 intros s x y.
 do 2 rewrite InA_alt.
 intros H (z,(U,V)).  
 exists z; split; eauto.
Qed.
Hint Immediate InA_eqA.

Lemma In_InA : forall l x, In x l -> InA x l.
Proof.
 simple induction l; simpl in |- *; intuition.
 subst; auto.  
Qed.
Hint Resolve In_InA.

Lemma InA_split : forall l x, InA x l -> 
 exists l1, exists y, exists l2, 
 eqA x y /\ l = l1++y::l2.
Proof.
induction l; inversion_clear 1.
exists (@nil A); exists a; exists l; auto.
destruct (IHl x H0) as (l1,(y,(l2,(H1,H2)))).
exists (a::l1); exists y; exists l2; auto.
split; simpl; f_equal; auto.
Qed.

Lemma InA_app : forall l1 l2 x,
 InA x (l1 ++ l2) -> InA x l1 \/ InA x l2.
Proof.
 induction l1; simpl in *; intuition.
 inversion_clear H; auto.
 elim (IHl1 l2 x H0); auto.
Qed.

Lemma InA_app_iff : forall l1 l2 x,
 InA x (l1 ++ l2) <-> InA x l1 \/ InA x l2.
Proof.
 split.
 apply InA_app.
 destruct 1; generalize H; do 2 rewrite InA_alt.
 destruct 1 as (y,(H1,H2)); exists y; split; auto.
 apply in_or_app; auto.
 destruct 1 as (y,(H1,H2)); exists y; split; auto.
 apply in_or_app; auto.
Qed.

Lemma InA_rev : forall p m, 
 InA p (rev m) <-> InA p m.
Proof.
 intros; do 2 rewrite InA_alt.
 split; intros (y,H); exists y; intuition.
 rewrite In_rev; auto.
 rewrite <- In_rev; auto.
Qed.

(** Results concerning lists modulo [eqA] and [ltA] *)

Variable ltA : A -> A -> Prop.

Hypothesis ltA_trans : forall x y z, ltA x y -> ltA y z -> ltA x z.
Hypothesis ltA_not_eqA : forall x y, ltA x y -> ~ eqA x y.
Hypothesis ltA_eqA : forall x y z, ltA x y -> eqA y z -> ltA x z.
Hypothesis eqA_ltA : forall x y z, eqA x y -> ltA y z -> ltA x z.

Hint Resolve ltA_trans.
Hint Immediate ltA_eqA eqA_ltA.

Notation InfA:=(lelistA ltA).
Notation SortA:=(sort ltA).

Hint Constructors lelistA sort.

Lemma InfA_ltA :
 forall l x y, ltA x y -> InfA y l -> InfA x l.
Proof.
 destruct l; constructor; inversion_clear H0; 
 eapply ltA_trans; eauto.
Qed.
 
Lemma InfA_eqA :
 forall l x y, eqA x y -> InfA y l -> InfA x l.
Proof.
 intro s; case s; constructor; inversion_clear H0; eauto.
Qed.
Hint Immediate InfA_ltA InfA_eqA. 

Lemma SortA_InfA_InA :
 forall l x a, SortA l -> InfA a l -> InA x l -> ltA a x.
Proof. 
 simple induction l.
 intros; inversion H1.
 intros.
 inversion_clear H0; inversion_clear H1; inversion_clear H2.
 eapply ltA_eqA; eauto.
 eauto.
Qed.
  
Lemma In_InfA :
 forall l x, (forall y, In y l -> ltA x y) -> InfA x l.
Proof.
 simple induction l; simpl in |- *; intros; constructor; auto.
Qed.
 
Lemma InA_InfA :
 forall l x, (forall y, InA y l -> ltA x y) -> InfA x l.
Proof.
 simple induction l; simpl in |- *; intros; constructor; auto.
Qed.

(* In fact, this may be used as an alternative definition for InfA: *)

Lemma InfA_alt : 
 forall l x, SortA l -> (InfA x l <-> (forall y, InA y l -> ltA x y)).
Proof. 
split.
intros; eapply SortA_InfA_InA; eauto.
apply InA_InfA.
Qed.

Lemma InfA_app : forall l1 l2 a, InfA a l1 -> InfA a l2 -> InfA a (l1++l2).
Proof.
 induction l1; simpl; auto.
 inversion_clear 1; auto.
Qed.

Lemma SortA_app :
 forall l1 l2, SortA l1 -> SortA l2 ->
 (forall x y, InA x l1 -> InA y l2 -> ltA x y) ->
 SortA (l1 ++ l2).
Proof.
 induction l1; simpl in *; intuition.
 inversion_clear H.
 constructor; auto.
 apply InfA_app; auto.
 destruct l2; auto.
Qed.

Section NoDupA.

Lemma SortA_NoDupA : forall l, SortA l -> NoDupA l.
Proof.
 simple induction l; auto.
 intros x l' H H0.
 inversion_clear H0.
 constructor; auto.  
 intro.
 assert (ltA x x) by (eapply SortA_InfA_InA; eauto).
 elim (ltA_not_eqA H3); auto.
Qed.

Lemma NoDupA_app : forall l l', NoDupA l -> NoDupA l' -> 
  (forall x, InA x l -> InA x l' -> False) -> 
  NoDupA (l++l').
Proof.
induction l; simpl; auto; intros.
inversion_clear H.
constructor.
rewrite InA_alt; intros (y,(H4,H5)).
destruct (in_app_or _ _ _ H5).
elim H2.
rewrite InA_alt.
exists y; auto.
apply (H1 a).
auto.
rewrite InA_alt.
exists y; auto.
apply IHl; auto.
intros.
apply (H1 x); auto.
Qed.

Lemma NoDupA_rev : forall l, NoDupA l -> NoDupA (rev l).
Proof.
induction l.
simpl; auto.
simpl; intros.
inversion_clear H.
apply NoDupA_app; auto.
constructor; auto.
intro H2; inversion H2.
intros x.
rewrite InA_alt.
intros (x1,(H2,H3)).
inversion_clear 1.
destruct H0.
apply InA_eqA with x1; eauto.
apply In_InA.
rewrite In_rev; auto.
inversion H4.
Qed.

Lemma NoDupA_split : forall l l' x, NoDupA (l++x::l') -> NoDupA (l++l').
Proof.
 induction l; simpl in *; inversion_clear 1; auto.
 constructor; eauto.
 contradict H0.
 rewrite InA_app_iff in *; rewrite InA_cons; intuition.
Qed.

Lemma NoDupA_swap : forall l l' x, NoDupA (l++x::l') -> NoDupA (x::l++l').
Proof.
 induction l; simpl in *; inversion_clear 1; auto.
 constructor; eauto.
 assert (H2:=IHl _ _ H1).
 inversion_clear H2.
 rewrite InA_cons.
 red; destruct 1.
 apply H0.
 rewrite InA_app_iff in *; rewrite InA_cons; auto.
 apply H; auto.
 constructor.
 contradict H0.
 rewrite InA_app_iff in *; rewrite InA_cons; intuition.
 eapply NoDupA_split; eauto.
Qed.

End NoDupA.

(** Some results about [eqlistA] *)

Section EqlistA.

Lemma eqlistA_length : forall l l', eqlistA l l' -> length l = length l'.
Proof.
induction 1; auto; simpl; congruence.
Qed.

Lemma eqlistA_app : forall l1 l1' l2 l2', 
   eqlistA l1 l1' -> eqlistA l2 l2' -> eqlistA (l1++l2) (l1'++l2').
Proof.
intros l1 l1' l2 l2' H; revert l2 l2'; induction H; simpl; auto.
Qed.

Lemma eqlistA_rev_app : forall l1 l1', 
   eqlistA l1 l1' -> forall l2 l2', eqlistA l2 l2' -> 
   eqlistA ((rev l1)++l2) ((rev l1')++l2').
Proof.
induction 1; auto.
simpl; intros.
do 2 rewrite app_ass; simpl; auto.
Qed.

Lemma eqlistA_rev : forall l1 l1', 
   eqlistA l1 l1' -> eqlistA (rev l1) (rev l1').
Proof.
intros.
rewrite (app_nil_end (rev l1)).
rewrite (app_nil_end (rev l1')).
apply eqlistA_rev_app; auto.
Qed.

Lemma SortA_equivlistA_eqlistA : forall l l', 
   SortA l -> SortA l' -> equivlistA l l' -> eqlistA l l'.
Proof.
induction l; destruct l'; simpl; intros; auto.
destruct (H1 a); assert (H4 : InA a nil) by auto; inversion H4.  
destruct (H1 a); assert (H4 : InA a nil) by auto; inversion H4.  
inversion_clear H; inversion_clear H0.
assert (forall y, InA y l -> ltA a y).
intros; eapply SortA_InfA_InA with (l:=l); eauto.
assert (forall y, InA y l' -> ltA a0 y).
intros; eapply SortA_InfA_InA with (l:=l'); eauto.
clear H3 H4.
assert (eqA a a0).
 destruct (H1 a).
 destruct (H1 a0).
 assert (InA a (a0::l')) by auto.
 inversion_clear H8; auto.
 assert (InA a0 (a::l)) by auto.
 inversion_clear H8; auto.
 elim (@ltA_not_eqA a a); auto.
 apply ltA_trans with a0; auto.
constructor; auto.
apply IHl; auto.
split; intros.
destruct (H1 x).
assert (H8 : InA x (a0::l')) by auto; inversion_clear H8; auto. 
elim (@ltA_not_eqA a x); eauto.
destruct (H1 x).
assert (H8 : InA x (a::l)) by auto; inversion_clear H8; auto. 
elim (@ltA_not_eqA a0 x); eauto.
Qed.

End EqlistA.

(** A few things about [filter] *)

Section Filter.

Lemma filter_sort : forall f l, SortA l -> SortA (List.filter f l).
Proof.
induction l; simpl; auto.
inversion_clear 1; auto.
destruct (f a); auto.
constructor; auto.
apply In_InfA; auto.
intros.
rewrite filter_In in H; destruct H.
eapply SortA_InfA_InA; eauto.
Qed.

Lemma filter_InA : forall f, (compat_bool f) -> 
 forall l x, InA x (List.filter f l) <-> InA x l /\ f x = true.
Proof.
intros; do 2 rewrite InA_alt; intuition.
destruct H0 as (y,(H0,H1)); rewrite filter_In in H1; exists y; intuition.
destruct H0 as (y,(H0,H1)); rewrite filter_In in H1; intuition.
  rewrite (H _ _ H0); auto.
destruct H1 as (y,(H0,H1)); exists y; rewrite filter_In; intuition.
  rewrite <- (H _ _ H0); auto.
Qed.

Lemma filter_split : 
 forall f, (forall x y, f x = true -> f y = false -> ltA x y) -> 
 forall l, SortA l -> l = filter f l ++ filter (fun x=>negb (f x)) l.
Proof.
induction l; simpl; intros; auto.
inversion_clear H0.
pattern l at 1; rewrite IHl; auto.
case_eq (f a); simpl; intros; auto.
assert (forall e, In e l -> f e = false).
  intros.
  assert (H4:=SortA_InfA_InA H1 H2 (In_InA H3)).
  case_eq (f e); simpl; intros; auto.
  elim (@ltA_not_eqA e e); auto.
  apply ltA_trans with a; eauto.
replace (List.filter f l) with (@nil A); auto.
generalize H3; clear; induction l; simpl; auto.
case_eq (f a); auto; intros.
rewrite H3 in H; auto; try discriminate.
Qed.

End Filter.

Section Fold.

Variable B:Type.
Variable eqB:B->B->Prop.

(** Compatibility of a two-argument function with respect to two equalities. *)
Definition compat_op (f : A -> B -> B) :=
  forall (x x' : A) (y y' : B), eqA x x' -> eqB y y' -> eqB (f x y) (f x' y').

(** Two-argument functions that allow to reorder their arguments. *)
Definition transpose (f : A -> B -> B) :=
  forall (x y : A) (z : B), eqB (f x (f y z)) (f y (f x z)). 

(** A version of transpose with restriction on where it should hold *)
Definition transpose_restr (R : A -> A -> Prop)(f : A -> B -> B) :=
  forall (x y : A) (z : B), R x y -> eqB (f x (f y z)) (f y (f x z)).

Variable st:Equivalence eqB.
Variable f:A->B->B.
Variable i:B.
Variable Comp:compat_op f.

Lemma fold_right_eqlistA : 
   forall s s', eqlistA s s' -> 
   eqB (fold_right f i s) (fold_right f i s').
Proof.
induction 1; simpl; auto.
reflexivity.
Qed.

Lemma equivlistA_NoDupA_split : forall l l1 l2 x y, eqA x y -> 
 NoDupA (x::l) -> NoDupA (l1++y::l2) -> 
 equivlistA (x::l) (l1++y::l2) -> equivlistA l (l1++l2).
Proof.
 intros; intro a.
 generalize (H2 a).
 repeat rewrite InA_app_iff.
 do 2 rewrite InA_cons.
 inversion_clear H0.
 assert (SW:=NoDupA_swap H1).
 inversion_clear SW.
 rewrite InA_app_iff in H0.
 split; intros.
 assert (~eqA a x).
  contradict H3; apply InA_eqA with a; auto.
 assert (~eqA a y).
  contradict H8; eauto.
 intuition.
 assert (eqA a x \/ InA a l) by intuition.
 destruct H8; auto.
 elim H0.
 destruct H7; [left|right]; eapply InA_eqA; eauto.
Qed.

(** [ForallList2] : specifies that a certain binary predicate should
    always hold when inspecting two different elements of the list. *)

Inductive ForallList2 (R : A -> A -> Prop) : list A -> Prop :=
  | ForallNil : ForallList2 R nil
  | ForallCons : forall a l,
     (forall b, In b l -> R a b) ->
     ForallList2 R l -> ForallList2 R (a::l).
Hint Constructors ForallList2.

(** [NoDupA] can be written in terms of [ForallList2] *)

Lemma ForallList2_NoDupA : forall l,
 ForallList2 (fun a b => ~eqA a b) l <-> NoDupA l.
Proof.
 induction l; split; intros; auto.
 inversion_clear H. constructor; [ | rewrite <- IHl; auto ].
 rewrite InA_alt; intros (a',(Haa',Ha')).
 exact (H0 a' Ha' Haa').
 inversion_clear H. constructor; [ | rewrite IHl; auto ].
 intros b Hb.
 contradict H0.
 rewrite InA_alt; exists b; auto.
Qed.

Lemma ForallList2_impl : forall (R R':A->A->Prop),
 (forall a b, R a b -> R' a b) ->
 forall l, ForallList2 R l -> ForallList2 R' l.
Proof.
 induction 2; auto.
Qed.

(** The following definition is easier to use than [ForallList2]. *)

Definition ForallList2_alt (R:A->A->Prop) l :=
 forall a b, InA a l -> InA b l -> ~eqA a b -> R a b.

Section Restriction.
Variable R : A -> A -> Prop.

(** [ForallList2] and [ForallList2_alt] are related, but no completely
    equivalent. For proving one implication, we need to know that the
    list has no duplicated elements... *)

Lemma ForallList2_equiv1 : forall l, NoDupA l ->
 ForallList2_alt R l -> ForallList2 R l.
Proof.
 induction l; auto.
 constructor. intros b Hb.
 inversion_clear H.
 apply H0; auto.
 contradict H1.
 apply InA_eqA with b; auto.
 apply IHl.
 inversion_clear H; auto.
 intros b c Hb Hc Hneq.
 apply H0; auto.
Qed.

(** ... and for proving the other implication, we need to be able
   to reverse and adapt relation [R] modulo [eqA]. *)

Hypothesis R_sym : forall a b, R a b -> R b a.
Hypothesis R_compat : forall a, compat_P (R a).

Lemma ForallList2_equiv2 : forall l,
 ForallList2 R l -> ForallList2_alt R l.
Proof.
 induction l.
 intros _. red. intros a b Ha. inversion Ha.
 inversion_clear 1 as [|? ? H_R Hl].
 intros b c Hb Hc Hneq.
 inversion_clear Hb; inversion_clear Hc.
 (* b,c = a : impossible *)
 elim Hneq; eauto.
 (* b = a, c in l *)
 rewrite InA_alt in H0; destruct H0 as (d,(Hcd,Hd)).
 apply R_compat with d; auto.
 apply R_sym; apply R_compat with a; auto.
 (* b in l, c = a *)
 rewrite InA_alt in H; destruct H as (d,(Hcd,Hd)).
 apply R_compat with a; auto.
 apply R_sym; apply R_compat with d; auto.
 (* b,c in l *)
 apply (IHl Hl); auto.
Qed.

Lemma ForallList2_equiv : forall l, NoDupA l ->
 (ForallList2 R l <-> ForallList2_alt R l).
Proof.
split; [apply ForallList2_equiv2|apply ForallList2_equiv1]; auto.
Qed.

Lemma ForallList2_equivlistA : forall l l', NoDupA l' ->
 equivlistA l l' -> ForallList2 R l -> ForallList2 R l'.
Proof.
intros.
apply ForallList2_equiv1; auto.
intros a b Ha Hb Hneq.
red in H0; rewrite <- H0 in Ha,Hb.
revert a b Ha Hb Hneq.
change (ForallList2_alt R l).
apply ForallList2_equiv2; auto.
Qed.

Variable TraR :transpose_restr R f.

Lemma fold_right_commutes_restr :
  forall s1 s2 x, ForallList2 R (s1++x::s2) ->
  eqB (fold_right f i (s1++x::s2)) (f x (fold_right f i (s1++s2))).
Proof.
induction s1; simpl; auto; intros.
reflexivity.
transitivity (f a (f x (fold_right f i (s1++s2)))).
apply Comp; auto.
apply IHs1.
inversion_clear H; auto.
apply TraR.
inversion_clear H.
apply H0.
apply in_or_app; simpl; auto.
Qed.

Lemma fold_right_equivlistA_restr :
  forall s s', NoDupA s -> NoDupA s' -> ForallList2 R s ->
  equivlistA s s' -> eqB (fold_right f i s) (fold_right f i s').
Proof.
 simple induction s.
 destruct s'; simpl.
 intros; reflexivity.
 unfold equivlistA; intros.
 destruct (H2 a).
 assert (X : InA a nil); auto; inversion X.
 intros x l Hrec s' N N' F E; simpl in *.
 assert (InA x s').
  rewrite <- (E x); auto.
 destruct (InA_split H) as (s1,(y,(s2,(H1,H2)))).
 subst s'.
 transitivity (f x (fold_right f i (s1++s2))).
 apply Comp; auto.
 apply Hrec; auto.
 inversion_clear N; auto.
 eapply NoDupA_split; eauto.
 inversion_clear F; auto.
 eapply equivlistA_NoDupA_split; eauto.
 transitivity (f y (fold_right f i (s1++s2))).
 apply Comp; auto. reflexivity.
 symmetry; apply fold_right_commutes_restr.
 apply ForallList2_equivlistA with (x::l); auto.
Qed.

Lemma fold_right_add_restr :
  forall s' s x, NoDupA s -> NoDupA s' -> ForallList2 R s' -> ~ InA x s ->
  equivlistA s' (x::s) -> eqB (fold_right f i s') (f x (fold_right f i s)).
Proof.
 intros; apply (@fold_right_equivlistA_restr s' (x::s)); auto.
Qed.

End Restriction.

(** we now state similar results, but without restriction on transpose. *)

Variable Tra :transpose f.

Lemma fold_right_commutes : forall s1 s2 x,
  eqB (fold_right f i (s1++x::s2)) (f x (fold_right f i (s1++s2))).
Proof.
induction s1; simpl; auto; intros.
reflexivity.
transitivity (f a (f x (fold_right f i (s1++s2)))); auto.
Qed.

Lemma fold_right_equivlistA :
  forall s s', NoDupA s -> NoDupA s' ->
  equivlistA s s' -> eqB (fold_right f i s) (fold_right f i s').
Proof.
intros; apply fold_right_equivlistA_restr with (R:=fun _ _ => True);
 try red; auto.
apply ForallList2_equiv1; try red; auto.
Qed.

Lemma fold_right_add :
  forall s' s x, NoDupA s -> NoDupA s' -> ~ InA x s ->
  equivlistA s' (x::s) -> eqB (fold_right f i s') (f x (fold_right f i s)).
Proof.
 intros; apply (@fold_right_equivlistA s' (x::s)); auto.
Qed.

Section Remove.

Hypothesis eqA_dec : forall x y : A, {eqA x y}+{~(eqA x y)}.

Lemma InA_dec : forall x l, { InA x l } + { ~ InA x l }.
Proof.
induction l.
right; auto.
red; inversion 1.
destruct (eqA_dec x a).
left; auto.
destruct IHl.
left; auto.
right; red; inversion_clear 1; contradiction. 
Qed.

Fixpoint removeA (x : A) (l : list A){struct l} : list A :=
  match l with
    | nil => nil
    | y::tl => if (eqA_dec x y) then removeA x tl else y::(removeA x tl)
  end.

Lemma removeA_filter : forall x l,
  removeA x l = filter (fun y => if eqA_dec x y then false else true) l.
Proof.
induction l; simpl; auto.
destruct (eqA_dec x a); auto.
rewrite IHl; auto.
Qed.

Lemma removeA_InA : forall l x y, InA y (removeA x l) <-> InA y l /\ ~eqA x y.
Proof.
induction l; simpl; auto.
split.
inversion_clear 1.
destruct 1; inversion_clear H.
intros.
destruct (eqA_dec x a); simpl; auto.
rewrite IHl; split; destruct 1; split; auto.
inversion_clear H; auto.
destruct H0; apply eqA_trans with a; auto.
split.
inversion_clear 1.
split; auto.
contradict n.
apply eqA_trans with y; auto.
rewrite (IHl x y) in H0; destruct H0; auto.
destruct 1; inversion_clear H; auto.
constructor 2; rewrite IHl; auto.
Qed.

Lemma removeA_NoDupA :
  forall s x, NoDupA s ->  NoDupA (removeA x s).
Proof.
simple induction s; simpl; intros.
auto.
inversion_clear H0.
destruct (eqA_dec x a); simpl; auto. 
constructor; auto.
rewrite removeA_InA.
intuition.
Qed. 

Lemma removeA_equivlistA : forall l l' x, 
  ~InA x l -> equivlistA (x :: l) l' -> equivlistA l (removeA x l').
Proof.  
unfold equivlistA; intros. 
rewrite removeA_InA.
split; intros.
rewrite <- H0; split; auto.
contradict H.
apply InA_eqA with x0; auto.
rewrite <- (H0 x0) in H1.
destruct H1.
inversion_clear H1; auto.
elim H2; auto.
Qed.

End Remove.

End Fold.

End Type_with_equality.

Hint Unfold compat_bool compat_nat compat_P.
Hint Constructors InA NoDupA sort lelistA eqlistA.

Section Find. 
Variable A B : Type. 
Variable eqA : A -> A -> Prop. 
Hypothesis eqA_sym : forall x y, eqA x y -> eqA y x.
Hypothesis eqA_trans : forall x y z, eqA x y -> eqA y z -> eqA x z.
Hypothesis eqA_dec : forall x y : A, {eqA x y}+{~(eqA x y)}.

Fixpoint findA (f : A -> bool) (l:list (A*B)) : option B := 
 match l with  
  | nil => None 
  | (a,b)::l => if f a then Some b else findA f l
 end.

Lemma findA_NoDupA : 
 forall l a b, 
 NoDupA (fun p p' => eqA (fst p) (fst p')) l -> 
 (InA (fun p p' => eqA (fst p) (fst p') /\ snd p = snd p') (a,b) l <->
  findA (fun a' => if eqA_dec a a' then true else false) l = Some b).
Proof.
induction l; simpl; intros.
split; intros; try discriminate.
inversion H0.
destruct a as (a',b'); rename a0 into a.
inversion_clear H.
split; intros.
inversion_clear H.
simpl in *; destruct H2; subst b'.
destruct (eqA_dec a a'); intuition.
destruct (eqA_dec a a'); simpl.
destruct H0.
generalize e H2 eqA_trans eqA_sym; clear.
induction l.
inversion 2.
inversion_clear 2; intros; auto.
destruct a0.
compute in H; destruct H.
subst b.
constructor 1; auto.
simpl.
apply eqA_trans with a; auto.
rewrite <- IHl; auto.
destruct (eqA_dec a a'); simpl in *.
inversion H; clear H; intros; subst b'; auto.
constructor 2.
rewrite IHl; auto.
Qed.

End Find. 
