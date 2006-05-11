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
Variable A : Set.
Variable eqA : A -> A -> Prop. 

(** Being in a list modulo an equality relation over type [A]. *)

Inductive InA (x : A) : list A -> Prop :=
  | InA_cons_hd : forall y l, eqA x y -> InA x (y :: l)
  | InA_cons_tl : forall y l, InA x l -> InA x (y :: l).

Hint Constructors InA.

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

Definition eqlistA l l' := forall x, InA x l <-> InA x l'.

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

Lemma InfA_ltA :
 forall l x y, ltA x y -> InfA y l -> InfA x l.
Proof.
 intro s; case s; constructor; inversion_clear H0.
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

Lemma SortA_NoDupA : forall l, SortA l -> NoDupA l.
Proof.
 simple induction l; auto.
 intros x l' H H0.
 inversion_clear H0.
 constructor; auto.  
 intro.
 assert (ltA x x) by eapply SortA_InfA_InA; eauto.
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


Lemma InA_app : forall l1 l2 x,
 InA x (l1 ++ l2) -> InA x l1 \/ InA x l2.
Proof.
 induction l1; simpl in *; intuition.
 inversion_clear H; auto.
 elim (IHl1 l2 x H0); auto.
Qed.

 Hint Constructors lelistA sort.

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

Section Remove.

Hypothesis eqA_dec : forall x y : A, {eqA x y}+{~(eqA x y)}.

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
swap n.
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

Lemma removeA_eqlistA : forall l l' x, 
  ~InA x l -> eqlistA (x :: l) l' -> eqlistA l (removeA x l').
Proof.  
unfold eqlistA; intros. 
rewrite removeA_InA.
split; intros.
rewrite <- H0; split; auto.
swap H.
apply InA_eqA with x0; auto.
rewrite <- (H0 x0) in H1.
destruct H1.
inversion_clear H1; auto.
elim H2; auto.
Qed.

Let addlistA x l l' := forall y, InA y l' <-> eqA x y \/ InA y l.

Lemma removeA_add :
  forall s s' x x', NoDupA s -> NoDupA (x' :: s') ->
  ~ eqA x x' -> ~ InA x s -> 
  addlistA x s (x' :: s') -> addlistA x (removeA x' s) s'.
Proof.
unfold addlistA; intros.
inversion_clear H0.
rewrite removeA_InA; auto.
split; intros.
destruct (eqA_dec x y); auto; intros.
right; split; auto.
destruct (H3 y); clear H3.
destruct H6; intuition.
swap H4; apply InA_eqA with y; auto.
destruct H0.
assert (InA y (x' :: s')) by rewrite H3; auto.
inversion_clear H6; auto.
elim H1; apply eqA_trans with y; auto.
destruct H0.
assert (InA y (x' :: s')) by rewrite H3; auto.
inversion_clear H7; auto.
elim H6; auto.
Qed.

Section Fold.

Variable B:Set.
Variable eqB:B->B->Prop.

(** Two-argument functions that allow to reorder its arguments. *)
Definition transpose (f : A -> B -> B) :=
  forall (x y : A) (z : B), eqB (f x (f y z)) (f y (f x z)). 

(** Compatibility of a two-argument function with respect to two equalities. *)
Definition compat_op (f : A -> B -> B) :=
  forall (x x' : A) (y y' : B), eqA x x' -> eqB y y' -> eqB (f x y) (f x' y').

(** Compatibility of a function upon natural numbers. *)
Definition compat_nat (f : A -> nat) :=
  forall x x' : A, eqA x x' -> f x = f x'.

Variable st:Setoid_Theory _ eqB.
Variable f:A->B->B.
Variable Comp:compat_op f.
Variable Ass:transpose f.
Variable i:B.

Lemma removeA_fold_right_0 :
  forall s x, ~InA x s ->
  eqB (fold_right f i s) (fold_right f i (removeA x s)).
Proof.
 simple induction s; simpl; intros.
 refl_st.
 destruct (eqA_dec x a); simpl; intros.
 absurd_hyp e; auto.
 apply Comp; auto. 
Qed.   

Lemma removeA_fold_right :
  forall s x, NoDupA s -> InA x s ->
  eqB (fold_right f i s) (f x (fold_right f i (removeA x s))).
Proof.
 simple induction s; simpl.  
 inversion_clear 2.
 intros.
 inversion_clear H0.
 destruct (eqA_dec x a); simpl; intros.
 apply Comp; auto. 
 apply removeA_fold_right_0; auto.
 swap H2; apply InA_eqA with x; auto.
 inversion_clear H1. 
 destruct n; auto.
 trans_st (f a (f x (fold_right f i (removeA x l)))).
Qed.   

Lemma fold_right_equal :
  forall s s', NoDupA s -> NoDupA s' ->
  eqlistA s s' -> eqB (fold_right f i s) (fold_right f i s').
Proof.
 simple induction s.
 destruct s'; simpl.
 intros; refl_st; auto.
 unfold eqlistA; intros.
 destruct (H1 a).
 assert (X : InA a nil); auto; inversion X.
 intros x l Hrec s' N N' E; simpl in *.
 trans_st (f x (fold_right f i (removeA x s'))).
 apply Comp; auto.
 apply Hrec; auto.
 inversion N; auto.
 apply removeA_NoDupA; auto; apply eqA_trans.
 apply removeA_eqlistA; auto.
 inversion_clear N; auto.
 sym_st.
 apply removeA_fold_right; auto.
 unfold eqlistA in E.
 rewrite <- E; auto.
Qed.

Lemma fold_right_add :
  forall s' s x, NoDupA s -> NoDupA s' -> ~ InA x s ->
  addlistA x s s' -> eqB (fold_right f i s') (f x (fold_right f i s)).
Proof.   
 simple induction s'.
 unfold addlistA; intros.
 destruct (H2 x); clear H2.
 assert (X : InA x nil); auto; inversion X.
 intros x' l' Hrec s x N N' IN EQ; simpl.
 (* if x=x' *)
 destruct (eqA_dec x x').
 apply Comp; auto.
 apply fold_right_equal; auto.
 inversion_clear N'; trivial.
 unfold eqlistA; unfold addlistA in EQ; intros.
 destruct (EQ x0); clear EQ.
 split; intros.
 destruct H; auto.
 inversion_clear N'.
 destruct H2; apply InA_eqA with x0; auto.
 apply eqA_trans with x; auto.
 assert (X:InA x0 (x' :: l')); auto; inversion_clear X; auto.
 destruct IN; apply InA_eqA with x0; auto.
 apply eqA_trans with x'; auto.
 (* else x<>x' *)   
 trans_st (f x' (f x (fold_right f i (removeA x' s)))).
 apply Comp; auto.
 apply Hrec; auto.
 apply removeA_NoDupA; auto; apply eqA_trans.
 inversion_clear N'; auto.
 rewrite removeA_InA; intuition.
 apply removeA_add; auto.
 trans_st (f x (f x' (fold_right f i (removeA x' s)))).
 apply Comp; auto.
 sym_st.
 apply removeA_fold_right; auto.
 destruct (EQ x'). 
 destruct H; auto; destruct n; auto.
Qed.

End Fold.

End Remove.

End Type_with_equality.

Hint Constructors InA.
Hint Constructors NoDupA. 
Hint Constructors sort.
Hint Constructors lelistA.
