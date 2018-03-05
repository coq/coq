(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

(******************************************************************)
(** * Basics: definition of polymorphic lists and some operations *)
(******************************************************************)

(** The definition of [list] is now in [Init/Datatypes],
    as well as the definitions of [length] and [app] *)

Open Scope list_scope.

(** Standard notations for lists.
In a special module to avoid conflicts. *)
Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.

Import ListNotations.

Section Lists.

  Variable A : Type.

  (** Head and tail *)

  Definition hd (default:A) (l:list A) :=
    match l with
      | [] => default
      | x :: _ => x
    end.

  Definition hd_error (l:list A) :=
    match l with
      | [] => None
      | x :: _ => Some x
    end.

  Definition tl (l:list A) :=
    match l with
      | [] => nil
      | a :: m => m
    end.

  (** The [In] predicate *)
  Fixpoint In (a:A) (l:list A) : Prop :=
    match l with
      | [] => False
      | b :: m => b = a \/ In a m
    end.

End Lists.

Section Facts.

  Variable A : Type.


  (** *** Generic facts *)

  (** Discrimination *)
  Theorem nil_cons : forall (x:A) (l:list A), [] <> x :: l.
  Proof.
    intros; discriminate.
  Qed.


  (** Destruction *)

  Theorem destruct_list : forall l : list A, {x:A & {tl:list A | l = x::tl}}+{l = []}.
  Proof.
    induction l as [|a tail].
    right; reflexivity.
    left; exists a, tail; reflexivity.
  Qed.

  Lemma hd_error_tl_repr : forall l (a:A) r,
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof. destruct l as [|x xs].
    - unfold hd_error, tl; intros a r. split; firstorder discriminate.
    - intros. simpl. split.
      * intros (H1, H2). inversion H1. rewrite H2. reflexivity.
      * inversion 1. subst. auto.
  Qed.

  Lemma hd_error_some_nil : forall l (a:A), hd_error l = Some a -> l <> nil.
  Proof. unfold hd_error. destruct l; now discriminate. Qed.

  Theorem length_zero_iff_nil (l : list A):
    length l = 0 <-> l=[].
  Proof.
    split; [now destruct l | now intros ->].
  Qed.

  (** *** Head and tail *)

  Theorem hd_error_nil : hd_error (@nil A) = None.
  Proof.
    simpl; reflexivity.
  Qed.

  Theorem hd_error_cons : forall (l : list A) (x : A), hd_error (x::l) = Some x.
  Proof.
    intros; simpl; reflexivity.
  Qed.


  (************************)
  (** *** Facts about [In] *)
  (************************)


  (** Characterization of [In] *)

  Theorem in_eq : forall (a:A) (l:list A), In a (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem in_cons : forall (a b:A) (l:list A), In b l -> In b (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem not_in_cons (x a : A) (l : list A):
    ~ In x (a::l) <-> x<>a /\ ~ In x l.
  Proof.
    simpl. intuition.
  Qed.

  Theorem in_nil : forall a:A, ~ In a [].
  Proof.
    unfold not; intros a H; inversion_clear H.
  Qed.

  Theorem in_split : forall x (l:list A), In x l -> exists l1 l2, l = l1++x::l2.
  Proof.
  induction l; simpl; destruct 1.
  subst a; auto.
  exists [], l; auto.
  destruct (IHl H) as (l1,(l2,H0)).
  exists (a::l1), l2; simpl. apply f_equal. auto.
  Qed.

  (** Inversion *)
  Lemma in_inv : forall (a b:A) (l:list A), In b (a :: l) -> a = b \/ In b l.
  Proof.
    intros a b l H; inversion_clear H; auto.
  Qed.

  (** Decidability of [In] *)
  Theorem in_dec :
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (a:A) (l:list A), {In a l} + {~ In a l}.
  Proof.
    intro H; induction l as [| a0 l IHl].
    right; apply in_nil.
    destruct (H a0 a); simpl; auto.
    destruct IHl; simpl; auto.
    right; unfold not; intros [Hc1| Hc2]; auto.
  Defined.


  (**************************)
  (** *** Facts about [app] *)
  (**************************)

  (** Discrimination *)
  Theorem app_cons_not_nil : forall (x y:list A) (a:A), [] <> x ++ a :: y.
  Proof.
    unfold not.
    destruct x as [| a l]; simpl; intros.
    discriminate H.
    discriminate H.
  Qed.


  (** Concat with [nil] *)
  Theorem app_nil_l : forall l:list A, [] ++ l = l.
  Proof.
    reflexivity.
  Qed.

  Theorem app_nil_r : forall l:list A, l ++ [] = l.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  (* begin hide *)
  (* Deprecated *)
  Theorem app_nil_end : forall (l:list A), l = l ++ [].
  Proof. symmetry; apply app_nil_r. Qed.
  (* end hide *)

  (** [app] is associative *)
  Theorem app_assoc : forall l m n:list A, l ++ m ++ n = (l ++ m) ++ n.
  Proof.
    intros l m n; induction l; simpl; f_equal; auto.
  Qed.

  (* begin hide *)
  (* Deprecated *)
  Theorem app_assoc_reverse : forall l m n:list A, (l ++ m) ++ n = l ++ m ++ n.
  Proof.
     auto using app_assoc.
  Qed.
  Hint Resolve app_assoc_reverse.
  (* end hide *)

  (** [app] commutes with [cons] *)
  Theorem app_comm_cons : forall (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
  Proof.
    auto.
  Qed.

  (** Facts deduced from the result of a concatenation *)

  Theorem app_eq_nil : forall l l':list A, l ++ l' = [] -> l = [] /\ l' = [].
  Proof.
    destruct l as [| x l]; destruct l' as [| y l']; simpl; auto.
    intro; discriminate.
    intros H; discriminate H.
  Qed.

  Theorem app_eq_unit :
    forall (x y:list A) (a:A),
      x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof.
    destruct x as [| a l]; [ destruct y as [| a l] | destruct y as [| a0 l0] ];
      simpl.
    intros a H; discriminate H.
    left; split; auto.
    right; split; auto.
    generalize H.
    generalize (app_nil_r l); intros E.
    rewrite -> E; auto.
    intros.
    injection H as H H0.
    assert ([] = l ++ a0 :: l0) by auto.
    apply app_cons_not_nil in H1 as [].
  Qed.

  Lemma app_inj_tail :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof.
    induction x as [| x l IHl];
      [ destruct y as [| a l] | destruct y as [| a l0] ];
      simpl; auto.
    - intros a b H.
      injection H.
      auto.
    - intros a0 b H.
      injection H as H1 H0.
      apply app_cons_not_nil in H0 as [].
    - intros a b H.
      injection H as H1 H0.
      assert ([] = l ++ [a]) by auto.
      apply app_cons_not_nil in H as [].
    - intros a0 b H.
      injection H as <- H0.
      destruct (IHl l0 a0 b H0) as (<-,<-).
      split; auto.
  Qed.


  (** Compatibility with other operations *)

  Lemma app_length : forall l l' : list A, length (l++l') = length l + length l'.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma in_app_or : forall (l m:list A) (a:A), In a (l ++ m) -> In a l \/ In a m.
  Proof.
    intros l m a.
    elim l; simpl; auto.
    intros a0 y H H0.
    now_show ((a0 = a \/ In a y) \/ In a m).
    elim H0; auto.
    intro H1.
    now_show ((a0 = a \/ In a y) \/ In a m).
    elim (H H1); auto.
  Qed.

  Lemma in_or_app : forall (l m:list A) (a:A), In a l \/ In a m -> In a (l ++ m).
  Proof.
    intros l m a.
    elim l; simpl; intro H.
    now_show (In a m).
    elim H; auto; intro H0.
    now_show (In a m).
    elim H0. (* subProof completed *)
    intros y H0 H1.
    now_show (H = a \/ In a (y ++ m)).
    elim H1; auto 4.
    intro H2.
    now_show (H = a \/ In a (y ++ m)).
    elim H2; auto.
  Qed.

  Lemma in_app_iff : forall l l' (a:A), In a (l++l') <-> In a l \/ In a l'.
  Proof.
    split; auto using in_app_or, in_or_app.
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    induction l; simpl; auto; injection 1; auto.
  Qed.

  Lemma app_inv_tail:
    forall l l1 l2 : list A, l1 ++ l = l2 ++ l -> l1 = l2.
  Proof.
    intros l l1 l2; revert l1 l2 l.
    induction l1 as [ | x1 l1]; destruct l2 as [ | x2 l2];
     simpl; auto; intros l H.
    absurd (length (x2 :: l2 ++ l) <= length l).
    simpl; rewrite app_length; auto with arith.
    rewrite <- H; auto with arith.
    absurd (length (x1 :: l1 ++ l) <= length l).
    simpl; rewrite app_length; auto with arith.
    rewrite H; auto with arith.
    injection H as H H0; f_equal; eauto.
  Qed.

End Facts.

Hint Resolve app_assoc app_assoc_reverse: datatypes.
Hint Resolve app_comm_cons app_cons_not_nil: datatypes.
Hint Immediate app_eq_nil: datatypes.
Hint Resolve app_eq_unit app_inj_tail: datatypes.
Hint Resolve in_eq in_cons in_inv in_nil in_app_or in_or_app: datatypes.



(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, [] => default
      | S m, x :: t => nth m t default
    end.

  Fixpoint nth_ok (n:nat) (l:list A) (default:A) {struct l} : bool :=
    match n, l with
      | O, x :: l' => true
      | O, other => false
      | S m, [] => false
      | S m, x :: t => nth_ok m t default
    end.

  Lemma nth_in_or_default :
    forall (n:nat) (l:list A) (d:A), {In (nth n l d) l} + {nth n l d = d}.
  Proof.
    intros n l d; revert n; induction l.
    - right; destruct n; trivial.
    - intros [|n]; simpl.
      * left; auto.
      * destruct (IHl n); auto.
  Qed.

  Lemma nth_S_cons :
    forall (n:nat) (l:list A) (d a:A),
      In (nth n l d) l -> In (nth (S n) (a :: l) d) (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Fixpoint nth_error (l:list A) (n:nat) {struct n} : option A :=
    match n, l with
      | O, x :: _ => Some x
      | S n, _ :: l => nth_error l n
      | _, _ => None
    end.

  Definition nth_default (default:A) (l:list A) (n:nat) : A :=
    match nth_error l n with
      | Some x => x
      | None => default
    end.

  Lemma nth_default_eq :
    forall n l (d:A), nth_default d l n = nth n l d.
  Proof.
    unfold nth_default; induction n; intros [ | ] ?; simpl; auto.
  Qed.

  (** Results about [nth] *)

  Lemma nth_In :
    forall (n:nat) (l:list A) (d:A), n < length l -> In (nth n l d) l.
  Proof.
    unfold lt; induction n as [| n hn]; simpl.
    - destruct l; simpl; [ inversion 2 | auto ].
    - destruct l; simpl.
      * inversion 2.
      * intros d ie; right; apply hn; auto with arith.
  Qed.

  Lemma In_nth l x d : In x l ->
    exists n, n < length l /\ nth n l d = x.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      * subst; exists 0; simpl; auto with arith.
      * destruct (IH H) as (n & Hn & Hn').
        exists (S n); simpl; auto with arith.
  Qed.

  Lemma nth_overflow : forall l n d, length l <= n -> nth n l d = d.
  Proof.
    induction l; destruct n; simpl; intros; auto.
    - inversion H.
    - apply IHl; auto with arith.
  Qed.

  Lemma nth_indep :
    forall l n d d', n < length l -> nth n l d = nth n l d'.
  Proof.
    induction l.
    - inversion 1.
    - intros [|n] d d'; simpl; auto with arith.
  Qed.

  Lemma app_nth1 :
    forall l l' d n, n < length l -> nth n (l++l') d = nth n l d.
  Proof.
    induction l.
    - inversion 1.
    - intros l' d [|n]; simpl; auto with arith.
  Qed.

  Lemma app_nth2 :
    forall l l' d n, n >= length l -> nth n (l++l') d = nth (n-length l) l' d.
  Proof.
    induction l; intros l' d [|n]; auto.
    - inversion 1.
    - intros; simpl; rewrite IHl; auto with arith.
  Qed.

  Lemma nth_split n l d : n < length l ->
    exists l1, exists l2, l = l1 ++ nth n l d :: l2 /\ length l1 = n.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|a l] H; try easy.
    - exists nil; exists l; now simpl.
    - destruct (IH l) as (l1 & l2 & Hl & Hl1); auto with arith.
      exists (a::l1); exists l2; simpl; split; now f_equal.
  Qed.

  (** Results about [nth_error] *)

  Lemma nth_error_In l n x : nth_error l n = Some x -> In x l.
  Proof.
    revert n. induction l as [|a l IH]; intros [|n]; simpl; try easy.
    - injection 1; auto.
    - eauto.
  Qed.

  Lemma In_nth_error l x : In x l -> exists n, nth_error l n = Some x.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      * subst; exists 0; simpl; auto with arith.
      * destruct (IH H) as (n,Hn).
        exists (S n); simpl; auto with arith.
  Qed.

  Lemma nth_error_None l n : nth_error l n = None <-> length l <= n.
  Proof.
    revert n. induction l; destruct n; simpl.
    - split; auto.
    - split; auto with arith.
    - split; now auto with arith.
    - rewrite IHl; split; auto with arith.
  Qed.

  Lemma nth_error_Some l n : nth_error l n <> None <-> n < length l.
  Proof.
   revert n. induction l; destruct n; simpl.
    - split; [now destruct 1 | inversion 1].
    - split; [now destruct 1 | inversion 1].
    - split; now auto with arith.
    - rewrite IHl; split; auto with arith.
  Qed.

  Lemma nth_error_split l n a : nth_error l n = Some a ->
    exists l1, exists l2, l = l1 ++ a :: l2 /\ length l1 = n.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|x l] H; simpl in *; try easy.
    - exists nil; exists l. now injection H as ->.
    - destruct (IH _ H) as (l1 & l2 & H1 & H2).
      exists (x::l1); exists l2; simpl; split; now f_equal.
  Qed.

  Lemma nth_error_app1 l l' n : n < length l ->
    nth_error (l++l') n = nth_error l n.
  Proof.
    revert l.
    induction n; intros [|a l] H; auto; try solve [inversion H].
    simpl in *. apply IHn. auto with arith.
  Qed.

  Lemma nth_error_app2 l l' n : length l <= n ->
    nth_error (l++l') n = nth_error l' (n-length l).
  Proof.
    revert l.
    induction n; intros [|a l] H; auto; try solve [inversion H].
    simpl in *. apply IHn. auto with arith.
  Qed.

  (*****************)
  (** ** Remove    *)
  (*****************)

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Fixpoint remove (x : A) (l : list A) : list A :=
    match l with
      | [] => []
      | y::tl => if (eq_dec x y) then remove x tl else y::(remove x tl)
    end.

  Theorem remove_In : forall (l : list A) (x : A), ~ In x (remove x l).
  Proof.
    induction l as [|x l]; auto.
    intro y; simpl; destruct (eq_dec y x) as [yeqx | yneqx].
    apply IHl.
    unfold not; intro HF; simpl in HF; destruct HF; auto.
    apply (IHl y); assumption.
  Qed.


(******************************)
(** ** Last element of a list *)
(******************************)

  (** [last l d] returns the last element of the list [l],
    or the default value [d] if [l] is empty. *)

  Fixpoint last (l:list A) (d:A) : A :=
  match l with
    | [] => d
    | [a] => a
    | a :: l => last l d
  end.

  (** [removelast l] remove the last element of [l] *)

  Fixpoint removelast (l:list A) : list A :=
    match l with
      | [] =>  []
      | [a] => []
      | a :: l => a :: removelast l
    end.

  Lemma app_removelast_last :
    forall l d, l <> [] -> l = removelast l ++ [last l d].
  Proof.
    induction l.
    destruct 1; auto.
    intros d _.
    destruct l; auto.
    pattern (a0::l) at 1; rewrite IHl with d; auto; discriminate.
  Qed.

  Lemma exists_last :
    forall l, l <> [] -> { l' : (list A) & { a : A | l = l' ++ [a]}}.
  Proof.
    induction l.
    destruct 1; auto.
    intros _.
    destruct l.
    exists [], a; auto.
    destruct IHl as [l' (a',H)]; try discriminate.
    rewrite H.
    exists (a::l'), a'; auto.
  Qed.

  Lemma removelast_app :
    forall l l', l' <> [] -> removelast (l++l') = l ++ removelast l'.
  Proof.
    induction l.
    simpl; auto.
    simpl; intros.
    assert (l++l' <> []).
    destruct l.
    simpl; auto.
    simpl; discriminate.
    specialize (IHl l' H).
    destruct (l++l'); [elim H0; auto|f_equal; auto].
  Qed.


  (******************************************)
  (** ** Counting occurrences of an element *)
  (******************************************)

  Fixpoint count_occ (l : list A) (x : A) : nat :=
    match l with
      | [] => 0
      | y :: tl =>
        let n := count_occ tl x in
        if eq_dec y x then S n else n
    end.

  (** Compatibility of count_occ with operations on list *)
  Theorem count_occ_In l x : In x l <-> count_occ l x > 0.
  Proof.
    induction l as [|y l]; simpl.
    - split; [destruct 1 | apply gt_irrefl].
    - destruct eq_dec as [->|Hneq]; rewrite IHl; intuition.
  Qed.

  Theorem count_occ_not_In l x : ~ In x l <-> count_occ l x = 0.
  Proof.
    rewrite count_occ_In. unfold gt. now rewrite Nat.nlt_ge, Nat.le_0_r.
  Qed.

  Lemma count_occ_nil x : count_occ [] x = 0.
  Proof.
    reflexivity.
  Qed.

  Theorem count_occ_inv_nil l :
    (forall x:A, count_occ l x = 0) <-> l = [].
  Proof.
    split.
    - induction l as [|x l]; trivial.
      intros H. specialize (H x). simpl in H.
      destruct eq_dec as [_|NEQ]; [discriminate|now elim NEQ].
    - now intros ->.
  Qed.

  Lemma count_occ_cons_eq l x y :
    x = y -> count_occ (x::l) y = S (count_occ l y).
  Proof.
    intros H. simpl. now destruct (eq_dec x y).
  Qed.

  Lemma count_occ_cons_neq l x y :
    x <> y -> count_occ (x::l) y = count_occ l y.
  Proof.
    intros H. simpl. now destruct (eq_dec x y).
  Qed.

End Elts.

(*******************************)
(** * Manipulating whole lists *)
(*******************************)

Section ListOps.

  Variable A : Type.

  (*************************)
  (** ** Reverse           *)
  (*************************)

  Fixpoint rev (l:list A) : list A :=
    match l with
      | [] => []
      | x :: l' => rev l' ++ [x]
    end.

  Lemma rev_app_distr : forall x y:list A, rev (x ++ y) = rev y ++ rev x.
  Proof.
    induction x as [| a l IHl].
    destruct y as [| a l].
    simpl.
    auto.

    simpl.
    rewrite app_nil_r; auto.

    intro y.
    simpl.
    rewrite (IHl y).
    rewrite app_assoc; trivial.
  Qed.

  Remark rev_unit : forall (l:list A) (a:A), rev (l ++ [a]) = a :: rev l.
  Proof.
    intros.
    apply (rev_app_distr l [a]); simpl; auto.
  Qed.

  Lemma rev_involutive : forall l:list A, rev (rev l) = l.
  Proof.
    induction l as [| a l IHl].
    simpl; auto.

    simpl.
    rewrite (rev_unit (rev l) a).
    rewrite IHl; auto.
  Qed.


  (** Compatibility with other operations *)

  Lemma in_rev : forall l x, In x l <-> In x (rev l).
  Proof.
    induction l.
    simpl; intuition.
    intros.
    simpl.
    intuition.
    subst.
    apply in_or_app; right; simpl; auto.
    apply in_or_app; left; firstorder.
    destruct (in_app_or _ _ _ H); firstorder.
  Qed.

  Lemma rev_length : forall l, length (rev l) = length l.
  Proof.
    induction l;simpl; auto.
    rewrite app_length.
    rewrite IHl.
    simpl.
    elim (length l); simpl; auto.
  Qed.

  Lemma rev_nth : forall l d n,  n < length l ->
    nth n (rev l) d = nth (length l - S n) l d.
  Proof.
    induction l.
    intros; inversion H.
    intros.
    simpl in H.
    simpl (rev (a :: l)).
    simpl (length (a :: l) - S n).
    inversion H.
    rewrite <- minus_n_n; simpl.
    rewrite <- rev_length.
    rewrite app_nth2; auto.
    rewrite <- minus_n_n; auto.
    rewrite app_nth1; auto.
    rewrite (minus_plus_simpl_l_reverse (length l) n 1).
    replace (1 + length l) with (S (length l)); auto with arith.
    rewrite <- minus_Sn_m; auto with arith.
    apply IHl ; auto with arith.
    rewrite rev_length; auto.
  Qed.


  (**  An alternative tail-recursive definition for reverse *)

  Fixpoint rev_append (l l': list A) : list A :=
    match l with
      | [] => l'
      | a::l => rev_append l (a::l')
    end.

  Definition rev' l : list A := rev_append l [].

  Lemma rev_append_rev : forall l l', rev_append l l' = rev l ++ l'.
  Proof.
    induction l; simpl; auto; intros.
    rewrite <- app_assoc; firstorder.
  Qed.

  Lemma rev_alt : forall l, rev l = rev_append l [].
  Proof.
    intros; rewrite rev_append_rev.
    rewrite app_nil_r; trivial.
  Qed.


(*********************************************)
(** Reverse Induction Principle on Lists  *)
(*********************************************)

  Section Reverse_Induction.

    Lemma rev_list_ind :
      forall P:list A-> Prop,
	P [] ->
	(forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
	forall l:list A, P (rev l).
    Proof.
      induction l; auto.
    Qed.

    Theorem rev_ind :
      forall P:list A -> Prop,
	P [] ->
	(forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros.
      generalize (rev_involutive l).
      intros E; rewrite <- E.
      apply (rev_list_ind P).
      auto.

      simpl.
      intros.
      apply (H0 a (rev l0)).
      auto.
    Qed.

  End Reverse_Induction.

  (*************************)
  (** ** Concatenation     *)
  (*************************)

  Fixpoint concat (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x l => x ++ concat l
  end.

  Lemma concat_nil : concat nil = nil.
  Proof.
  reflexivity.
  Qed.

  Lemma concat_cons : forall x l, concat (cons x l) = x ++ concat l.
  Proof.
  reflexivity.
  Qed.

  Lemma concat_app : forall l1 l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
  Proof.
  intros l1; induction l1 as [|x l1 IH]; intros l2; simpl.
  + reflexivity.
  + rewrite IH; apply app_assoc.
  Qed.

  (***********************************)
  (** ** Decidable equality on lists *)
  (***********************************)

  Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.

  Lemma list_eq_dec : forall l l':list A, {l = l'} + {l <> l'}.
  Proof. decide equality. Defined.

End ListOps.

(***************************************************)
(** * Applying functions to the elements of a list *)
(***************************************************)

(************)
(** ** Map  *)
(************)

Section Map.
  Variables (A : Type) (B : Type).
  Variable f : A -> B.

  Fixpoint map (l:list A) : list B :=
    match l with
      | [] => []
      | a :: t => (f a) :: (map t)
    end.

  Lemma map_cons (x:A)(l:list A) : map (x::l) = (f x) :: (map l).
  Proof.
    reflexivity.
  Qed.

  Lemma in_map :
    forall (l:list A) (x:A), In x l -> In (f x) (map l).
  Proof.
    induction l; firstorder (subst; auto).
  Qed.

  Lemma in_map_iff : forall l y, In y (map l) <-> exists x, f x = y /\ In x l.
  Proof.
    induction l; firstorder (subst; auto).
  Qed.

  Lemma map_length : forall l, length (map l) = length l.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma map_nth : forall l d n,
    nth n (map l) (f d) = f (nth n l d).
  Proof.
    induction l; simpl map; destruct n; firstorder.
  Qed.

  Lemma map_nth_error : forall n l d,
    nth_error l n = Some d -> nth_error (map l) n = Some (f d).
  Proof.
    induction n; intros [ | ] ? Heq; simpl in *; inversion Heq; auto.
  Qed.

  Lemma map_app : forall l l',
    map (l++l') = (map l)++(map l').
  Proof.
    induction l; simpl; auto.
    intros; rewrite IHl; auto.
  Qed.

  Lemma map_rev : forall l, map (rev l) = rev (map l).
  Proof.
    induction l; simpl; auto.
    rewrite map_app.
    rewrite IHl; auto.
  Qed.

  Lemma map_eq_nil : forall l, map l = [] -> l = [].
  Proof.
    destruct l; simpl; reflexivity || discriminate.
  Qed.

  (** [map] and count of occurrences *)

  Hypothesis decA: forall x1 x2 : A, {x1 = x2} + {x1 <> x2}.
  Hypothesis decB: forall y1 y2 : B, {y1 = y2} + {y1 <> y2}.
  Hypothesis Hfinjective: forall x1 x2: A, (f x1) = (f x2) -> x1 = x2.

  Theorem count_occ_map x l:
    count_occ decA l x = count_occ decB (map l) (f x).
  Proof.
    revert x. induction l as [| a l' Hrec]; intro x; simpl.
    - reflexivity.
    - specialize (Hrec x).
      destruct (decA a x) as [H1|H1], (decB (f a) (f x)) as [H2|H2].
      * rewrite Hrec. reflexivity.
      * contradiction H2. rewrite H1. reflexivity.
      * specialize (Hfinjective H2). contradiction H1.
      * assumption.
  Qed.

  (** [flat_map] *)

  Definition flat_map (f:A -> list B) :=
    fix flat_map (l:list A) : list B :=
    match l with
      | nil => nil
      | cons x t => (f x)++(flat_map t)
    end.

  Lemma in_flat_map : forall (f:A->list B)(l:list A)(y:B),
    In y (flat_map f l) <-> exists x, In x l /\ In y (f x).
  Proof using A B.
    clear Hfinjective.
    induction l; simpl; split; intros.
    contradiction.
    destruct H as (x,(H,_)); contradiction.
    destruct (in_app_or _ _ _ H).
    exists a; auto.
    destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
    exists x; auto.
    apply in_or_app.
    destruct H as (x,(H0,H1)); destruct H0.
    subst; auto.
    right; destruct (IHl y) as (_,H2); apply H2.
    exists x; auto.
  Qed.

End Map.

Lemma flat_map_concat_map : forall A B (f : A -> list B) l,
  flat_map f l = concat (map f l).
Proof.
intros A B f l; induction l as [|x l IH]; simpl.
+ reflexivity.
+ rewrite IH; reflexivity.
Qed.

Lemma concat_map : forall A B (f : A -> B) l, map f (concat l) = concat (map (map f) l).
Proof.
intros A B f l; induction l as [|x l IH]; simpl.
+ reflexivity.
+ rewrite map_app, IH; reflexivity.
Qed.

Lemma map_id : forall (A :Type) (l : list A),
  map (fun x => x) l = l.
Proof.
  induction l; simpl; auto; rewrite IHl; auto.
Qed.

Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma map_ext_in :
  forall (A B : Type)(f g:A->B) l, (forall a, In a l -> f a = g a) -> map f l = map g l.
Proof.
  induction l; simpl; auto.
  intros; rewrite H by intuition; rewrite IHl; auto.
Qed.

Lemma map_ext :
  forall (A B : Type)(f g:A->B), (forall a, f a = g a) -> forall l, map f l = map g l.
Proof.
  intros; apply map_ext_in; auto.
Qed.


(************************************)
(** Left-to-right iterator on lists *)
(************************************)

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint fold_left (l:list B) (a0:A) : A :=
    match l with
      | nil => a0
      | cons b t => fold_left t (f a0 b)
    end.

  Lemma fold_left_app : forall (l l':list B)(i:A),
    fold_left (l++l') i = fold_left l' (fold_left l i).
  Proof.
    induction l.
    simpl; auto.
    intros.
    simpl.
    auto.
  Qed.

End Fold_Left_Recursor.

Lemma fold_left_length :
  forall (A:Type)(l:list A), fold_left (fun x _ => S x) l 0 = length l.
Proof.
  intros A l.
  enough (H : forall n, fold_left (fun x _ => S x) l n = n + length l) by exact (H 0).
  induction l; simpl; auto.
  intros; rewrite IHl.
  simpl; auto with arith.
Qed.

(************************************)
(** Right-to-left iterator on lists *)
(************************************)

Section Fold_Right_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_right (l:list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right t)
    end.

End Fold_Right_Recursor.

  Lemma fold_right_app : forall (A B:Type)(f:A->B->B) l l' i,
    fold_right f i (l++l') = fold_right f (fold_right f i l') l.
  Proof.
    induction l.
    simpl; auto.
    simpl; intros.
    f_equal; auto.
  Qed.

  Lemma fold_left_rev_right : forall (A B:Type)(f:A->B->B) l i,
    fold_right f i (rev l) = fold_left (fun x y => f y x) l i.
  Proof.
    induction l.
    simpl; auto.
    intros.
    simpl.
    rewrite fold_right_app; simpl; auto.
  Qed.

  Theorem fold_symmetric :
    forall (A : Type) (f : A -> A -> A),
    (forall x y z : A, f x (f y z) = f (f x y) z) ->
    forall (a0 : A), (forall y : A, f a0 y = f y a0) ->
    forall (l : list A), fold_left f l a0 = fold_right f a0 l.
  Proof.
    intros A f assoc a0 comma0 l.
    induction l as [ | a1 l ]; [ simpl; reflexivity | ].
    simpl. rewrite <- IHl. clear IHl. revert a1. induction l; [ auto | ].
    simpl. intro. rewrite <- assoc. rewrite IHl. rewrite IHl. auto.
  Qed.

  (** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
      indexed by elts of [x], sorted in lexicographic order. *)

  Fixpoint list_power (A B:Type)(l:list A) (l':list B) :
    list (list (A * B)) :=
    match l with
      | nil => cons nil nil
      | cons x t =>
	flat_map (fun f:list (A * B) => map (fun y:B => cons (x, y) f) l')
        (list_power t l')
    end.


  (*************************************)
  (** ** Boolean operations over lists *)
  (*************************************)

  Section Bool.
    Variable A : Type.
    Variable f : A -> bool.

  (** find whether a boolean function can be satisfied by an
       elements of the list. *)

    Fixpoint existsb (l:list A) : bool :=
      match l with
	| nil => false
	| a::l => f a || existsb l
      end.

    Lemma existsb_exists :
      forall l, existsb l = true <-> exists x, In x l /\ f x = true.
    Proof.
      induction l; simpl; intuition.
      inversion H.
      firstorder.
      destruct (orb_prop _ _ H1); firstorder.
      firstorder.
      subst.
      rewrite H2; auto.
    Qed.

    Lemma existsb_nth : forall l n d, n < length l ->
      existsb l = false -> f (nth n l d) = false.
    Proof.
      induction l.
      inversion 1.
      simpl; intros.
      destruct (orb_false_elim _ _ H0); clear H0; auto.
      destruct n ; auto.
      rewrite IHl; auto with arith.
    Qed.

    Lemma existsb_app : forall l1 l2,
      existsb (l1++l2) = existsb l1 || existsb l2.
    Proof.
      induction l1; intros l2; simpl.
        solve[auto].
      case (f a); simpl; solve[auto].
    Qed.

  (** find whether a boolean function is satisfied by
    all the elements of a list. *)

    Fixpoint forallb (l:list A) : bool :=
      match l with
	| nil => true
	| a::l => f a && forallb l
      end.

    Lemma forallb_forall :
      forall l, forallb l = true <-> (forall x, In x l -> f x = true).
    Proof.
      induction l; simpl; intuition.
      destruct (andb_prop _ _ H1).
      congruence.
      destruct (andb_prop _ _ H1); auto.
      assert (forallb l = true).
      apply H0; intuition.
      rewrite H1; auto.
    Qed.

    Lemma forallb_app :
      forall l1 l2, forallb (l1++l2) = forallb l1 && forallb l2.
    Proof.
      induction l1; simpl.
        solve[auto].
      case (f a); simpl; solve[auto].
    Qed.
  (** [filter] *)

    Fixpoint filter (l:list A) : list A :=
      match l with
	| nil => nil
	| x :: l => if f x then x::(filter l) else filter l
      end.

    Lemma filter_In : forall x l, In x (filter l) <-> In x l /\ f x = true.
    Proof.
      induction l; simpl.
      intuition.
      intros.
      case_eq (f a); intros; simpl; intuition congruence.
    Qed.

  (** [find] *)

    Fixpoint find (l:list A) : option A :=
      match l with
	| nil => None
	| x :: tl => if f x then Some x else find tl
      end.

    Lemma find_some l x : find l = Some x -> In x l /\ f x = true.
    Proof.
     induction l as [|a l IH]; simpl; [easy| ].
     case_eq (f a); intros Ha Eq.
     * injection Eq as ->; auto.
     * destruct (IH Eq); auto.
    Qed.

    Lemma find_none l : find l = None -> forall x, In x l -> f x = false.
    Proof.
     induction l as [|a l IH]; simpl; [easy|].
     case_eq (f a); intros Ha Eq x IN; [easy|].
     destruct IN as [<-|IN]; auto.
    Qed.

  (** [partition] *)

    Fixpoint partition (l:list A) : list A * list A :=
      match l with
	| nil => (nil, nil)
	| x :: tl => let (g,d) := partition tl in
	  if f x then (x::g,d) else (g,x::d)
      end.

  Theorem partition_cons1 a l l1 l2:
    partition l = (l1, l2) ->
    f a = true ->
    partition (a::l) = (a::l1, l2).
  Proof.
    simpl. now intros -> ->.
  Qed.

  Theorem partition_cons2 a l l1 l2:
    partition l = (l1, l2) ->
    f a=false ->
    partition (a::l) = (l1, a::l2).
  Proof.
    simpl. now intros -> ->.
  Qed.

  Theorem partition_length l l1 l2:
    partition l = (l1, l2) ->
    length l = length l1 + length l2.
  Proof.
    revert l1 l2. induction l as [ | a l' Hrec]; intros l1 l2.
    - now intros [= <- <- ].
    - simpl. destruct (f a), (partition l') as (left, right);
      intros [= <- <- ]; simpl; rewrite (Hrec left right); auto.
  Qed.

  Theorem partition_inv_nil (l : list A):
    partition l = ([], []) <-> l = [].
  Proof.
    split.
    - destruct l as [|a l'].
      * intuition.
      * simpl. destruct (f a), (partition l'); now intros [= -> ->].
    - now intros ->.
  Qed.

  Theorem elements_in_partition l l1 l2:
    partition l = (l1, l2) ->
    forall x:A, In x l <-> In x l1 \/ In x l2.
  Proof.
    revert l1 l2. induction l as [| a l' Hrec]; simpl; intros l1 l2 Eq x.
    - injection Eq as <- <-. tauto.
    - destruct (partition l') as (left, right).
      specialize (Hrec left right eq_refl x).
      destruct (f a); injection Eq as <- <-; simpl; tauto.
  Qed.

  End Bool.




  (******************************************************)
  (** ** Operations on lists of pairs or lists of lists *)
  (******************************************************)

  Section ListPairs.
    Variables (A : Type) (B : Type).

  (** [split] derives two lists from a list of pairs *)

    Fixpoint split (l:list (A*B)) : list A * list B :=
      match l with
	| [] => ([], [])
	| (x,y) :: tl => let (left,right) := split tl in (x::left, y::right)
      end.

    Lemma in_split_l : forall (l:list (A*B))(p:A*B),
      In p l -> In (fst p) (fst (split l)).
    Proof.
      induction l; simpl; intros; auto.
      destruct p; destruct a; destruct (split l); simpl in *.
      destruct H.
      injection H; auto.
      right; apply (IHl (a0,b) H).
    Qed.

    Lemma in_split_r : forall (l:list (A*B))(p:A*B),
      In p l -> In (snd p) (snd (split l)).
    Proof.
      induction l; simpl; intros; auto.
      destruct p; destruct a; destruct (split l); simpl in *.
      destruct H.
      injection H; auto.
      right; apply (IHl (a0,b) H).
    Qed.

    Lemma split_nth : forall (l:list (A*B))(n:nat)(d:A*B),
      nth n l d = (nth n (fst (split l)) (fst d), nth n (snd (split l)) (snd d)).
    Proof.
      induction l.
      destruct n; destruct d; simpl; auto.
      destruct n; destruct d; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
      destruct a; destruct (split l); simpl in *; auto.
      apply IHl.
    Qed.

    Lemma split_length_l : forall (l:list (A*B)),
      length (fst (split l)) = length l.
    Proof.
      induction l; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

    Lemma split_length_r : forall (l:list (A*B)),
      length (snd (split l)) = length l.
    Proof.
      induction l; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

  (** [combine] is the opposite of [split].
      Lists given to [combine] are meant to be of same length.
      If not, [combine] stops on the shorter list *)

    Fixpoint combine (l : list A) (l' : list B) : list (A*B) :=
      match l,l' with
	| x::tl, y::tl' => (x,y)::(combine tl tl')
	| _, _ => nil
      end.

    Lemma split_combine : forall (l: list (A*B)),
      let (l1,l2) := split l in combine l1 l2 = l.
    Proof.
      induction l.
      simpl; auto.
      destruct a; simpl.
      destruct (split l); simpl in *.
      f_equal; auto.
    Qed.

    Lemma combine_split : forall (l:list A)(l':list B), length l = length l' ->
      split (combine l l') = (l,l').
    Proof.
      induction l, l'; simpl; trivial; try discriminate.
      now intros [= ->%IHl].
    Qed.

    Lemma in_combine_l : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In x l.
    Proof.
      induction l.
      simpl; auto.
      destruct l'; simpl; auto; intros.
      contradiction.
      destruct H.
      injection H; auto.
      right; apply IHl with l' y; auto.
    Qed.

    Lemma in_combine_r : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In y l'.
    Proof.
      induction l.
      simpl; intros; contradiction.
      destruct l'; simpl; auto; intros.
      destruct H.
      injection H; auto.
      right; apply IHl with x; auto.
    Qed.

    Lemma combine_length : forall (l:list A)(l':list B),
      length (combine l l') = min (length l) (length l').
    Proof.
      induction l.
      simpl; auto.
      destruct l'; simpl; auto.
    Qed.

    Lemma combine_nth : forall (l:list A)(l':list B)(n:nat)(x:A)(y:B),
      length l = length l' ->
      nth n (combine l l') (x,y) = (nth n l x, nth n l' y).
    Proof.
      induction l; destruct l'; intros; try discriminate.
      destruct n; simpl; auto.
      destruct n; simpl in *; auto.
    Qed.

  (** [list_prod] has the same signature as [combine], but unlike
     [combine], it adds every possible pairs, not only those at the
     same position. *)

    Fixpoint list_prod (l:list A) (l':list B) :
      list (A * B) :=
      match l with
	| nil => nil
	| cons x t => (map (fun y:B => (x, y)) l')++(list_prod t l')
      end.

    Lemma in_prod_aux :
      forall (x:A) (y:B) (l:list B),
	In y l -> In (x, y) (map (fun y0:B => (x, y0)) l).
    Proof.
      induction l;
	[ simpl; auto
	  | simpl; destruct 1 as [H1| ];
	    [ left; rewrite H1; trivial | right; auto ] ].
    Qed.

    Lemma in_prod :
      forall (l:list A) (l':list B) (x:A) (y:B),
	In x l -> In y l' -> In (x, y) (list_prod l l').
    Proof.
      induction l;
	[ simpl; tauto
	  | simpl; intros; apply in_or_app; destruct H;
	    [ left; rewrite H; apply in_prod_aux; assumption | right; auto ] ].
    Qed.

    Lemma in_prod_iff :
      forall (l:list A)(l':list B)(x:A)(y:B),
	In (x,y) (list_prod l l') <-> In x l /\ In y l'.
    Proof.
      split; [ | intros; apply in_prod; intuition ].
      induction l; simpl; intros.
      intuition.
      destruct (in_app_or _ _ _ H); clear H.
      destruct (in_map_iff (fun y : B => (a, y)) l' (x,y)) as (H1,_).
      destruct (H1 H0) as (z,(H2,H3)); clear H0 H1.
      injection H2 as -> ->; intuition.
      intuition.
    Qed.

    Lemma prod_length : forall (l:list A)(l':list B),
      length (list_prod l l') = (length l) * (length l').
    Proof.
      induction l; simpl; auto.
      intros.
      rewrite app_length.
      rewrite map_length.
      auto.
    Qed.

  End ListPairs.




(*****************************************)
(** * Miscellaneous operations on lists  *)
(*****************************************)



(******************************)
(** ** Length order of lists  *)
(******************************)

Section length_order.
  Variable A : Type.

  Definition lel (l m:list A) := length l <= length m.

  Variables a b : A.
  Variables l m n : list A.

  Lemma lel_refl : lel l l.
  Proof.
    unfold lel; auto with arith.
  Qed.

  Lemma lel_trans : lel l m -> lel m n -> lel l n.
  Proof.
    unfold lel; intros.
    now_show (length l <= length n).
    apply le_trans with (length m); auto with arith.
  Qed.

  Lemma lel_cons_cons : lel l m -> lel (a :: l) (b :: m).
  Proof.
    unfold lel; simpl; auto with arith.
  Qed.

  Lemma lel_cons : lel l m -> lel l (b :: m).
  Proof.
    unfold lel; simpl; auto with arith.
  Qed.

  Lemma lel_tail : lel (a :: l) (b :: m) -> lel l m.
  Proof.
    unfold lel; simpl; auto with arith.
  Qed.

  Lemma lel_nil : forall l':list A, lel l' nil -> nil = l'.
  Proof.
    intro l'; elim l'; auto with arith.
    intros a' y H H0.
    now_show (nil = a' :: y).
    absurd (S (length y) <= 0); auto with arith.
  Qed.
End length_order.

Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons:
  datatypes.


(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.

  Variable A : Type.

  Definition incl (l m:list A) := forall a:A, In a l -> In a m.
  Hint Unfold incl.

  Lemma incl_refl : forall l:list A, incl l l.
  Proof.
    auto.
  Qed.
  Hint Resolve incl_refl.

  Lemma incl_tl : forall (a:A) (l m:list A), incl l m -> incl l (a :: m).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate incl_tl.

  Lemma incl_tran : forall l m n:list A, incl l m -> incl m n -> incl l n.
  Proof.
    auto.
  Qed.

  Lemma incl_appl : forall l m n:list A, incl l n -> incl l (n ++ m).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate incl_appl.

  Lemma incl_appr : forall l m n:list A, incl l n -> incl l (m ++ n).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate incl_appr.

  Lemma incl_cons :
    forall (a:A) (l m:list A), In a m -> incl l m -> incl (a :: l) m.
  Proof.
    unfold incl; simpl; intros a l m H H0 a0 H1.
    now_show (In a0 m).
    elim H1.
    now_show (a = a0 -> In a0 m).
    elim H1; auto; intro H2.
    now_show (a = a0 -> In a0 m).
    elim H2; auto. (* solves subgoal *)
    now_show (In a0 l -> In a0 m).
    auto.
  Qed.
  Hint Resolve incl_cons.

  Lemma incl_app : forall l m n:list A, incl l n -> incl m n -> incl (l ++ m) n.
  Proof.
    unfold incl; simpl; intros l m n H H0 a H1.
    now_show (In a n).
    elim (in_app_or _ _ _ H1); auto.
  Qed.
  Hint Resolve incl_app.

End SetIncl.

Hint Resolve incl_refl incl_tl incl_tran incl_appl incl_appr incl_cons
  incl_app: datatypes.


(**************************************)
(** * Cutting a list at some position *)
(**************************************)

Section Cutting.

  Variable A : Type.

  Fixpoint firstn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => nil
      | S n => match l with
		 | nil => nil
		 | a::l => a::(firstn n l)
	       end
    end.

  Lemma firstn_nil n: firstn n [] = [].
  Proof. induction n; now simpl. Qed.

  Lemma firstn_cons n a l: firstn (S n) (a::l) = a :: (firstn n l).
  Proof. now simpl. Qed.

  Lemma firstn_all l: firstn (length l) l = l.
  Proof. induction l as [| ? ? H]; simpl; [reflexivity | now rewrite H]. Qed.

  Lemma firstn_all2 n: forall (l:list A), (length l) <= n -> firstn n l = l.
  Proof. induction n as [|k iHk].
    - intro. inversion 1 as [H1|?].
      rewrite (length_zero_iff_nil l) in H1. subst. now simpl.
    - destruct l as [|x xs]; simpl.
      * now reflexivity.
      * simpl. intro H. apply Peano.le_S_n in H. f_equal. apply iHk, H.
  Qed.

  Lemma firstn_O l: firstn 0 l = [].
  Proof. now simpl. Qed.

  Lemma firstn_le_length n: forall l:list A, length (firstn n l) <= n.
  Proof.
    induction n as [|k iHk]; simpl; [auto | destruct l as [|x xs]; simpl].
    - auto with arith.
    - apply Peano.le_n_S, iHk.
  Qed.

  Lemma firstn_length_le: forall l:list A, forall n:nat,
    n <= length l -> length (firstn n l) = n.
  Proof. induction l as [|x xs Hrec].
    - simpl. intros n H. apply le_n_0_eq in H. rewrite <- H. now simpl.
    - destruct n.
      * now simpl.
      * simpl. intro H. apply le_S_n in H. now rewrite (Hrec n H).
  Qed.

  Lemma firstn_app n:
    forall l1 l2,
    firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2).
  Proof. induction n as [|k iHk]; intros l1 l2.
    - now simpl.
    - destruct l1 as [|x xs].
      * unfold firstn at 2, length. now rewrite 2!app_nil_l, <- minus_n_O.
      * rewrite <- app_comm_cons. simpl. f_equal. apply iHk.
  Qed.

  Lemma firstn_app_2 n:
    forall l1 l2,
    firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2.
  Proof. induction n as [| k iHk];intros l1 l2.
    - unfold firstn at 2. rewrite <- plus_n_O, app_nil_r.
      rewrite firstn_app. rewrite <- minus_diag_reverse.
      unfold firstn at 2. rewrite app_nil_r. apply firstn_all.
    - destruct l2 as [|x xs].
      * simpl. rewrite app_nil_r. apply firstn_all2. auto with arith.
      * rewrite firstn_app. assert (H0 : (length l1 + S k - length l1) = S k).
        auto with arith.
        rewrite H0, firstn_all2; [reflexivity | auto with arith].
  Qed.

  Lemma firstn_firstn:
    forall l:list A,
    forall i j : nat,
    firstn i (firstn j l) = firstn (min i j) l.
  Proof. induction l as [|x xs Hl].
    - intros. simpl. now rewrite ?firstn_nil.
    - destruct i.
      * intro. now simpl.
      * destruct j.
        + now simpl.
        + simpl. f_equal. apply Hl.
  Qed.

  Fixpoint skipn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => l
      | S n => match l with
		 | nil => nil
		 | a::l => skipn n l
	       end
    end.

  Lemma firstn_skipn : forall n l, firstn n l ++ skipn n l = l.
  Proof.
    induction n.
    simpl; auto.
    destruct l; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma firstn_length : forall n l, length (firstn n l) = min n (length l).
  Proof.
    induction n; destruct l; simpl; auto.
  Qed.

   Lemma removelast_firstn : forall n l, n < length l ->
     removelast (firstn (S n) l) = firstn n l.
   Proof.
     induction n; destruct l.
     simpl; auto.
     simpl; auto.
     simpl; auto.
     intros.
     simpl in H.
     change (firstn (S (S n)) (a::l)) with ((a::nil)++firstn (S n) l).
     change (firstn (S n) (a::l)) with (a::firstn n l).
     rewrite removelast_app.
     rewrite IHn; auto with arith.

     clear IHn; destruct l; simpl in *; try discriminate.
     inversion_clear H.
     inversion_clear H0.
   Qed.

   Lemma firstn_removelast : forall n l, n < length l ->
     firstn n (removelast l) = firstn n l.
   Proof.
     induction n; destruct l.
     simpl; auto.
     simpl; auto.
     simpl; auto.
     intros.
     simpl in H.
     change (removelast (a :: l)) with (removelast ((a::nil)++l)).
     rewrite removelast_app.
     simpl; f_equal; auto with arith.
     intro H0; rewrite H0 in H; inversion_clear H; inversion_clear H1.
   Qed.

End Cutting.

(**********************************************************************)
(** ** Predicate for List addition/removal (no need for decidability) *)
(**********************************************************************)

Section Add.

  Variable A : Type.

  (* [Add a l l'] means that [l'] is exactly [l], with [a] added
     once somewhere *)
  Inductive Add (a:A) : list A -> list A -> Prop :=
    | Add_head l : Add a l (a::l)
    | Add_cons x l l' : Add a l l' -> Add a (x::l) (x::l').

  Lemma Add_app a l1 l2 : Add a (l1++l2) (l1++a::l2).
  Proof.
   induction l1; simpl; now constructor.
  Qed.

  Lemma Add_split a l l' :
    Add a l l' -> exists l1 l2, l = l1++l2 /\ l' = l1++a::l2.
  Proof.
   induction 1.
   - exists nil; exists l; split; trivial.
   - destruct IHAdd as (l1 & l2 & Hl & Hl').
     exists (x::l1); exists l2; split; simpl; f_equal; trivial.
  Qed.

  Lemma Add_in a l l' : Add a l l' ->
   forall x, In x l' <-> In x (a::l).
  Proof.
   induction 1; intros; simpl in *; rewrite ?IHAdd; tauto.
  Qed.

  Lemma Add_length a l l' : Add a l l' -> length l' = S (length l).
  Proof.
   induction 1; simpl; auto with arith.
  Qed.

  Lemma Add_inv a l : In a l -> exists l', Add a l' l.
  Proof.
   intro Ha. destruct (in_split _ _ Ha) as (l1 & l2 & ->).
   exists (l1 ++ l2). apply Add_app.
  Qed.

  Lemma incl_Add_inv a l u v :
    ~In a l -> incl (a::l) v -> Add a u v -> incl l u.
  Proof.
   intros Ha H AD y Hy.
   assert (Hy' : In y (a::u)).
   { rewrite <- (Add_in AD). apply H; simpl; auto. }
   destruct Hy'; [ subst; now elim Ha | trivial ].
  Qed.

End Add.

(********************************)
(** ** Lists without redundancy *)
(********************************)

Section ReDun.

  Variable A : Type.

  Inductive NoDup : list A -> Prop :=
    | NoDup_nil : NoDup nil
    | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l).

  Lemma NoDup_Add a l l' : Add a l l' -> (NoDup l' <-> NoDup l /\ ~In a l).
  Proof.
   induction 1 as [l|x l l' AD IH].
   - split; [ inversion_clear 1; now split | now constructor ].
   - split.
     + inversion_clear 1. rewrite IH in *. rewrite (Add_in AD) in *.
       simpl in *; split; try constructor; intuition.
     + intros (N,IN). inversion_clear N. constructor.
       * rewrite (Add_in AD); simpl in *; intuition.
       * apply IH. split; trivial. simpl in *; intuition.
  Qed.

  Lemma NoDup_remove l l' a :
    NoDup (l++a::l') -> NoDup (l++l') /\ ~In a (l++l').
  Proof.
  apply NoDup_Add. apply Add_app.
  Qed.

  Lemma NoDup_remove_1 l l' a : NoDup (l++a::l') -> NoDup (l++l').
  Proof.
  intros. now apply NoDup_remove with a.
  Qed.

  Lemma NoDup_remove_2 l l' a : NoDup (l++a::l') -> ~In a (l++l').
  Proof.
  intros. now apply NoDup_remove.
  Qed.

  Theorem NoDup_cons_iff a l:
    NoDup (a::l) <-> ~ In a l /\ NoDup l.
  Proof.
    split.
    + inversion_clear 1. now split.
    + now constructor.
  Qed.

  (** Effective computation of a list without duplicates *)

  Hypothesis decA: forall x y : A, {x = y} + {x <> y}.

  Fixpoint nodup (l : list A) : list A :=
    match l with
      | [] => []
      | x::xs => if in_dec decA x xs then nodup xs else x::(nodup xs)
    end.

  Lemma nodup_In l x : In x (nodup l) <-> In x l.
  Proof.
    induction l as [|a l' Hrec]; simpl.
    - reflexivity.
    - destruct (in_dec decA a l'); simpl; rewrite Hrec.
      * intuition; now subst.
      * reflexivity.
  Qed.

  Lemma NoDup_nodup l: NoDup (nodup l).
  Proof.
    induction l as [|a l' Hrec]; simpl.
    - constructor.
    - destruct (in_dec decA a l'); simpl.
      * assumption.
      * constructor; [ now rewrite nodup_In | assumption].
  Qed.

  Lemma nodup_inv k l a : nodup k = a :: l -> ~ In a l.
  Proof.
    intros H.
    assert (H' : NoDup (a::l)).
    { rewrite <- H. apply NoDup_nodup. }
    now inversion_clear H'.
  Qed.

  Theorem NoDup_count_occ l:
    NoDup l <-> (forall x:A, count_occ decA l x <= 1).
  Proof.
    induction l as [| a l' Hrec].
    - simpl; split; auto. constructor.
    - rewrite NoDup_cons_iff, Hrec, (count_occ_not_In decA). clear Hrec. split.
      + intros (Ha, H) x. simpl. destruct (decA a x); auto.
        subst; now rewrite Ha.
      + split.
        * specialize (H a). rewrite count_occ_cons_eq in H; trivial.
          now inversion H.
        * intros x. specialize (H x). simpl in *. destruct (decA a x); auto.
          now apply Nat.lt_le_incl.
  Qed.

  Theorem NoDup_count_occ' l:
    NoDup l <-> (forall x:A, In x l -> count_occ decA l x = 1).
  Proof.
    rewrite NoDup_count_occ.
    setoid_rewrite (count_occ_In decA). unfold gt, lt in *.
    split; intros H x; specialize (H x);
    set (n := count_occ decA l x) in *; clearbody n.
    (* the rest would be solved by omega if we had it here... *)
    - now apply Nat.le_antisymm.
    - destruct (Nat.le_gt_cases 1 n); trivial.
      + rewrite H; trivial.
      + now apply Nat.lt_le_incl.
  Qed.

  (** Alternative characterisations of being without duplicates,
      thanks to [nth_error] and [nth] *)

  Lemma NoDup_nth_error l :
    NoDup l <->
    (forall i j, i<length l -> nth_error l i = nth_error l j -> i = j).
  Proof.
    split.
    { intros H; induction H as [|a l Hal Hl IH]; intros i j Hi E.
      - inversion Hi.
      - destruct i, j; simpl in *; auto.
        * elim Hal. eapply nth_error_In; eauto.
        * elim Hal. eapply nth_error_In; eauto.
        * f_equal. apply IH; auto with arith. }
    { induction l as [|a l]; intros H; constructor.
      * intro Ha. apply In_nth_error in Ha. destruct Ha as (n,Hn).
        assert (n < length l) by (now rewrite <- nth_error_Some, Hn).
        specialize (H 0 (S n)). simpl in H. discriminate H; auto with arith.
      * apply IHl.
        intros i j Hi E. apply eq_add_S, H; simpl; auto with arith. }
  Qed.

  Lemma NoDup_nth l d :
    NoDup l <->
    (forall i j, i<length l -> j<length l ->
       nth i l d = nth j l d -> i = j).
  Proof.
    split.
    { intros H; induction H as [|a l Hal Hl IH]; intros i j Hi Hj E.
      - inversion Hi.
      - destruct i, j; simpl in *; auto.
        * elim Hal. subst a. apply nth_In; auto with arith.
        * elim Hal. subst a. apply nth_In; auto with arith.
        * f_equal. apply IH; auto with arith. }
    { induction l as [|a l]; intros H; constructor.
      * intro Ha. eapply In_nth in Ha. destruct Ha as (n & Hn & Hn').
        specialize (H 0 (S n)). simpl in H. discriminate H; eauto with arith.
      * apply IHl.
        intros i j Hi Hj E. apply eq_add_S, H; simpl; auto with arith. }
  Qed.

  (** Having [NoDup] hypotheses bring more precise facts about [incl]. *)

  Lemma NoDup_incl_length l l' :
    NoDup l -> incl l l' -> length l <= length l'.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH]; simpl.
   - auto with arith.
   - intros l' H.
     destruct (Add_inv a l') as (l'', AD). { apply H; simpl; auto. }
     rewrite (Add_length AD). apply le_n_S. apply IH.
     now apply incl_Add_inv with a l'.
  Qed.

  Lemma NoDup_length_incl l l' :
    NoDup l -> length l' <= length l -> incl l l' -> incl l' l.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH].
   - destruct l'; easy.
   - intros l' E H x Hx.
     destruct (Add_inv a l') as (l'', AD). { apply H; simpl; auto. }
     rewrite (Add_in AD) in Hx. simpl in Hx.
     destruct Hx as [Hx|Hx]; [left; trivial|right].
     revert x Hx. apply (IH l''); trivial.
     * apply le_S_n. now rewrite <- (Add_length AD).
     * now apply incl_Add_inv with a l'.
  Qed.

End ReDun.

(** NoDup and map *)

(** NB: the reciprocal result holds only for injective functions,
    see FinFun.v *)

Lemma NoDup_map_inv A B (f:A->B) l : NoDup (map f l) -> NoDup l.
Proof.
 induction l; simpl; inversion_clear 1; subst; constructor; auto.
 intro H. now apply (in_map f) in H.
Qed.

(***********************************)
(** ** Sequence of natural numbers *)
(***********************************)

Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)

  Fixpoint seq (start len:nat) : list nat :=
    match len with
      | 0 => nil
      | S len => start :: seq (S start) len
    end.

  Lemma seq_length : forall len start, length (seq start len) = len.
  Proof.
    induction len; simpl; auto.
  Qed.

  Lemma seq_nth : forall len start n d,
    n < len -> nth n (seq start len) d = start+n.
  Proof.
    induction len; intros.
    inversion H.
    simpl seq.
    destruct n; simpl.
    auto with arith.
    rewrite IHlen;simpl; auto with arith.
  Qed.

  Lemma seq_shift : forall len start,
    map S (seq start len) = seq (S start) len.
  Proof.
    induction len; simpl; auto.
    intros.
    rewrite IHlen.
    auto with arith.
  Qed.

  Lemma in_seq len start n :
    In n (seq start len) <-> start <= n < start+len.
  Proof.
   revert start. induction len; simpl; intros.
   - rewrite <- plus_n_O. split;[easy|].
     intros (H,H'). apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H H')).
   - rewrite IHlen, <- plus_n_Sm; simpl; split.
     * intros [H|H]; subst; intuition auto with arith.
     * intros (H,H'). destruct (Lt.le_lt_or_eq _ _ H); intuition.
  Qed.

  Lemma seq_NoDup len start : NoDup (seq start len).
  Proof.
   revert start; induction len; simpl; constructor; trivial.
   rewrite in_seq. intros (H,_). apply (Lt.lt_irrefl _ H).
  Qed.

End NatSeq.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate.

    Variable P:A->Prop.

    Inductive Exists : list A -> Prop :=
      | Exists_cons_hd : forall x l, P x -> Exists (x::l)
      | Exists_cons_tl : forall x l, Exists l -> Exists (x::l).

    Hint Constructors Exists.

    Lemma Exists_exists (l:list A) :
      Exists l <-> (exists x, In x l /\ P x).
    Proof.
      split.
      - induction 1; firstorder.
      - induction l; firstorder; subst; auto.
    Qed.

    Lemma Exists_nil : Exists nil <-> False.
    Proof. split; inversion 1. Qed.

    Lemma Exists_cons x l:
      Exists (x::l) <-> P x \/ Exists l.
    Proof. split; inversion 1; auto. Qed.

    Lemma Exists_dec l:
      (forall x:A, {P x} + { ~ P x }) ->
      {Exists l} + {~ Exists l}.
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - right. abstract now rewrite Exists_nil.
      - destruct Hrec as [Hl'|Hl'].
        * left. now apply Exists_cons_tl.
        * destruct (Pdec a) as [Ha|Ha].
          + left. now apply Exists_cons_hd.
          + right. abstract now inversion 1.
    Defined.

    Inductive Forall : list A -> Prop :=
      | Forall_nil : Forall nil
      | Forall_cons : forall x l, P x -> Forall l -> Forall (x::l).

    Hint Constructors Forall.

    Lemma Forall_forall (l:list A):
      Forall l <-> (forall x, In x l -> P x).
    Proof.
      split.
      - induction 1; firstorder; subst; auto.
      - induction l; firstorder.
    Qed.

    Lemma Forall_inv : forall (a:A) l, Forall (a :: l) -> P a.
    Proof.
      intros; inversion H; trivial.
    Qed.

    Lemma Forall_rect : forall (Q : list A -> Type),
      Q [] -> (forall b l, P b -> Q (b :: l)) -> forall l, Forall l -> Q l.
    Proof.
      intros Q H H'; induction l; intro; [|eapply H', Forall_inv]; eassumption.
    Qed.

    Lemma Forall_dec :
      (forall x:A, {P x} + { ~ P x }) ->
      forall l:list A, {Forall l} + {~ Forall l}.
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - left. apply Forall_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_cons.
          * right. abstract now inversion 1.
        + right. abstract now inversion 1.
    Defined.

  End One_predicate.

  Lemma Forall_Exists_neg (P:A->Prop)(l:list A) :
   Forall (fun x => ~ P x) l <-> ~(Exists P l).
  Proof.
   rewrite Forall_forall, Exists_exists. firstorder.
  Qed.

  Lemma Exists_Forall_neg (P:A->Prop)(l:list A) :
    (forall x, P x \/ ~P x) ->
    Exists (fun x => ~ P x) l <-> ~(Forall P l).
  Proof.
   intro Dec.
   split.
   - rewrite Forall_forall, Exists_exists; firstorder.
   - intros NF.
     induction l as [|a l IH].
     + destruct NF. constructor.
     + destruct (Dec a) as [Ha|Ha].
       * apply Exists_cons_tl, IH. contradict NF. now constructor.
       * now apply Exists_cons_hd.
  Qed.

  Lemma neg_Forall_Exists_neg (P:A->Prop) (l:list A) :
    (forall x:A, {P x} + { ~ P x }) ->
    ~ Forall P l ->
    Exists (fun x => ~ P x) l.
  Proof.
    intro Dec.
    apply Exists_Forall_neg; intros.
    destruct (Dec x); auto.
  Qed.

  Lemma Forall_Exists_dec (P:A->Prop) :
    (forall x:A, {P x} + { ~ P x }) ->
    forall l:list A,
    {Forall P l} + {Exists (fun x => ~ P x) l}.
  Proof.
    intros Pdec l.
    destruct (Forall_dec P Pdec l); [left|right]; trivial.
    now apply neg_Forall_Exists_neg.
  Defined.

  Lemma Forall_impl : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
    forall l, Forall P l -> Forall Q l.
  Proof.
    intros P Q H l. rewrite !Forall_forall. firstorder.
  Qed.

End Exists_Forall.

Hint Constructors Exists.
Hint Constructors Forall.

Section Forall2.

  (** [Forall2]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Prop.

  Inductive Forall2 : list A -> list B -> Prop :=
    | Forall2_nil : Forall2 [] []
    | Forall2_cons : forall x y l l',
      R x y -> Forall2 l l' -> Forall2 (x::l) (y::l').

  Hint Constructors Forall2.

  Theorem Forall2_refl : Forall2 [] [].
  Proof. intros; apply Forall2_nil. Qed.

  Theorem Forall2_app_inv_l : forall l1 l2 l',
    Forall2 (l1 ++ l2) l' ->
    exists l1' l2', Forall2 l1 l1' /\ Forall2 l2 l2' /\ l' = l1' ++ l2'.
  Proof.
    induction l1; intros.
      exists [], l'; auto.
      simpl in H; inversion H; subst; clear H.
      apply IHl1 in H4 as (l1' & l2' & Hl1 & Hl2 & ->).
      exists (y::l1'), l2'; simpl; auto.
  Qed.

  Theorem Forall2_app_inv_r : forall l1' l2' l,
    Forall2 l (l1' ++ l2') ->
    exists l1 l2, Forall2 l1 l1' /\ Forall2 l2 l2' /\ l = l1 ++ l2.
  Proof.
    induction l1'; intros.
      exists [], l; auto.
      simpl in H; inversion H; subst; clear H.
      apply IHl1' in H4 as (l1 & l2 & Hl1 & Hl2 & ->).
      exists (x::l1), l2; simpl; auto.
  Qed.

  Theorem Forall2_app : forall l1 l2 l1' l2',
    Forall2 l1 l1' -> Forall2 l2 l2' -> Forall2 (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros. induction l1 in l1', H, H0 |- *; inversion H; subst; simpl; auto.
  Qed.
End Forall2.

Hint Constructors Forall2.

Section ForallPairs.

  (** [ForallPairs] : specifies that a certain relation should
    always hold when inspecting all possible pairs of elements of a list. *)

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Definition ForallPairs l :=
    forall a b, In a l -> In b l -> R a b.

  (** [ForallOrdPairs] : we still check a relation over all pairs
     of elements of a list, but now the order of elements matters. *)

  Inductive ForallOrdPairs : list A -> Prop :=
    | FOP_nil : ForallOrdPairs nil
    | FOP_cons : forall a l,
      Forall (R a) l -> ForallOrdPairs l -> ForallOrdPairs (a::l).

  Hint Constructors ForallOrdPairs.

  Lemma ForallOrdPairs_In : forall l,
    ForallOrdPairs l ->
    forall x y, In x l -> In y l -> x=y \/ R x y \/ R y x.
  Proof.
    induction 1.
    inversion 1.
    simpl; destruct 1; destruct 1; subst; auto.
    right; left. apply -> Forall_forall; eauto.
    right; right. apply -> Forall_forall; eauto.
  Qed.

  (** [ForallPairs] implies [ForallOrdPairs]. The reverse implication is true
    only when [R] is symmetric and reflexive. *)

  Lemma ForallPairs_ForallOrdPairs l: ForallPairs l -> ForallOrdPairs l.
  Proof.
    induction l; auto. intros H.
    constructor.
    apply <- Forall_forall. intros; apply H; simpl; auto.
    apply IHl. red; intros; apply H; simpl; auto.
  Qed.

  Lemma ForallOrdPairs_ForallPairs :
    (forall x, R x x) ->
    (forall x y, R x y -> R y x) ->
    forall l, ForallOrdPairs l -> ForallPairs l.
  Proof.
    intros Refl Sym l Hl x y Hx Hy.
    destruct (ForallOrdPairs_In Hl _ _ Hx Hy); subst; intuition.
  Qed.
End ForallPairs.

(** * Inversion of predicates over lists based on head symbol *)

Ltac is_list_constr c :=
 match c with
  | nil => idtac
  | (_::_) => idtac
  | _ => fail
 end.

Ltac invlist f :=
 match goal with
  | H:f ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ _ _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ _ _ _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | _ => idtac
 end.



(** * Exporting hints and tactics *)


Hint Rewrite
  rev_involutive (* rev (rev l) = l *)
  rev_unit (* rev (l ++ a :: nil) = a :: rev l *)
  map_nth (* nth n (map f l) (f d) = f (nth n l d) *)
  map_length (* length (map f l) = length l *)
  seq_length (* length (seq start len) = len *)
  app_length (* length (l ++ l') = length l + length l' *)
  rev_length (* length (rev l) = length l *)
  app_nil_r (* l ++ nil = l *)
  : list.

Ltac simpl_list := autorewrite with list.
Ltac ssimpl_list := autorewrite with list using simpl.

(* begin hide *)
(* Compatibility notations after the migration of [list] to [Datatypes] *)
Notation list := list (only parsing).
Notation list_rect := list_rect (only parsing).
Notation list_rec := list_rec (only parsing).
Notation list_ind := list_ind (only parsing).
Notation nil := nil (only parsing).
Notation cons := cons (only parsing).
Notation length := length (only parsing).
Notation app := app (only parsing).
(* Compatibility Names *)
Notation tail := tl (only parsing).
Notation head := hd_error (only parsing).
Notation head_nil := hd_error_nil (only parsing).
Notation head_cons := hd_error_cons (only parsing).
Notation ass_app := app_assoc (only parsing).
Notation app_ass := app_assoc_reverse (only parsing).
Notation In_split := in_split (only parsing).
Notation In_rev := in_rev (only parsing).
Notation In_dec := in_dec (only parsing).
Notation distr_rev := rev_app_distr (only parsing).
Notation rev_acc := rev_append (only parsing).
Notation rev_acc_rev := rev_append_rev (only parsing).
Notation AllS := Forall (only parsing). (* was formerly in TheoryList *)

Hint Resolve app_nil_end : datatypes.
(* end hide *)

Section Repeat.

  Variable A : Type.
  Fixpoint repeat (x : A) (n: nat ) :=
    match n with
      | O => []
      | S k => x::(repeat x k)
    end.

  Theorem repeat_length x n:
    length (repeat x n) = n.
  Proof.
    induction n as [| k Hrec]; simpl; rewrite ?Hrec; reflexivity.
  Qed.

  Theorem repeat_spec n x y:
    In y (repeat x n) -> y=x.
  Proof.
    induction n as [|k Hrec]; simpl; destruct 1; auto.
  Qed.

End Repeat.

(* Unset Universe Polymorphism. *)
