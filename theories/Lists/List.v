(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PeanoNat.
Require Import Morphisms.
Require Export ListDef.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

(******************************************************************)
(** * Basics: definition of polymorphic lists and some operations *)
(******************************************************************)

(** The definition of [list] is now in [Init/Datatypes],
    as well as the definitions of [length] and [app] *)

#[local] Open Scope bool_scope.
Open Scope list_scope.

(** Standard notations for lists.
In a special module to avoid conflicts. *)
Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : list_scope.
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
      | [] => []
      | _ :: l' => l'
    end.

  (** The [In] predicate *)
  Fixpoint In (a:A) (l:list A) : Prop :=
    match l with
      | [] => False
      | b :: l' => b = a \/ In a l'
    end.

End Lists.

Section Facts.

  Variable A : Type.

  (** *** Generic facts *)

  (** Discrimination *)
  Theorem nil_cons (x:A) (l:list A) : [] <> x :: l.
  Proof.
    discriminate.
  Qed.


  (** Destruction *)

  Theorem destruct_list (l : list A) : {x:A & {tl:list A | l = x::tl}}+{l = []}.
  Proof.
    induction l as [|a tail].
    - right; reflexivity.
    - left; exists a, tail; reflexivity.
  Qed.

  Lemma hd_error_tl_repr l (a:A) r :
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof.
    destruct l as [|x xs]; [easy|cbn;split].
    - now intros [[= ->] ->].
    - now intros [= -> ->].
  Qed.

  Lemma hd_error_some_nil l (a:A) : hd_error l = Some a -> l <> [].
  Proof. unfold hd_error. destruct l; now discriminate. Qed.

  Theorem length_zero_iff_nil (l : list A):
    length l = 0 <-> l = [].
  Proof.
    split; [now destruct l | now intros ->].
  Qed.

  (** *** Head and tail *)

  Theorem hd_error_nil : hd_error (@nil A) = None.
  Proof.
    reflexivity.
  Qed.

  Theorem hd_error_cons (l : list A) (x : A) : hd_error (x::l) = Some x.
  Proof.
    reflexivity.
  Qed.


  (**************************)
  (** *** Facts about [app] *)
  (**************************)

  (** Discrimination *)
  Theorem app_cons_not_nil (x y:list A) (a:A) : [] <> x ++ a :: y.
  Proof.
    now destruct x.
  Qed.


  (** Concat with [nil] *)
  Theorem app_nil_l (l:list A) : [] ++ l = l.
  Proof.
    reflexivity.
  Qed.

  Theorem app_nil_r (l:list A) : l ++ [] = l.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  (* begin hide *)
  (* Deprecated since 8.3 but attribute added in 8.18 *)
  Theorem app_nil_end_deprecated (l:list A) : l = l ++ [].
  Proof. symmetry; apply app_nil_r. Qed.
  (* end hide *)

  (** [app] is associative *)
  Theorem app_assoc (l m n:list A) : l ++ m ++ n = (l ++ m) ++ n.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  (* begin hide *)
  (* Deprecated since 8.3 but attribute added in 8.18 *)
  Theorem app_assoc_reverse_deprecated (l m n:list A) : (l ++ m) ++ n = l ++ m ++ n.
  Proof. symmetry; apply app_assoc. Qed.
  (* end hide *)

  (** [app] commutes with [cons] *)
  Theorem app_comm_cons (x y:list A) (a:A) : a :: (x ++ y) = (a :: x) ++ y.
  Proof.
    reflexivity.
  Qed.

  (** Facts deduced from the result of a concatenation *)

  Theorem app_eq_nil (l l':list A) : l ++ l' = [] -> l = [] /\ l' = [].
  Proof.
    now destruct l, l'.
  Qed.

  Lemma app_eq_cons x y z (a : A):
    x ++ y = a :: z -> (x = [] /\ y = a :: z) \/ exists x', x = a :: x' /\ z = x' ++ y.
  Proof.
    intro H. destruct x as [|b x].
    - now left.
    - right. injection H as ->. now exists x.
  Qed.

  Theorem app_eq_unit (x y:list A) (a:A) :
      x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof.
    destruct x; cbn.
    - intros ->. now left.
    - intros [= -> [-> ->] %app_eq_nil]. now right.
  Qed.

  Lemma elt_eq_unit l1 l2 (a b : A) :
    l1 ++ a :: l2 = [b] -> a = b /\ l1 = [] /\ l2 = [].
  Proof.
    intros Heq.
    apply app_eq_unit in Heq.
    now destruct Heq as [[Heq1 Heq2]|[Heq1 Heq2]]; inversion_clear Heq2.
  Qed.

  Theorem app_eq_app X (x1 x2 y1 y2: list X) : x1++x2 = y1++y2 ->
    exists l, (x1 = y1++l /\ y2 = l++x2) \/ (y1 = x1++l /\ x2 = l++y2).
  Proof.
    revert y1. induction x1 as [|a x1 IH].
    - cbn. intros y1 ->. exists y1. now right.
    - intros [|b y1]; cbn.
      + intros <-. exists (a :: x1). now left.
      + intros [=-> [l Hl] %IH]. exists l.
        now destruct Hl as [[-> ->]|[-> ->]]; [left|right].
  Qed.

  Lemma app_inj_tail :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof.
    intros x y a b [l [[-> Hl %eq_sym]|[-> Hl %eq_sym]]] %app_eq_app;
      apply elt_eq_unit in Hl as [? [-> ?]]; now rewrite app_nil_r.
  Qed.

  Lemma app_inj_tail_iff :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] <-> x = y /\ a = b.
  Proof.
    intros. now split; [apply app_inj_tail|intros [-> ->]].
  Qed.

  (** Compatibility with other operations *)

  Lemma length_nil : length (@nil A) = 0.
  Proof.
    reflexivity.
  Qed.

  Lemma length_cons : forall (l : list A) a, length (a :: l) = S (length l).
  Proof.
    reflexivity.
  Qed.

  Lemma length_app : forall l l' : list A, length (l++l') = length l + length l'.
  Proof.
    intro l; induction l; simpl; auto.
  Qed.

  Lemma last_length : forall (l : list A) a, length (l ++ [a]) = S (length l).
  Proof.
    intros ; rewrite length_app ; simpl.
    rewrite Nat.add_succ_r, Nat.add_0_r; reflexivity.
  Qed.

  Lemma app_inv_head_iff:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 <-> l1 = l2.
  Proof.
    intro l; induction l as [|? l IHl]; split; intros H; simpl; auto.
    - apply IHl. inversion H. auto.
    - subst. auto.
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    apply app_inv_head_iff.
  Qed.

  Lemma app_inv_tail:
    forall l l1 l2 : list A, l1 ++ l = l2 ++ l -> l1 = l2.
  Proof.
    intros l. induction l as [|a l IHl].
    - intros ? ?. now rewrite !app_nil_r.
    - intros ? ?. change (a :: l) with ([a] ++ l).
      rewrite !app_assoc. now intros [? ?] %IHl %app_inj_tail_iff.
  Qed.

  Lemma app_inv_tail_iff:
    forall l l1 l2 : list A, l1 ++ l = l2 ++ l <-> l1 = l2.
  Proof.
    split; [apply app_inv_tail | now intros ->].
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

  Lemma in_app_or : forall (l m:list A) (a:A), In a (l ++ m) -> In a l \/ In a m.
  Proof.
    intros l m a. induction l; cbn; tauto.
  Qed.

  Lemma in_or_app : forall (l m:list A) (a:A), In a l \/ In a m -> In a (l ++ m).
  Proof.
    intros l m a. induction l; cbn; tauto.
  Qed.

  Lemma in_app_iff : forall l l' (a:A), In a (l++l') <-> In a l \/ In a l'.
  Proof.
    split; auto using in_app_or, in_or_app.
  Qed.

  Theorem in_split : forall x (l:list A), In x l -> exists l1 l2, l = l1++x::l2.
  Proof.
  intros x l; induction l as [|a l IHl]; simpl; [destruct 1|destruct 1 as [?|H]].
  - subst a; auto.
    exists [], l; auto.
  - destruct (IHl H) as (l1,(l2,H0)).
    exists (a::l1), l2; simpl. apply f_equal. auto.
  Qed.

  Lemma in_elt : forall (x:A) l1 l2, In x (l1 ++ x :: l2).
  Proof.
  intros.
  apply in_or_app.
  right; left; reflexivity.
  Qed.

  Lemma in_elt_inv : forall (x y : A) l1 l2,
    In x (l1 ++ y :: l2) -> x = y \/ In x (l1 ++ l2).
  Proof.
  intros x y l1 l2 Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin|[Hin|Hin]]; [right|left|right]; try apply in_or_app; intuition.
  Qed.

  Lemma app_inj_pivot x1 x2 y1 y2 (a : A): x1 ++ a :: x2 = y1 ++ a :: y2 ->
    ((In a x1 /\ In a y2) \/ (In a x2 /\ In a y1)) \/ (x1 = y1 /\ x2 = y2).
  Proof.
    induction y1 as [|b y1 IHy] in x1 |- *; intros [[-> H]|[x' [-> H]]]%app_eq_cons.
    - right. now injection H.
    - subst y2.
      left; left. split; [apply in_eq | apply in_elt].
    - injection H as -> ->.
      left; right. split; [ apply in_elt | apply in_eq ].
    - symmetry in H. apply IHy in H as [[[]|[]]|[]].
      + left; left. split; [apply in_cons|]; assumption.
      + left; right. split; [|apply in_cons]; assumption.
      + right. split; congruence.
  Qed.

  (** Inversion *)
  Lemma in_inv : forall (a b:A) (l:list A), In b (a :: l) -> a = b \/ In b l.
  Proof. easy. Qed.

  (** Decidability of [In] *)
  Theorem in_dec :
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (a:A) (l:list A), {In a l} + {~ In a l}.
  Proof.
    intros H a l; induction l as [| a0 l IHl].
    - right; apply in_nil.
    - destruct (H a0 a); simpl; auto.
      destruct IHl; simpl; auto.
      right; unfold not; intros [Hc1| Hc2]; auto.
  Defined.

  Lemma length_tl l : length (@tl A l) = length l - 1.
  Proof. case l; cbn [length tl Nat.sub]; auto using Nat.sub_0_r. Qed.
End Facts.

#[global]
Hint Resolve app_assoc app_assoc_reverse_deprecated: datatypes.
#[global]
Hint Resolve app_comm_cons app_cons_not_nil: datatypes.
#[global]
Hint Immediate app_eq_nil: datatypes.
#[global]
Hint Resolve app_eq_unit app_inj_tail: datatypes.
#[global]
Hint Resolve in_eq in_cons in_inv in_nil in_app_or in_or_app: datatypes.

(* XXX declare datatypes db and move to top of file *)
Local Ltac Tauto.intuition_solver ::= auto with datatypes.



(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Local Notation nth := (@nth A).

  Fixpoint nth_ok (n:nat) (l:list A) (default:A) {struct l} : bool :=
    match n, l with
      | O, x :: l' => true
      | O, [] => false
      | S m, [] => false
      | S m, x :: l' => nth_ok m l' default
    end.

  Lemma nth_in_or_default :
    forall (n:nat) (l:list A) (d:A), {In (nth n l d) l} + {nth n l d = d}.
  Proof.
    intros n l d; revert n; induction l as [|? ? IHl].
    - intro n; right; destruct n; trivial.
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
      | S n, _ :: l' => nth_error l' n
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
    unfold nth_default; intro n; induction n; intros [ | ] ?; simpl; auto.
  Qed.

  (** Results about [nth] *)

  Lemma nth_In :
    forall (n:nat) (l:list A) (d:A), n < length l -> In (nth n l d) l.
  Proof.
    unfold lt; intro n; induction n as [| n hn]; simpl; intro l.
    - destruct l; simpl; [ inversion 2 | auto ].
    - destruct l; simpl.
      * inversion 2.
      * intros d ie; right; apply hn. now apply Nat.succ_le_mono.
  Qed.

  Lemma In_nth l x d : In x l ->
    exists n, n < length l /\ nth n l d = x.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      * subst; exists 0; simpl; auto using Nat.lt_0_succ.
      * destruct (IH H) as (n & Hn & Hn').
        apply Nat.succ_lt_mono in Hn. now exists (S n).
  Qed.

  Lemma nth_overflow : forall l n d, length l <= n -> nth n l d = d.
  Proof.
    intro l; induction l as [|? ? IHl]; intro n; destruct n;
     simpl; intros d H; auto.
    - inversion H.
    - apply IHl. now apply Nat.succ_le_mono.
  Qed.

  Lemma nth_indep :
    forall l n d d', n < length l -> nth n l d = nth n l d'.
  Proof.
    intro l; induction l as [|? ? IHl].
    - inversion 1.
    - intros [|n] d d'; [intros; reflexivity|].
      intros H. apply IHl. now apply Nat.succ_lt_mono.
  Qed.

  Lemma app_nth1 :
    forall l l' d n, n < length l -> nth n (l++l') d = nth n l d.
  Proof.
    intro l; induction l as [|? ? IHl].
    - inversion 1.
    - intros l' d [|n]; simpl; [intros; reflexivity|].
      intros H. apply IHl. now apply Nat.succ_lt_mono.
  Qed.

  Lemma app_nth2 :
    forall l l' d n, n >= length l -> nth n (l++l') d = nth (n-length l) l' d.
  Proof.
    intro l; induction l as [|? ? IHl]; intros l' d [|n]; auto.
    - inversion 1.
    - intros; simpl; rewrite IHl; [reflexivity|now apply Nat.succ_le_mono].
  Qed.

  Lemma app_nth2_plus : forall l l' d n,
    nth (length l + n) (l ++ l') d = nth n l' d.
  Proof.
    intros.
    now rewrite app_nth2, Nat.add_comm, Nat.add_sub; [|apply Nat.le_add_r].
  Qed.

  Lemma nth_middle : forall l l' a d,
    nth (length l) (l ++ a :: l') d = a.
  Proof.
    intros.
    rewrite <- Nat.add_0_r at 1.
    apply app_nth2_plus.
  Qed.

  Lemma nth_split n l d : n < length l ->
    exists l1, exists l2, l = l1 ++ nth n l d :: l2 /\ length l1 = n.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|a l] H; try easy.
    - exists nil; exists l; now simpl.
    - destruct (IH l) as (l1 & l2 & Hl & Hl1); [now apply Nat.succ_lt_mono|].
      exists (a::l1); exists l2; simpl; split; now f_equal.
  Qed.

  Lemma nth_ext : forall l l' d d', length l = length l' ->
    (forall n, n < length l -> nth n l d = nth n l' d') -> l = l'.
  Proof.
    intro l; induction l as [|a l IHl];
     intros l' d d' Hlen Hnth; destruct l' as [| b l'].
    - reflexivity.
    - inversion Hlen.
    - inversion Hlen.
    - change a with (nth 0 (a :: l) d).
      change b with (nth 0 (b :: l') d').
      rewrite Hnth; f_equal.
      + apply IHl with d d'; [ now inversion Hlen | ].
        intros n Hlen'; apply (Hnth (S n)).
        now apply (Nat.succ_lt_mono n (length l)).
      + simpl; apply Nat.lt_0_succ.
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
    - intros [H|[n ?] %IH].
      + subst; now exists 0.
      + now exists (S n).
  Qed.

  Lemma In_iff_nth_error l x : In x l <-> exists n, nth_error l n = Some x.
  Proof. firstorder eauto using In_nth_error, nth_error_In. Qed.

  Lemma nth_error_None l n : nth_error l n = None <-> length l <= n.
  Proof.
    revert n. induction l as [|? ? IHl]; intro n; destruct n; simpl.
    - split; auto.
    - now split; intros; [apply Nat.le_0_l|].
    - now split; [|intros ? %Nat.nle_succ_0].
    - now rewrite IHl, Nat.succ_le_mono.
  Qed.

  Lemma nth_error_Some l n : nth_error l n <> None <-> n < length l.
  Proof.
   revert n. induction l as [|? ? IHl]; intro n; destruct n; simpl.
    - split; [now destruct 1 | inversion 1].
    - split; [now destruct 1 | inversion 1].
    - now split; intros; [apply Nat.lt_0_succ|].
    - now rewrite IHl, Nat.succ_lt_mono.
  Qed.

  Lemma nth_error_split l n a : nth_error l n = Some a ->
    exists l1, exists l2, l = l1 ++ a :: l2 /\ length l1 = n.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|x l] H; [easy| |easy|].
    - exists nil; exists l. now injection H as [= ->].
    - destruct (IH _ H) as (l1 & l2 & H1 & H2).
      exists (x::l1); exists l2; simpl; split; now f_equal.
  Qed.

  Lemma nth_error_app1 l l' n : n < length l ->
    nth_error (l++l') n = nth_error l n.
  Proof.
    revert l.
    induction n as [|n IHn]; intros [|a l] H; [easy ..|].
    cbn. now apply IHn, Nat.succ_le_mono.
  Qed.

  Lemma nth_error_app2 l l' n : length l <= n ->
    nth_error (l++l') n = nth_error l' (n-length l).
  Proof.
    revert l.
    induction n as [|n IHn]; intros [|a l] H; [easy ..|].
    cbn. now apply IHn, Nat.succ_le_mono.
  Qed.

  Lemma nth_error_app l l' n : nth_error (l ++ l') n =
    if Nat.ltb n (length l)
    then nth_error l n
    else nth_error l' (n - length l).
  Proof.
    case (Nat.ltb_spec n (length l)) as [].
    - rewrite nth_error_app1; trivial.
    - rewrite nth_error_app2; trivial.
  Qed.

  Lemma nth_error_ext l l':
    (forall n, nth_error l n = nth_error l' n) -> l = l'.
  Proof.
    revert l'. induction l as [|a l IHl];
      intros l' Hnth; destruct l'.
    - reflexivity.
    - discriminate (Hnth 0).
    - discriminate (Hnth 0).
    - injection (Hnth 0) as ->. f_equal. apply IHl.
      intro n. exact (Hnth (S n)).
  Qed.

  Lemma unfold_nth_error l n
    : nth_error l n
      = match n, l with
        | O, x :: _ => Some x
        | S n, _ :: l' => nth_error l' n
        | _, _ => None
        end.
  Proof. destruct n; reflexivity. Qed.

  Lemma nth_error_nil n : nth_error [] n = None.
  Proof. destruct n; reflexivity. Qed.

  Lemma nth_error_cons x xs n
    : nth_error (x :: xs) n
      = match n with
        | O => Some x
        | S n => nth_error xs n
        end.
  Proof. apply unfold_nth_error. Qed.

  Lemma nth_error_0 l
    : nth_error l O = hd_error l.
  Proof. destruct l; reflexivity. Qed.

  Lemma nth_error_S l n
    : nth_error l (S n) = nth_error (tl l) n.
  Proof. destruct l; rewrite ?nth_error_nil; reflexivity. Qed.

  Lemma nth_error_cons_0 x l : nth_error (cons x l) 0 = Some x.
  Proof. trivial. Qed.

  Lemma nth_error_cons_succ x l n :
    nth_error (cons x l) (S n) = nth_error l n.
  Proof. trivial. Qed.

  (** Results directly relating [nth] and [nth_error] *)

  Lemma nth_error_nth : forall (l : list A) (n : nat) (x d : A),
    nth_error l n = Some x -> nth n l d = x.
  Proof.
    intros l n x d H.
    apply nth_error_split in H. destruct H as [l1 [l2 [H H']]].
    subst. rewrite app_nth2; [|auto].
    rewrite Nat.sub_diag. reflexivity.
  Qed.

  Lemma nth_error_nth' : forall (l : list A) (n : nat) (d : A),
    n < length l -> nth_error l n = Some (nth n l d).
  Proof.
    intros l n d H.
    apply (nth_split _ d) in H. destruct H as [l1 [l2 [H H']]].
    subst. rewrite H. rewrite nth_error_app2; [|auto].
    rewrite app_nth2; [| auto]. repeat (rewrite Nat.sub_diag). reflexivity.
  Qed.

  Lemma nth_error_nth_None (l : list A) (n : nat) (d : A) :
    nth_error l n = None -> nth n l d = d.
  Proof.
    intros H%nth_error_None. apply nth_overflow. assumption.
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
    | a :: l' => last l' d
  end.

  Lemma last_last : forall l a d, last (l ++ [a]) d = a.
  Proof.
    intro l; induction l as [|? l IHl]; intros; [ reflexivity | ].
    simpl; rewrite IHl.
    destruct l; reflexivity.
  Qed.

  (** [removelast l] remove the last element of [l] *)

  Fixpoint removelast (l:list A) : list A :=
    match l with
      | [] =>  []
      | [a] => []
      | a :: l' => a :: removelast l'
    end.

  Lemma app_removelast_last :
    forall l d, l <> [] -> l = removelast l ++ [last l d].
  Proof.
    intro l; induction l as [|? l IHl].
    - destruct 1; auto.
    - intros d _.
      destruct l as [|a0 l]; auto.
      pattern (a0::l) at 1; rewrite IHl with d; auto; discriminate.
  Qed.

  Lemma exists_last :
    forall l, l <> [] -> { l' : (list A) & { a : A | l = l' ++ [a]}}.
  Proof.
    intro l; induction l as [|a l IHl].
    - destruct 1; auto.
    - intros _.
      destruct l.
      + exists [], a; auto.
      + destruct IHl as [l' (a',H)]; try discriminate.
        rewrite H.
        exists (a::l'), a'; auto.
  Qed.

  Lemma removelast_app :
    forall l l', l' <> [] -> removelast (l++l') = l ++ removelast l'.
  Proof.
    intro l; induction l as [|? l IHl]; [easy|].
    intros l' H. cbn. rewrite <- IHl by assumption.
    now destruct l, l'.
  Qed.

  Lemma removelast_last : forall l a, removelast (l ++ [a]) = l.
  Proof.
    intros. rewrite removelast_app.
    - apply app_nil_r.
    - intros Heq; inversion Heq.
  Qed.


  (*****************)
  (** ** Remove    *)
  (*****************)

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Fixpoint remove (x : A) (l : list A) : list A :=
    match l with
      | [] => []
      | y::tl => if (eq_dec x y) then remove x tl else y :: remove x tl
    end.

  Lemma remove_cons : forall x l, remove x (x :: l) = remove x l.
  Proof.
    intros x l; simpl; destruct (eq_dec x x); [ reflexivity | now exfalso ].
  Qed.

  Lemma remove_app : forall x l1 l2,
    remove x (l1 ++ l2) = remove x l1 ++ remove x l2.
  Proof.
    intros x l1; induction l1 as [|a l1 IHl1]; intros l2; simpl.
    - reflexivity.
    - destruct (eq_dec x a).
      + apply IHl1.
      + rewrite <- app_comm_cons; f_equal.
        apply IHl1.
  Qed.

  Theorem remove_In : forall (l : list A) (x : A), ~ In x (remove x l).
  Proof.
    intro l; induction l as [|x l IHl]; auto.
    intro y; simpl; destruct (eq_dec y x) as [yeqx | yneqx].
    - apply IHl.
    - unfold not; intro HF; simpl in HF; destruct HF; auto.
      apply (IHl y); assumption.
  Qed.

  Lemma notin_remove: forall l x, ~ In x l -> remove x l = l.
  Proof.
    intros l x; induction l as [|y l IHl]; simpl; intros Hnin.
    - reflexivity.
    - destruct (eq_dec x y); [subst|f_equal]; tauto.
  Qed.

  Lemma in_remove: forall l x y, In x (remove y l) -> In x l /\ x <> y.
  Proof.
    intro l; induction l as [|z l IHl]; intros x y Hin.
    - inversion Hin.
    - simpl in Hin.
      destruct (eq_dec y z) as [Heq|Hneq]; subst; split.
      + right; now apply IHl with z.
      + intros Heq; revert Hin; subst; apply remove_In.
      + inversion Hin; subst; [left; reflexivity|right].
        now apply IHl with y.
      + destruct Hin as [Hin|Hin]; subst.
        * now intros Heq; apply Hneq.
        * intros Heq; revert Hin; subst; apply remove_In.
  Qed.

  Lemma in_in_remove : forall l x y, x <> y -> In x l -> In x (remove y l).
  Proof.
    intro l; induction l as [|z l IHl]; simpl; intros x y Hneq Hin.
    - apply Hin.
    - destruct (eq_dec y z); subst.
      + destruct Hin.
        * exfalso; now apply Hneq.
        * now apply IHl.
      + simpl; destruct Hin; [now left|right].
        now apply IHl.
  Qed.

  Lemma remove_remove_comm : forall l x y,
    remove x (remove y l) = remove y (remove x l).
  Proof.
    intro l; induction l as [| z l IHl]; simpl; intros x y.
    - reflexivity.
    - destruct (eq_dec y z); simpl; destruct (eq_dec x z); try rewrite IHl; auto.
      + subst; symmetry; apply remove_cons.
      + simpl; destruct (eq_dec y z); tauto.
  Qed.

  Lemma remove_remove_eq : forall l x, remove x (remove x l) = remove x l.
  Proof. intros l x; now rewrite (notin_remove _ _ (remove_In l x)). Qed.

  Lemma remove_length_le : forall l x, length (remove x l) <= length l.
  Proof.
    intro l; induction l as [|y l IHl]; simpl; intros x; trivial.
    destruct (eq_dec x y); simpl.
    - rewrite IHl; constructor; reflexivity.
    - apply (proj1 (Nat.succ_le_mono _ _) (IHl x)).
  Qed.

  Lemma remove_length_lt : forall l x, In x l -> length (remove x l) < length l.
  Proof.
    intro l; induction l as [|y l IHl]; simpl; intros x Hin.
    - contradiction Hin.
    - destruct Hin as [-> | Hin].
      + destruct (eq_dec x x); [|easy].
        apply Nat.lt_succ_r, remove_length_le.
      + specialize (IHl _ Hin); destruct (eq_dec x y); simpl; auto.
        now apply Nat.succ_lt_mono in IHl.
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
    induction l as [|y l IHl]; simpl.
    - split; [destruct 1 | apply Nat.nlt_0_r].
    - destruct eq_dec as [->|Hneq]; rewrite IHl; intuition (apply Nat.lt_0_succ).
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

  Lemma count_occ_app l1 l2 x :
    count_occ (l1 ++ l2) x = count_occ l1 x + count_occ l2 x.
  Proof.
    induction l1 as [ | h l1 IHl1]; cbn; trivial.
    now destruct (eq_dec h x); [ rewrite IHl1 | ].
  Qed.

  Lemma count_occ_elt_eq l1 l2 x y : x = y ->
    count_occ (l1 ++ x :: l2) y = S (count_occ (l1 ++ l2) y).
  Proof.
    intros ->.
    rewrite ? count_occ_app; cbn.
    destruct (eq_dec y y) as [Heq | Hneq];
      [ apply Nat.add_succ_r | now contradiction Hneq ].
  Qed.

  Lemma count_occ_elt_neq l1 l2 x y : x <> y ->
    count_occ (l1 ++ x :: l2) y = count_occ (l1 ++ l2) y.
  Proof.
    intros Hxy.
    rewrite ? count_occ_app; cbn.
    now destruct (eq_dec x y) as [Heq | Hneq]; [ contradiction Hxy | ].
  Qed.

  Lemma count_occ_bound x l : count_occ l x <= length l.
  Proof.
    induction l as [|h l]; cbn; auto.
    destruct (eq_dec h x); [ apply (proj1 (Nat.succ_le_mono _ _)) | ]; intuition.
  Qed.

End Elts.
Notation nth := nth.

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
    intros x y; induction x as [| a l IHl]; cbn.
    - now rewrite app_nil_r.
    - now rewrite IHl, app_assoc.
  Qed.

  Remark rev_unit : forall (l:list A) (a:A), rev (l ++ [a]) = a :: rev l.
  Proof.
    intros l a. apply rev_app_distr.
  Qed.

  Lemma rev_involutive : forall l:list A, rev (rev l) = l.
  Proof.
    intro l; induction l as [| a l IHl].
    - reflexivity.
    - cbn. now rewrite rev_unit, IHl.
  Qed.

  Lemma rev_inj (l1 l2: list A):
    rev l1 = rev l2 -> l1 = l2.
  Proof.
    intro H. apply (f_equal rev) in H.
    rewrite !rev_involutive in H. assumption.
  Qed.

  Lemma rev_eq_app : forall l l1 l2, rev l = l1 ++ l2 -> l = rev l2 ++ rev l1.
  Proof.
    intros l l1 l2 Heq.
    rewrite <- (rev_involutive l), Heq.
    apply rev_app_distr.
  Qed.

  (*********************************************)
  (** Reverse Induction Principle on Lists     *)
  (*********************************************)

  Lemma rev_list_ind : forall P:list A-> Prop,
    P [] ->
    (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
    forall l:list A, P (rev l).
  Proof.
    intros P ? ? l; induction l; auto.
  Qed.

  Theorem rev_ind : forall P:list A -> Prop,
    P [] ->
    (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
  Proof.
    intros P ? ? l. rewrite <- (rev_involutive l).
    apply (rev_list_ind P); cbn; auto.
  Qed.

  (** Compatibility with other operations *)

  Lemma in_rev : forall l x, In x l <-> In x (rev l).
  Proof.
    intro l; induction l as [|? ? IHl]; [easy|].
    intros. cbn. rewrite in_app_iff, IHl. cbn. tauto.
  Qed.

  Lemma length_rev : forall l, length (rev l) = length l.
  Proof.
    intro l; induction l as [|? l IHl];simpl; auto.
    now rewrite length_app, IHl, Nat.add_comm.
  Qed.

  Lemma rev_nth : forall l d n, n < length l ->
    nth n (rev l) d = nth (length l - S n) l d.
  Proof.
    intros l d; induction l as [|a l IHl] using rev_ind; [easy|].
    rewrite rev_app_distr, length_app, Nat.add_comm. cbn. intros [|n].
    - now rewrite Nat.sub_0_r, nth_middle.
    - intros Hn %Nat.succ_lt_mono.
      rewrite (IHl _ Hn), app_nth1; [reflexivity|].
      apply Nat.sub_lt; [assumption|apply Nat.lt_0_succ].
  Qed.

  Lemma nth_error_rev n l : nth_error (rev l) n =
    if Nat.ltb n (length l) then nth_error l (length l - S n) else None.
  Proof.
    case (Nat.ltb_spec n (length l)) as []; cycle 1.
    { apply nth_error_None; rewrite ?length_rev; trivial. }
    destruct l as [|x l']; [inversion H|]; set (x::l') as l in *.
    rewrite 2 nth_error_nth' with (d:=x), rev_nth;
      rewrite ?length_rev; auto using Nat.lt_0_succ, Nat.sub_lt.
  Qed.


  (**  An alternative tail-recursive definition for reverse *)

  Fixpoint rev_append (l l': list A) : list A :=
    match l with
      | [] => l'
      | a :: l => rev_append l (a::l')
    end.

  Definition rev' l : list A := rev_append l [].

  Lemma rev_append_rev : forall l l', rev_append l l' = rev l ++ l'.
  Proof.
    intro l; induction l; simpl; auto; intros.
    rewrite <- app_assoc; firstorder.
  Qed.

  Lemma rev_alt : forall l, rev l = rev_append l [].
  Proof.
    intros; rewrite rev_append_rev.
    rewrite app_nil_r; trivial.
  Qed.

  (*************************)
  (** ** Concatenation     *)
  (*************************)

  Fixpoint concat (l : list (list A)) : list A :=
    match l with
     | [] => []
     | x :: l => x ++ concat l
    end.

  Lemma concat_nil : concat [] = [].
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
  - reflexivity.
  - rewrite IH; apply app_assoc.
  Qed.

  Lemma in_concat : forall l y,
    In y (concat l) <-> exists x, In x l /\ In y x.
  Proof.
    intro l; induction l as [|a l IHl]; simpl; intro y; split; intros H.
    - contradiction.
    - destruct H as (x,(H,_)); contradiction.
    - destruct (in_app_or _ _ _ H) as [H0|H0].
      + exists a; auto.
      + destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
        exists x; auto.
    - apply in_or_app.
      destruct H as (x,(H0,H1)); destruct H0.
      + subst; auto.
      + right; destruct (IHl y) as (_,H2); apply H2.
        exists x; auto.
  Qed.


  (***********************************)
  (** ** Decidable equality on lists *)
  (***********************************)

  Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.

  Lemma list_eq_dec : forall l l':list A, {l = l'} + {l <> l'}.
  Proof. decide equality. Defined.

  Lemma count_occ_rev l x : count_occ eq_dec (rev l) x = count_occ eq_dec l x.
  Proof.
    induction l as [|a l IHl]; trivial.
    cbn; rewrite count_occ_app, IHl; cbn.
    destruct (eq_dec a x); rewrite Nat.add_comm; reflexivity.
  Qed.

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

  Local Notation map := (@map A B f).

  Lemma map_cons (x:A)(l:list A) : map (x::l) = (f x) :: (map l).
  Proof.
    reflexivity.
  Qed.

  Lemma in_map :
    forall (l:list A) (x:A), In x l -> In (f x) (map l).
  Proof.
    intro l; induction l; firstorder (subst; auto).
  Qed.

  Lemma in_map_iff : forall l y, In y (map l) <-> exists x, f x = y /\ In x l.
  Proof.
    intro l; induction l; firstorder (subst; auto).
  Qed.

  Lemma length_map : forall l, length (map l) = length l.
  Proof.
    intro l; induction l; simpl; auto.
  Qed.

  Lemma map_nth : forall l d n,
    nth n (map l) (f d) = f (nth n l d).
  Proof.
    intro l; induction l; simpl map; intros d n; destruct n; firstorder.
  Qed.

  Lemma nth_error_map : forall n l,
    nth_error (map l) n = option_map f (nth_error l n).
  Proof.
    intro n. induction n as [|n IHn]; intro l.
    - now destruct l.
    - destruct l as [|? l]; [reflexivity|exact (IHn l)].
  Qed.

  Lemma map_nth_error : forall n l d,
    nth_error l n = Some d -> nth_error (map l) n = Some (f d).
  Proof.
    intros n l d H. now rewrite nth_error_map, H.
  Qed.

  Lemma tl_map l : tl (map l) = map (tl l).
  Proof. case l; trivial. Qed.

  Lemma map_app : forall l l',
    map (l++l') = (map l)++(map l').
  Proof.
    intro l; induction l as [|a l IHl]; simpl; auto.
    intros; rewrite IHl; auto.
  Qed.

  Lemma map_last : forall l a,
    map (l ++ [a]) = (map l) ++ [f a].
  Proof.
    intro l; induction l as [|a l IHl]; intros; [ reflexivity | ].
    simpl; rewrite IHl; reflexivity.
  Qed.

  Lemma map_rev : forall l, map (rev l) = rev (map l).
  Proof.
    intro l; induction l as [|a l IHl]; simpl; auto.
    rewrite map_app.
    rewrite IHl; auto.
  Qed.

  Lemma map_eq_nil : forall l, map l = [] -> l = [].
  Proof.
    intro l; destruct l; simpl; reflexivity || discriminate.
  Qed.

  Lemma map_eq_cons : forall l l' b,
    map l = b :: l' -> exists a tl, l = a :: tl /\ f a = b /\ map tl = l'.
  Proof.
    intros l l' b Heq.
    destruct l as [|a l]; inversion_clear Heq.
    exists a, l; repeat split.
  Qed.

  Lemma map_eq_app  : forall l l1 l2,
    map l = l1 ++ l2 -> exists l1' l2', l = l1' ++ l2' /\ map l1' = l1 /\ map l2' = l2.
  Proof.
    intro l; induction l as [|a l IHl]; simpl; intros l1 l2 Heq.
    - symmetry in Heq; apply app_eq_nil in Heq; destruct Heq; subst.
      exists nil, nil; repeat split.
    - destruct l1; simpl in Heq; inversion Heq as [[Heq2 Htl]].
      + exists nil, (a :: l); repeat split.
      + destruct (IHl _ _ Htl) as (l1' & l2' & ? & ? & ?); subst.
        exists (a :: l1'), l2'; repeat split.
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
      + rewrite Hrec. reflexivity.
      + contradiction H2. rewrite H1. reflexivity.
      + specialize (Hfinjective H2). contradiction H1.
      + assumption.
  Qed.

End Map.
Notation map := map.

(*****************)
(** ** Flat Map  *)
(*****************)

Section FlatMap.
  Variables (A : Type) (B : Type).
  Variable f : A -> list B.

    (** [flat_map] *)

    Fixpoint flat_map (l:list A) : list B :=
      match l with
        | [] => []
        | x :: l => f x ++ flat_map l
      end.

    Lemma flat_map_concat_map l :
      flat_map l = concat (map f l).
    Proof.
      induction l as [|x l IH]; simpl.
      - reflexivity.
      - rewrite IH; reflexivity.
    Qed.

    Lemma flat_map_app l1 l2 :
      flat_map (l1 ++ l2) = flat_map l1 ++ flat_map l2.
    Proof.
      now rewrite !flat_map_concat_map, map_app, concat_app.
    Qed.

    Lemma in_flat_map l y :
      In y (flat_map l) <-> exists x, In x l /\ In y (f x).
    Proof.
      rewrite flat_map_concat_map, in_concat.
      split.
      - intros [l' [[x [<- ?]] %in_map_iff ?]].
        now exists x.
      - intros [x [? ?]]. exists (f x).
        now split; [apply in_map|].
    Qed.

End FlatMap.

Lemma concat_map : forall A B (f : A -> B) l, map f (concat l) = concat (map (map f) l).
Proof.
  intros A B f l; induction l as [|x l IH]; simpl.
  - reflexivity.
  - rewrite map_app, IH; reflexivity.
Qed.

Lemma remove_concat A (eq_dec : forall x y : A, {x = y}+{x <> y}) : forall l x,
  remove eq_dec x (concat l) = flat_map (remove eq_dec x) l.
Proof.
  intros l x; induction l as [|? ? IHl]; [ reflexivity | simpl ].
  rewrite remove_app, IHl; reflexivity.
Qed.

Lemma map_id : forall (A :Type) (l : list A),
  map (fun x => x) l = l.
Proof.
  intros A l; induction l as [|? ? IHl]; simpl; auto; rewrite IHl; auto.
Qed.

Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
  intros A B C f g l; induction l as [|? ? IHl]; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma map_ext_in :
  forall (A B : Type)(f g:A->B) l, (forall a, In a l -> f a = g a) -> map f l = map g l.
Proof.
  intros A B f g l; induction l as [|? ? IHl]; simpl; auto.
  intros H; rewrite H by intuition; rewrite IHl; auto.
Qed.

Lemma ext_in_map :
  forall (A B : Type)(f g:A->B) l, map f l = map g l -> forall a, In a l -> f a = g a.
Proof. intros A B f g l; induction l; intros [=] ? []; subst; auto. Qed.

Arguments ext_in_map [A B f g l].

Lemma map_ext_in_iff :
   forall (A B : Type)(f g:A->B) l, map f l = map g l <-> forall a, In a l -> f a = g a.
Proof. split; [apply ext_in_map | apply map_ext_in]. Qed.

Arguments map_ext_in_iff {A B f g l}.

Lemma map_ext :
  forall (A B : Type)(f g:A->B), (forall a, f a = g a) -> forall l, map f l = map g l.
Proof.
  intros; apply map_ext_in; auto.
Qed.

Global Instance Proper_map {A B} :
  Proper (pointwise_relation _ eq ==> eq ==> eq) (@map A B).
Proof. repeat intro; subst; auto using map_ext. Qed.

Lemma flat_map_ext : forall (A B : Type)(f g : A -> list B),
  (forall a, f a = g a) -> forall l, flat_map f l = flat_map g l.
Proof.
  intros A B f g Hext l.
  rewrite 2 flat_map_concat_map.
  now rewrite (map_ext _ g).
Qed.

Lemma nth_nth_nth_map A : forall (l : list A) n d ln dn, n < length ln \/ length l <= dn ->
  nth (nth n ln dn) l d = nth n (map (fun x => nth x l d) ln) d.
Proof.
  intros l n d ln dn Hlen.
  rewrite <- (map_nth (fun m => nth m l d)).
  destruct Hlen.
  - apply nth_indep. now rewrite length_map.
  - now rewrite (nth_overflow l).
Qed.


(************************************)
(** Left-to-right iterator on lists *)
(************************************)

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint fold_left (l:list B) (a0:A) : A :=
    match l with
      | [] => a0
      | b :: l => fold_left l (f a0 b)
    end.

  Lemma fold_left_app : forall (l l':list B)(i:A),
    fold_left (l++l') i = fold_left l' (fold_left l i).
  Proof.
    now intro l; induction l; cbn.
  Qed.

End Fold_Left_Recursor.

Lemma fold_left_S_0 :
  forall (A:Type)(l:list A), fold_left (fun x _ => S x) l 0 = length l.
Proof.
  intros A l. induction l as [|? ? IH] using rev_ind; [reflexivity|].
  now rewrite fold_left_app, length_app, IH, Nat.add_comm.
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
      | [] => a0
      | b :: l => f b (fold_right l)
    end.

End Fold_Right_Recursor.

  Lemma fold_right_app : forall (A B:Type)(f:A->B->B) l l' i,
    fold_right f i (l++l') = fold_right f (fold_right f i l') l.
  Proof.
    intros A B f l; induction l.
    - simpl; auto.
    - simpl; intros.
      f_equal; auto.
  Qed.

  Lemma fold_left_rev_right : forall (A B:Type)(f:A->B->B) l i,
    fold_right f i (rev l) = fold_left (fun x y => f y x) l i.
  Proof.
    intros A B f l; induction l.
    - simpl; auto.
    - intros.
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
    induction l as [ | a1 l IHl]; [ simpl; reflexivity | ].
    simpl. rewrite <- IHl. clear IHl. revert a1.
    induction l as [|? ? IHl]; [ auto | ].
    simpl. intro. rewrite <- assoc. rewrite IHl. rewrite IHl. auto.
  Qed.

  (** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
      indexed by elts of [x], sorted in lexicographic order. *)

  Fixpoint list_power (A B:Type)(l:list A) (l':list B) :
    list (list (A * B)) :=
    match l with
      | [] => [[]]
      | x :: l =>
        flat_map (fun f:list (A * B) => map (fun y:B => (x, y) :: f) l')
        (list_power l l')
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
        | [] => false
        | a :: l => f a || existsb l
      end.

    Lemma existsb_exists :
      forall l, existsb l = true <-> exists x, In x l /\ f x = true.
    Proof.
      intro l; induction l as [ | a m IH ]; split; simpl.
      - easy.
      - intros [x [[]]].
      - destruct (f a) eqn:Ha.
        + intros _. exists a. tauto.
        + intros [x [? ?]] %IH. exists x. tauto.
      - intros [ x [ [ Hax | Hxm ] Hfx ] ].
        + now rewrite Hax, Hfx.
        + destruct IH as [ _ -> ]; eauto with bool.
    Qed.

    Lemma existsb_nth : forall l n d, n < length l ->
      existsb l = false -> f (nth n l d) = false.
    Proof.
      intro l; induction l as [|a ? IHl]; [easy|].
      cbn. intros [|n]; [now destruct (f a)|].
      intros d ? %Nat.succ_lt_mono.
      now destruct (f a); [|apply IHl].
    Qed.

    Lemma existsb_app : forall l1 l2,
      existsb (l1++l2) = existsb l1 || existsb l2.
    Proof.
      intro l1; induction l1 as [|a ? ?]; intros l2; simpl.
      - auto.
      - case (f a); simpl; solve[auto].
    Qed.

  (** find whether a boolean function is satisfied by
    all the elements of a list. *)

    Fixpoint forallb (l:list A) : bool :=
      match l with
      | [] => true
      | a::l => f a && forallb l
      end.

    Lemma forallb_forall :
      forall l, forallb l = true <-> (forall x, In x l -> f x = true).
    Proof.
      intro l; induction l as [|a l IHl]; simpl; [ tauto | split; intro H ].
      + destruct (andb_prop _ _ H); intros a' [?|?].
        - congruence.
        - apply IHl; assumption.
      + apply andb_true_intro; split.
        - apply H; left; reflexivity.
        - apply IHl; intros; apply H; right; assumption.
    Qed.

    Lemma forallb_app :
      forall l1 l2, forallb (l1++l2) = forallb l1 && forallb l2.
    Proof.
      intro l1; induction l1 as [|a ? ?]; simpl.
      - auto.
      - case (f a); simpl; solve[auto].
    Qed.

  (** [filter] *)

    Fixpoint filter (l:list A) : list A :=
      match l with
      | [] => []
      | x :: l => if f x then x::(filter l) else filter l
      end.

    Lemma filter_In : forall x l, In x (filter l) <-> In x l /\ f x = true.
    Proof.
      intros x l; induction l as [|a ? ?]; simpl.
      - tauto.
      - intros.
        case_eq (f a); intros; simpl; intuition congruence.
    Qed.

    Lemma filter_app (l l':list A) :
      filter (l ++ l') = filter l ++ filter l'.
    Proof.
      induction l as [|x l IH]; simpl; trivial.
      destruct (f x); simpl; now rewrite IH.
    Qed.

    Lemma concat_filter_map : forall (l : list (list A)),
      concat (map filter l) = filter (concat l).
    Proof.
      intro l; induction l as [| v l IHl]; [auto|].
      simpl. rewrite IHl. rewrite filter_app. reflexivity.
    Qed.

    Lemma forallb_filter l: forallb (filter l) = true.
    Proof.
      induction l as [|x l IH]; [reflexivity|].
      cbn. remember (f x) as y. destruct y.
      - apply andb_true_intro. auto.
      - exact IH.
    Qed.

    Lemma forallb_filter_id l: forallb l = true -> filter l = l.
    Proof.
      induction l as [|x l IH]; [easy|].
      cbn. intro H. destruct (f x).
      - f_equal. apply IH, H.
      - discriminate H.
    Qed.

  (** [find] *)

    Fixpoint find (l:list A) : option A :=
      match l with
      | [] => None
      | x :: tl => if f x then Some x else find tl
      end.

    Lemma find_some l x : find l = Some x -> In x l /\ f x = true.
    Proof.
     induction l as [|a l IH]; simpl; [easy| ].
     case_eq (f a); intros Ha Eq.
     * injection Eq as [= ->]; auto.
     * destruct (IH Eq); auto.
    Qed.

    Lemma find_none l : find l = None -> forall x, In x l -> f x = false.
    Proof.
     induction l as [|a l IH]; simpl; [easy|].
     case_eq (f a); intros Ha Eq x IN; [easy|].
     destruct IN as [<-|IN]; auto.
    Qed.

    Lemma filter_rev (l : list A) : filter (rev l) = rev (filter l).
    Proof.
      induction l; cbn [rev]; trivial.
      rewrite filter_app, IHl; cbn [filter].
      case f; cbn [app]; auto using app_nil_r.
    Qed.

  (** [partition] *)

    Fixpoint partition (l:list A) : list A * list A :=
      match l with
      | [] => ([], [])
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
    - injection Eq as [= <- <-]. tauto.
    - destruct (partition l') as (left, right).
      specialize (Hrec left right eq_refl x).
      destruct (f a); injection Eq as [= <- <-]; simpl; tauto.
  Qed.

  End Bool.


  (*******************************)
  (** ** Further filtering facts *)
  (*******************************)

  Section Filtering.

    Lemma filter_map_swap A B f g l :
      filter f (@map A B g l) = @map A B g (filter (fun a => f (g a)) l).
    Proof. induction l; cbn [map filter]; auto. rewrite IHl; case f; auto. Qed.

    Variables (A : Type).

    Lemma filter_true l : filter (fun _ : A => true) l = l.
    Proof. induction l; cbn [filter]; congruence. Qed.

    Lemma filter_false l : filter (fun _ : A => false) l = nil.
    Proof. induction l; cbn [filter]; congruence. Qed.

    Lemma filter_ext_in : forall (f g : A -> bool) (l : list A),
      (forall a, In a l -> f a = g a) -> filter f l = filter g l.
    Proof.
      intros f g l. induction l as [| a l IHl]; [easy|cbn].
      intros H. rewrite (H a) by (now left).
      destruct (g a); [f_equal|]; apply IHl; intros; apply H; now right.
    Qed.

    Lemma ext_in_filter : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l -> (forall a, In a l -> f a = g a).
    Proof.
      intros f g l. induction l as [| a l IHl]; [easy|cbn].
      intros H. assert (Ha : f a = g a).
      - pose proof (Hf := proj1 (filter_In f a l)).
        pose proof (Hg := proj1 (filter_In g a l)).
        destruct (f a), (g a); [reflexivity| | |reflexivity].
        + symmetry. apply Hg. rewrite <- H. now left.
        + apply Hf. rewrite H. now left.
      - intros b [<-|Hbl]; [assumption|].
        apply IHl; [|assumption].
        destruct (f a), (g a); congruence.
    Qed.

    Lemma filter_ext_in_iff : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l <-> (forall a, In a l -> f a = g a).
    Proof.
      split; [apply ext_in_filter | apply filter_ext_in].
    Qed.

    Lemma filter_map : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l <-> map f l = map g l.
    Proof.
      intros f g l. now rewrite filter_ext_in_iff, map_ext_in_iff.
    Qed.

    Lemma filter_ext : forall (f g : A -> bool),
      (forall a, f a = g a) -> forall l, filter f l = filter g l.
    Proof.
      intros f g H l. rewrite filter_map. apply map_ext. assumption.
    Qed.

    Lemma partition_as_filter f (l : list A) : partition f l = (filter f l, filter (fun x => negb (f x)) l).
    Proof.
      induction l as [|x l IH].
      - reflexivity.
      - cbn. rewrite IH. destruct (f x); reflexivity.
    Qed.

    Corollary filter_length f (l : list A) : length (filter f l) + length (filter (fun x => negb (f x)) l) = length l.
    Proof. symmetry. apply (partition_length f), partition_as_filter. Qed.

    Corollary filter_length_le f (l : list A): length (filter f l) <= length l.
    Proof. rewrite <- (filter_length f l). apply Nat.le_add_r. Qed.

    Lemma filter_length_forallb f (l : list A): length (filter f l) = length l -> forallb f l = true.
    Proof.
      intro H. induction l as [|x l IH]; [reflexivity |].
      cbn in *. destruct (f x).
      - apply IH. now injection H.
      - exfalso. assert (length l < length (filter f l)) as E.
        + symmetry in H. apply Nat.eq_le_incl in H. exact H.
        + eapply Nat.le_ngt; [apply filter_length_le | exact E].
    Qed.

    (** Remove by filtering *)

    Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

    Definition remove' (x : A) : list A -> list A :=
      filter (fun y => if eq_dec x y then false else true).

    Lemma remove_alt (x : A) (l : list A) : remove' x l = remove eq_dec x l.
    Proof.
      induction l; [reflexivity|].
      simpl. now destruct eq_dec; [|f_equal].
    Qed.

    (** Counting occurrences by filtering *)

    Definition count_occ' (l : list A) (x : A) : nat :=
      length (filter (fun y => if eq_dec y x then true else false) l).

    Lemma count_occ_alt (l : list A) (x : A) :
      count_occ' l x = count_occ eq_dec l x.
    Proof.
      unfold count_occ'. induction l; [reflexivity|].
      simpl. now destruct eq_dec; simpl; [f_equal|].
    Qed.

  End Filtering.


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
      intro l. induction l as [|[? ?] l IHl]; [easy|].
      intros [? ?]. cbn.
      now intros [[=]|? %IHl]; destruct (split l); [left|right].
    Qed.

    Lemma in_split_r : forall (l:list (A*B))(p:A*B),
      In p l -> In (snd p) (snd (split l)).
    Proof.
      intro l. induction l as [|[? ?] l IHl]; [easy|].
      intros [? ?]. cbn.
      now intros [[=]|? %IHl]; destruct (split l); [left|right].
    Qed.

    Lemma split_nth : forall (l:list (A*B))(n:nat)(d:A*B),
      nth n l d = (nth n (fst (split l)) (fst d), nth n (snd (split l)) (snd d)).
    Proof.
      intro l; induction l as [|a l IHl].
      - intros n d; destruct n; destruct d; simpl; auto.
      - intros n d; destruct n; destruct d; simpl; auto.
        + destruct a; destruct (split l); simpl; auto.
        + destruct a; destruct (split l); simpl in *; auto.
    Qed.

    Lemma length_fst_split : forall (l:list (A*B)),
      length (fst (split l)) = length l.
    Proof.
      intro l; induction l as [|a l IHl]; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

    Lemma length_snd_split : forall (l:list (A*B)),
      length (snd (split l)) = length l.
    Proof.
      intro l; induction l as [|a l IHl]; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

  (** [combine] is the opposite of [split].
      Lists given to [combine] are meant to be of same length.
      If not, [combine] stops on the shorter list *)

    Fixpoint combine (l : list A) (l' : list B) : list (A*B) :=
      match l,l' with
      | x::tl, y::tl' => (x,y)::(combine tl tl')
      | _, _ => []
      end.

    Lemma split_combine : forall (l: list (A*B)),
      forall l1 l2, split l = (l1, l2) -> combine l1 l2 = l.
    Proof.
      intro l; induction l as [|a l IHl].
      1: simpl; auto.
      all: intuition; inversion H; auto.
      destruct (split l); simpl in *.
      inversion H1; subst; simpl.
      f_equal; auto.
    Qed.

    Lemma combine_split : forall (l:list A)(l':list B), length l = length l' ->
      split (combine l l') = (l,l').
    Proof.
      intro l; induction l as [|a l IHl]; intro l'; destruct l';
       simpl; trivial; try discriminate.
      now intros [= ->%IHl].
    Qed.

    Lemma in_combine_l : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In x l.
    Proof.
      intro l; induction l as [|a l IHl].
      - simpl; auto.
      - intro l'; destruct l' as [|a0 l']; simpl; auto; intros x y H.
        + contradiction.
        + destruct H as [H|H].
          * injection H; auto.
          * right; apply IHl with l' y; auto.
    Qed.

    Lemma in_combine_r : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In y l'.
    Proof.
      intro l; induction l as [|? ? IHl].
      - simpl; intros; contradiction.
      - intro l'; destruct l'; simpl; auto; intros x y H.
        destruct H as [H|H].
        + injection H; auto.
        + right; apply IHl with x; auto.
    Qed.

    Lemma length_combine : forall (l:list A)(l':list B),
      length (combine l l') = min (length l) (length l').
    Proof.
      intro l; induction l.
      - simpl; auto.
      - intro l'; destruct l'; simpl; auto.
    Qed.

    Lemma combine_nth : forall (l:list A)(l':list B)(n:nat)(x:A)(y:B),
      length l = length l' ->
      nth n (combine l l') (x,y) = (nth n l x, nth n l' y).
    Proof.
      intro l; induction l; intro l'; destruct l'; intros n x y; try discriminate.
      - destruct n; simpl; auto.
      - destruct n; simpl in *; auto.
    Qed.

  (** [list_prod] has the same signature as [combine], but unlike
     [combine], it adds every possible pairs, not only those at the
     same position. *)

    Fixpoint list_prod (l:list A) (l':list B) :
      list (A * B) :=
      match l with
      | [] => []
      | x :: t => (map (fun y:B => (x, y)) l')++(list_prod t l')
      end.

    Lemma in_prod_aux :
      forall (x:A) (y:B) (l:list B),
        In y l -> In (x, y) (map (fun y0:B => (x, y0)) l).
    Proof.
      intros x y l; induction l;
        [ simpl; auto
          | simpl; destruct 1 as [H1| ];
            [ left; rewrite H1; trivial | right; auto ] ].
    Qed.

    Lemma in_prod :
      forall (l:list A) (l':list B) (x:A) (y:B),
        In x l -> In y l' -> In (x, y) (list_prod l l').
    Proof.
      intro l; induction l;
      [ simpl; tauto
        | simpl; intros l' x y H H0; apply in_or_app; destruct H as [H|H];
          [ left; rewrite H; apply in_prod_aux; assumption | right; auto ] ].
    Qed.

    Lemma in_prod_iff :
      forall (l:list A)(l':list B)(x:A)(y:B),
        In (x,y) (list_prod l l') <-> In x l /\ In y l'.
    Proof.
      intros l l' x y; split; [ | intros H; now apply in_prod ].
      induction l as [|a l IHl]; cbn; [easy|].
      intros [[? [[= -> ->] ?]] %in_map_iff|] %in_app_or; tauto.
    Qed.

    Lemma length_prod : forall (l:list A)(l':list B),
      length (list_prod l l') = (length l) * (length l').
    Proof.
      intro l; induction l as [|? ? IHl]; simpl; [easy|].
      intros. now rewrite length_app, length_map, IHl.
    Qed.

    Lemma list_prod_as_flat_map : forall l l',
      list_prod l l' = flat_map (fun a => map (pair a) l') l.
    Proof. induction l; intros; cbn; rewrite ?IHl; trivial. Qed.
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
    now apply Nat.le_refl.
  Qed.

  Lemma lel_trans : lel l m -> lel m n -> lel l n.
  Proof.
    unfold lel; intros.
    now_show (length l <= length n).
    now apply Nat.le_trans with (length m).
  Qed.

  Lemma lel_cons_cons : lel l m -> lel (a :: l) (b :: m).
  Proof.
    now intros ? %Nat.succ_le_mono.
  Qed.

  Lemma lel_cons : lel l m -> lel l (b :: m).
  Proof.
    intros. now apply Nat.le_le_succ_r.
  Qed.

  Lemma lel_tail : lel (a :: l) (b :: m) -> lel l m.
  Proof.
    intros. now apply Nat.succ_le_mono.
  Qed.

  Lemma lel_nil : forall l':list A, lel l' [] -> [] = l'.
  Proof.
    intro l'; elim l'; [now intros|].
    now intros a' y H H0 %Nat.nle_succ_0.
  Qed.
End length_order.

#[global]
Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons:
  datatypes.


(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.

  Variable A : Type.

  Definition incl (l m:list A) := forall a:A, In a l -> In a m.
  #[local]
  Hint Unfold incl : core.

  Lemma incl_nil_l : forall l, incl [] l.
  Proof.
    intros l a Hin; inversion Hin.
  Qed.

  Lemma incl_l_nil : forall l, incl l [] -> l = [].
  Proof.
    intro l; destruct l as [|a l]; intros Hincl.
    - reflexivity.
    - exfalso; apply Hincl with a; simpl; auto.
  Qed.

  Lemma incl_refl : forall l:list A, incl l l.
  Proof.
    auto.
  Qed.
  #[local]
  Hint Resolve incl_refl : core.

  Lemma incl_tl : forall (a:A) (l m:list A), incl l m -> incl l (a :: m).
  Proof.
    auto with datatypes.
  Qed.
  #[local]
  Hint Immediate incl_tl : core.

  Lemma incl_tran : forall l m n:list A, incl l m -> incl m n -> incl l n.
  Proof.
    auto.
  Qed.

  Lemma incl_appl : forall l m n:list A, incl l n -> incl l (n ++ m).
  Proof.
    auto with datatypes.
  Qed.
  #[local]
  Hint Immediate incl_appl : core.

  Lemma incl_appr : forall l m n:list A, incl l n -> incl l (m ++ n).
  Proof.
    auto with datatypes.
  Qed.
  #[local]
  Hint Immediate incl_appr : core.

  Lemma incl_cons :
    forall (a:A) (l m:list A), In a m -> incl l m -> incl (a :: l) m.
  Proof.
    now intros a l m ? H b [<-|]; [|apply H].
  Qed.
  #[local]
  Hint Resolve incl_cons : core.

  Lemma incl_cons_inv : forall (a:A) (l m:list A),
    incl (a :: l) m -> In a m /\ incl l m.
  Proof.
    intros a l m Hi.
    split; [ | intros ? ? ]; apply Hi; simpl; auto.
  Qed.

  Lemma incl_app : forall l m n:list A, incl l n -> incl m n -> incl (l ++ m) n.
  Proof.
    unfold incl; simpl; intros l m n H H0 a H1.
    now_show (In a n).
    elim (in_app_or _ _ _ H1); auto.
  Qed.
  #[local]
  Hint Resolve incl_app : core.

  Lemma incl_app_app : forall l1 l2 m1 m2:list A,
    incl l1 m1 -> incl l2 m2 -> incl (l1 ++ l2) (m1 ++ m2).
  Proof.
    intros.
    apply incl_app; [ apply incl_appl | apply incl_appr]; assumption.
  Qed.

  Lemma incl_app_inv : forall l1 l2 m : list A,
    incl (l1 ++ l2) m -> incl l1 m /\ incl l2 m.
  Proof.
    intro l1; induction l1 as [|a l1 IHl1]; intros l2 m Hin; split; auto.
    - apply incl_nil_l.
    - intros b Hb; inversion_clear Hb; subst; apply Hin.
      + now constructor.
      + simpl; apply in_cons.
        apply incl_appl with l1; [ apply incl_refl | assumption ].
    - apply IHl1.
      now apply incl_cons_inv in Hin.
  Qed.

  Lemma incl_filter f l : incl (filter f l) l.
  Proof. intros x Hin; now apply filter_In in Hin. Qed.

  Lemma remove_incl (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall l1 l2 x,
    incl l1 l2 -> incl (remove eq_dec x l1) (remove eq_dec x l2).
  Proof.
    intros l1 l2 x Hincl y Hin.
    apply in_remove in Hin; destruct Hin as [Hin Hneq].
    apply in_in_remove; intuition.
  Qed.

End SetIncl.

Lemma incl_map A B (f : A -> B) l1 l2 : incl l1 l2 -> incl (map f l1) (map f l2).
Proof.
  intros Hincl x Hinx.
  destruct (proj1 (in_map_iff _ _ _) Hinx) as [y [<- Hiny]].
  now apply in_map, Hincl.
Qed.

#[global]
Hint Resolve incl_refl incl_tl incl_tran incl_appl incl_appr incl_cons
  incl_app incl_map: datatypes.


(**************************************)
(** * Cutting a list at some position *)
(**************************************)

Section Cutting.

  Variable A : Type.

  Local Notation firstn := (@firstn A).
  Local Notation skipn := (@skipn A).

  Lemma firstn_nil n: firstn n [] = [].
  Proof. induction n; now simpl. Qed.

  Lemma firstn_cons n a l: firstn (S n) (a::l) = a :: (firstn n l).
  Proof. now simpl. Qed.

  Lemma nth_error_firstn n l i
    : nth_error (firstn n l) i = if Nat.ltb i n then nth_error l i else None.
  Proof.
    revert l i; induction n, l, i; cbn [firstn nth_error]; trivial.
    case Nat.ltb; trivial.
  Qed.

  Lemma nth_firstn (n : nat) (l : list A) (i : nat) (d : A) :
    nth i (firstn n l) d = if i <? n then nth i l d else d.
  Proof.
    revert l i; induction n, l, i; cbn [firstn nth]; trivial.
    case Nat.ltb; trivial.
  Qed.

  Lemma firstn_all l: firstn (length l) l = l.
  Proof. induction l as [| ? ? H]; simpl; [reflexivity | now rewrite H]. Qed.

  Lemma firstn_all2 n: forall (l:list A), (length l) <= n -> firstn n l = l.
  Proof. induction n as [|k iHk].
    - intro l. inversion 1 as [H1|?].
      rewrite (length_zero_iff_nil l) in H1. subst. now simpl.
    - intro l; destruct l as [|x xs]; simpl.
      * now reflexivity.
      * simpl. intro H. f_equal. apply iHk. now apply Nat.succ_le_mono.
  Qed.

  Lemma firstn_0 l: firstn 0 l = [].
  Proof. now simpl. Qed.

  Lemma firstn_le_length n: forall l:list A, length (firstn n l) <= n.
  Proof.
    induction n as [|k iHk]; simpl; [auto | intro l; destruct l as [|x xs]; simpl].
    - now apply Nat.le_0_l.
    - now rewrite <- Nat.succ_le_mono.
  Qed.

  Lemma firstn_length_le: forall l:list A, forall n:nat,
    n <= length l -> length (firstn n l) = n.
  Proof. intro l; induction l as [|x xs Hrec].
    - simpl. intros n H. apply Nat.le_0_r in H. now subst.
    - intro n; destruct n as [|n].
      * now simpl.
      * simpl. intro H. f_equal. apply Hrec. now apply Nat.succ_le_mono.
  Qed.

  Lemma firstn_app n:
    forall l1 l2,
    firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2).
  Proof. induction n as [|k iHk]; intros l1 l2.
    - now simpl.
    - destruct l1 as [|x xs].
      * reflexivity.
      * rewrite <- app_comm_cons. simpl. f_equal. apply iHk.
  Qed.

  Lemma firstn_app_2 n:
    forall l1 l2,
    firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2.
  Proof. induction n as [| k iHk];intros l1 l2.
    - unfold firstn at 2. rewrite Nat.add_0_r, app_nil_r.
      rewrite firstn_app. rewrite Nat.sub_diag.
      unfold firstn at 2. rewrite app_nil_r. apply firstn_all.
    - destruct l2 as [|x xs].
      * simpl. rewrite app_nil_r. apply firstn_all2. now apply Nat.le_add_r.
      * rewrite firstn_app. assert (H0 : (length l1 + S k - length l1) = S k).
        1:now rewrite Nat.add_comm, Nat.add_sub.
        rewrite H0, firstn_all2; [reflexivity | now apply Nat.le_add_r].
  Qed.

  Lemma firstn_firstn:
    forall l:list A,
    forall i j : nat,
    firstn i (firstn j l) = firstn (min i j) l.
  Proof. intro l; induction l as [|x xs Hl].
    - intros. simpl. now rewrite ?firstn_nil.
    - intros [|i]; [easy|].
      intros [|j]; [easy|].
      cbn. f_equal. apply Hl.
  Qed.

  Lemma nth_error_skipn n l i : nth_error (skipn n l) i = nth_error l (n + i).
  Proof.
    revert l; induction n, l; cbn [nth_error skipn];
      rewrite ?nth_error_nil; trivial.
  Qed.

  Lemma nth_skipn n l i d : nth i (skipn n l) d = nth (n + i) l d.
  Proof.
    revert l; induction n, l; cbn [nth skipn];
      rewrite ?nth_error_nil; destruct i; trivial.
  Qed.

  Lemma hd_error_skipn n l : hd_error (skipn n l) = nth_error l n.
  Proof. rewrite <-nth_error_0, nth_error_skipn, Nat.add_0_r; trivial. Qed.

  Lemma firstn_skipn_comm : forall m n l,
  firstn m (skipn n l) = skipn n (firstn (n + m) l).
  Proof. now intros m n; induction n; intros []; simpl; destruct m. Qed.

  Lemma skipn_firstn_comm : forall m n l,
  skipn m (firstn n l) = firstn (n - m) (skipn m l).
  Proof. now intro m; induction m; intros [] []; simpl; rewrite ?firstn_nil. Qed.

  Lemma skipn_0 : forall l, skipn 0 l = l.
  Proof. reflexivity. Qed.

  Lemma skipn_nil : forall n, skipn n ([] : list A) = [].
  Proof. now intros []. Qed.

  Lemma skipn_cons n a l: skipn (S n) (a::l) = skipn n l.
  Proof. reflexivity. Qed.

  Lemma skipn_all : forall l, skipn (length l) l = [].
  Proof. now intro l; induction l. Qed.

  Lemma skipn_all2 n: forall l, length l <= n -> skipn n l = [].
  Proof.
    intros l L%Nat.sub_0_le; rewrite <-(firstn_all l) at 1.
    now rewrite skipn_firstn_comm, L.
  Qed.

  Lemma skipn_all_iff n l : length l <= n <-> skipn n l = [].
  Proof.
    split; [apply skipn_all2|].
    revert l; induction n as [|n IH]; intros l.
    - destruct l; simpl; [reflexivity|discriminate].
    - destruct l; simpl.
      + intros _. apply Nat.le_0_l.
      + intros H%IH. apply le_n_S. exact H.
  Qed.

  Lemma skipn_skipn : forall x y l, skipn x (skipn y l) = skipn (x + y) l.
  Proof.
    intros x y. rewrite Nat.add_comm. induction y as [|y IHy].
    - reflexivity.
    - intros [|].
      + now rewrite skipn_nil.
      + now rewrite skipn_cons, IHy.
  Qed.

  Lemma firstn_skipn : forall n l, firstn n l ++ skipn n l = l.
  Proof.
    intro n; induction n.
    - simpl; auto.
    - intro l; destruct l; simpl; auto.
      f_equal; auto.
  Qed.

  Lemma firstn_skipn_middle n l x :
    nth_error l n = Some x ->
    firstn n l ++ x :: skipn (S n) l = l.
  Proof.
    revert l x; induction n as [|n IH]; intros [|y l] x.
    - discriminate.
    - injection 1. intros ->. reflexivity.
    - discriminate.
    - simpl. intros H. f_equal. apply IH. exact H.
  Qed.

  Lemma length_firstn : forall n l, length (firstn n l) = min n (length l).
  Proof.
    intro n; induction n; intro l; destruct l; simpl; auto.
  Qed.

  Lemma length_skipn n :
    forall l, length (skipn n l) = length l - n.
  Proof.
    induction n.
    - intros l; simpl; rewrite Nat.sub_0_r; reflexivity.
    - intro l; destruct l; simpl; auto.
  Qed.

  Lemma skipn_app n : forall l1 l2,
    skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
  Proof. induction n; auto; intros [|]; simpl; auto. Qed.

  Lemma firstn_skipn_rev: forall x l,
      firstn x l = rev (skipn (length l - x) (rev l)).
  Proof.
    intros x l; rewrite <-(firstn_skipn x l) at 3.
    rewrite rev_app_distr, skipn_app, rev_app_distr, length_rev,
            length_skipn, Nat.sub_diag; simpl; rewrite rev_involutive.
    rewrite <-app_nil_r at 1; f_equal; symmetry; apply length_zero_iff_nil.
    repeat rewrite length_rev, length_skipn; apply Nat.sub_diag.
  Qed.

  Lemma firstn_rev: forall x l,
    firstn x (rev l) = rev (skipn (length l - x) l).
  Proof.
    now intros x l; rewrite firstn_skipn_rev, rev_involutive, length_rev.
  Qed.

  Lemma skipn_rev: forall x l,
      skipn x (rev l) = rev (firstn (length l - x) l).
  Proof.
    intros x l; rewrite firstn_skipn_rev, rev_involutive, <-length_rev.
    destruct (Nat.le_ge_cases (length (rev l)) x) as [L | L].
    - rewrite skipn_all2; [apply Nat.sub_0_le in L | trivial].
      now rewrite L, Nat.sub_0_r, skipn_all.
    - f_equal. now apply Nat.eq_sym, Nat.add_sub_eq_l, Nat.sub_add.
  Qed.

  Lemma removelast_firstn : forall n l, n < length l ->
    removelast (firstn (S n) l) = firstn n l.
  Proof.
    intro n; induction n as [|n IHn]; intros [|? l]; [easy ..|].
    cbn [length firstn]. destruct l.
    - now intros ? %Nat.succ_lt_mono.
    - now intros <- %Nat.succ_lt_mono %IHn.
  Qed.

  Lemma removelast_firstn_len : forall l,
    removelast l = firstn (pred (length l)) l.
  Proof.
    intro l; induction l as [|a l IHl]; [ reflexivity | simpl ].
    destruct l; [ | rewrite IHl ]; reflexivity.
  Qed.

  Lemma firstn_removelast : forall n l, n < length l ->
    firstn n (removelast l) = firstn n l.
  Proof.
    intro n; induction n as [|n IHn]; intros [|? l]; [easy ..|].
    cbn [length firstn]. destruct l.
    - now intros ? %Nat.succ_lt_mono.
    - now intros <- %Nat.succ_lt_mono %IHn.
  Qed.

End Cutting.
Notation firstn := firstn.
Notation skipn := skipn.

Section CuttingMap.
  Variables A B : Type.
  Variable f : A -> B.

  Lemma firstn_map : forall n l,
      firstn n (map f l) = map f (firstn n l).
  Proof.
    intro n; induction n; intros []; simpl; f_equal; trivial.
  Qed.

  Lemma skipn_map : forall n l,
      skipn n (map f l) = map f (skipn n l).
  Proof.
    intro n; induction n; intros []; simpl; trivial.
  Qed.
End CuttingMap.

(**************************************************************)
(** ** Combining pairs of lists of possibly-different lengths *)
(**************************************************************)

Section Combining.
    Variables (A B : Type).

    Lemma combine_nil : forall (l : list A),
      combine l (@nil B) = @nil (A*B).
    Proof.
      intros l.
      apply length_zero_iff_nil.
      rewrite length_combine. simpl. rewrite Nat.min_0_r.
      reflexivity.
    Qed.

    Lemma combine_firstn_l : forall (l : list A) (l' : list B),
      combine l l' = combine l (firstn (length l) l').
    Proof.
      intro l; induction l as [| x l IHl]; intros l'; [reflexivity|].
      destruct l' as [| x' l']; [reflexivity|].
      simpl. specialize IHl with l'. rewrite <- IHl.
      reflexivity.
    Qed.

    Lemma combine_firstn_r : forall (l : list A) (l' : list B),
      combine l l' = combine (firstn (length l') l) l'.
    Proof.
      intros l l'. generalize dependent l.
      induction l' as [| x' l' IHl']; intros l.
      - simpl. apply combine_nil.
      - destruct l as [| x l]; [reflexivity|].
        simpl. specialize IHl' with l. rewrite <- IHl'.
        reflexivity.
    Qed.

    Lemma combine_firstn : forall (l : list A) (l' : list B) (n : nat),
      firstn n (combine l l') = combine (firstn n l) (firstn n l').
    Proof.
      intro l; induction l as [| x l IHl]; intros l' n.
      - simpl. repeat (rewrite firstn_nil). reflexivity.
      - destruct l' as [| x' l'].
        + simpl. repeat (rewrite firstn_nil). rewrite combine_nil. reflexivity.
        + simpl. destruct n as [| n]; [reflexivity|].
          repeat (rewrite firstn_cons). simpl.
          rewrite IHl. reflexivity.
    Qed.

End Combining.

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
   induction 1 as [l|x ? ? ? IHAdd].
   - exists nil; exists l; split; trivial.
   - destruct IHAdd as (l1 & l2 & Hl & Hl').
     exists (x::l1); exists l2; split; simpl; f_equal; trivial.
  Qed.

  Lemma Add_in a l l' : Add a l l' ->
   forall x, In x l' <-> In x (a::l).
  Proof.
   induction 1 as [|? ? ? ? IHAdd]; intros; simpl in *; rewrite ?IHAdd; tauto.
  Qed.

  Lemma Add_length a l l' : Add a l l' -> length l' = S (length l).
  Proof.
   induction 1; simpl; now auto.
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
    | NoDup_nil : NoDup []
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

  Lemma NoDup_app (l1 l2 : list A):
    NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) ->
    NoDup (l1 ++ l2).
  Proof.
    intros H1 H2 H. induction l1 as [|a l1 IHl1]; [assumption|].
    apply NoDup_cons_iff in H1 as [].
    cbn. constructor.
    - intros H3%in_app_or. destruct H3.
      + contradiction.
      + apply (H a); [apply in_eq|assumption].
    - apply IHl1; [assumption|].
      intros. apply H, in_cons. assumption.
  Qed.

  Lemma NoDup_app_remove_l l l' : NoDup (l++l') -> NoDup l'.
  Proof.
  induction l as [|a l IHl]; intro H.
  - exact H.
  - apply IHl, (NoDup_remove_1 nil _ _ H).
  Qed.

  Lemma NoDup_app_remove_r l l' : NoDup (l++l') -> NoDup l.
  Proof.
  induction l' as [|a l' IHl']; intro H.
  - now rewrite app_nil_r in H.
  - apply IHl', (NoDup_remove_1 _ _ _ H).
  Qed.

  Lemma NoDup_rev l : NoDup l -> NoDup (rev l).
  Proof.
    induction l as [|a l IHl]; simpl; intros Hnd; [ constructor | ].
    inversion_clear Hnd as [ | ? ? Hnin Hndl ].
    assert (Add a (rev l) (rev l ++ a :: nil)) as Hadd
      by (rewrite <- (app_nil_r (rev l)) at 1; apply Add_app).
    apply NoDup_Add in Hadd; apply Hadd; intuition.
    now apply Hnin, in_rev.
  Qed.

  Lemma NoDup_filter f l : NoDup l -> NoDup (filter f l).
  Proof.
    induction l as [|a l IHl]; simpl; intros Hnd; auto.
    apply NoDup_cons_iff in Hnd.
    destruct (f a); [ | intuition ].
    apply NoDup_cons_iff; split; [intro H|]; intuition.
    apply filter_In in H; intuition.
  Qed.

  (** Effective computation of a list without duplicates *)

  Hypothesis decA: forall x y : A, {x = y} + {x <> y}.

  Fixpoint nodup (l : list A) : list A :=
    match l with
      | [] => []
      | x::xs => if in_dec decA x xs then nodup xs else x::(nodup xs)
    end.

  Lemma nodup_fixed_point (l : list A) :
    NoDup l -> nodup l = l.
  Proof.
    induction l as [| x l IHl]; [auto|]. intros H.
    simpl. destruct (in_dec decA x l) as [Hx | Hx]; rewrite NoDup_cons_iff in H.
    - destruct H as [H' _]. contradiction.
    - destruct H as [_ H']. apply IHl in H'. rewrite -> H'. reflexivity.
  Qed.

  Lemma nodup_In l x : In x (nodup l) <-> In x l.
  Proof.
    induction l as [|a l' Hrec]; simpl.
    - reflexivity.
    - destruct (in_dec decA a l'); simpl; rewrite Hrec.
      * now intuition subst.
      * reflexivity.
  Qed.

  Lemma nodup_incl l1 l2 : incl l1 (nodup l2) <-> incl l1 l2.
  Proof.
    split; intros Hincl a Ha; apply nodup_In; intuition.
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
      + intro H; split.
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
        * f_equal. now apply IH;[apply Nat.succ_lt_mono|]. }
    { induction l as [|a l IHl]; intros H; constructor.
      * intro Ha. apply In_nth_error in Ha. destruct Ha as (n,Hn).
        assert (n < length l) by (now rewrite <- nth_error_Some, Hn).
        specialize (H 0 (S n)). simpl in H. now discriminate H; [apply Nat.lt_0_succ|].
      * apply IHl.
        intros i j Hi %Nat.succ_lt_mono E. now apply eq_add_S, H. }
  Qed.

  Lemma NoDup_nth l d :
    NoDup l <->
    (forall i j, i<length l -> j<length l ->
       nth i l d = nth j l d -> i = j).
  Proof.
    rewrite NoDup_nth_error. split.
    - intros H i j ? ? E. apply H; [assumption|].
      now rewrite !(nth_error_nth' l d), E.
    - intros H i j ? E. assert (j < length l).
      { apply nth_error_Some. rewrite <- E. now apply nth_error_Some. }
      apply H; [assumption ..|].
      rewrite !(nth_error_nth' l d) in E; congruence.
  Qed.

  (** Having [NoDup] hypotheses bring more precise facts about [incl]. *)

  Lemma NoDup_incl_length l l' :
    NoDup l -> incl l l' -> length l <= length l'.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH]; simpl.
   - intros. now apply Nat.le_0_l.
   - intros l' H.
     destruct (Add_inv a l') as (l'', AD). { apply H; simpl; auto. }
     rewrite (Add_length AD). apply le_n_S. apply IH.
     now apply incl_Add_inv with a l'.
  Qed.

  Lemma NoDup_length_incl l l' :
    NoDup l -> length l' <= length l -> incl l l' -> incl l' l.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH].
   - intro l'; destruct l'; easy.
   - intros l' E H x Hx.
     destruct (Add_inv a l') as (l'', AD). { apply H; simpl; auto. }
     rewrite (Add_in AD) in Hx. simpl in Hx.
     destruct Hx as [Hx|Hx]; [left; trivial|right].
     revert x Hx. apply (IH l''); trivial.
     * apply Nat.succ_le_mono. now rewrite <- (Add_length AD).
     * now apply incl_Add_inv with a l'.
  Qed.

  Lemma NoDup_incl_NoDup (l l' : list A) : NoDup l ->
    length l' <= length l -> incl l l' -> NoDup l'.
  Proof.
    revert l'; induction l as [|a l IHl]; simpl; intros l' Hnd Hlen Hincl.
    - now destruct l'; inversion Hlen.
    - assert (In a l') as Ha by now apply Hincl; left.
      apply in_split in Ha as [l1' [l2' ->]].
      inversion_clear Hnd as [|? ? Hnin Hnd'].
      apply (NoDup_Add (Add_app a l1' l2')); split.
      + apply IHl; auto.
        * rewrite length_app.
          rewrite length_app in Hlen; simpl in Hlen; rewrite Nat.add_succ_r in Hlen.
          now apply Nat.succ_le_mono.
        * apply (incl_Add_inv (u:= l1' ++ l2')) in Hincl; auto.
          apply Add_app.
      + intros Hnin'.
        assert (incl (a :: l) (l1' ++ l2')) as Hincl''.
        { apply incl_tran with (l1' ++ a :: l2'); auto.
          intros x Hin.
          apply in_app_or in Hin as [Hin|[->|Hin]]; intuition. }
        apply NoDup_incl_length in Hincl''; [ | now constructor ].
        apply (Nat.nle_succ_diag_l (length l1' + length l2')).
        rewrite_all length_app.
        simpl in Hlen; rewrite Nat.add_succ_r in Hlen.
        now transitivity (S (length l)).
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

  Lemma cons_seq : forall len start, start :: seq (S start) len = seq start (S len).
  Proof.
    reflexivity.
  Qed.

  Lemma length_seq : forall len start, length (seq start len) = len.
  Proof.
    intro len; induction len; simpl; auto.
  Qed.

  Lemma seq_nth : forall len start n d,
    n < len -> nth n (seq start len) d = start+n.
  Proof.
    intro len; induction len as [|len IHlen]; intros start n d H.
    - inversion H.
    - simpl seq.
      destruct n; simpl.
      + now rewrite Nat.add_0_r.
      + now rewrite IHlen; [rewrite Nat.add_succ_r|apply Nat.succ_lt_mono].
  Qed.

  Lemma seq_shift : forall len start,
    map S (seq start len) = seq (S start) len.
  Proof.
    intro len; induction len as [|len IHlen]; simpl; auto.
    intros.
    now rewrite IHlen.
  Qed.

  Lemma in_seq len start n :
    In n (seq start len) <-> start <= n < start+len.
  Proof.
    revert start. induction len as [|len IHlen]; simpl; intros start.
    - rewrite Nat.add_0_r. split;[easy|].
      intros (H,H'). apply (Nat.lt_irrefl start).
      eapply Nat.le_lt_trans; eassumption.
    - rewrite IHlen, Nat.add_succ_r; simpl; split.
      + intros [H|H]; subst; intuition.
        * apply -> Nat.succ_le_mono. apply Nat.le_add_r.
        * now apply Nat.lt_le_incl.
      + intros (H,H'). inversion H.
        * now left.
        * right. subst. now split; [apply -> Nat.succ_le_mono|].
  Qed.

  Lemma seq_NoDup len start : NoDup (seq start len).
  Proof.
   revert start; induction len as [|len IH];
     intros start; simpl; constructor; trivial.
   rewrite in_seq. intros (H,_). now apply (Nat.lt_irrefl start).
  Qed.

  Lemma seq_app : forall len1 len2 start,
    seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
  Proof.
    intro len1; induction len1 as [|len1' IHlen]; intros; simpl in *.
    - now rewrite Nat.add_0_r.
    - now rewrite Nat.add_succ_r, IHlen.
  Qed.

  Lemma seq_S : forall len start, seq start (S len) = seq start len ++ [start + len].
  Proof.
   intros len start.
   change [start + len] with (seq (start + len) 1).
   rewrite <- seq_app.
   rewrite Nat.add_succ_r, Nat.add_0_r; reflexivity.
  Qed.

  Lemma skipn_seq n start len : skipn n (seq start len) = seq (start+n) (len-n).
  Proof.
    revert len; revert start; induction n, len;
      cbn [skipn seq]; rewrite ?Nat.add_0_r, ?IHn; cbn [Nat.add]; auto.
  Qed.

  Lemma nth_error_seq start len n :
    nth_error (seq start len) n =
    if Nat.ltb n len then Some (start + n) else None.
  Proof.
    revert len; revert start; induction n, len;
      cbn [nth_error seq]; rewrite ?Nat.add_0_r; trivial.
    rewrite <-seq_shift, nth_error_map, IHn.
    cbn [Nat.ltb Nat.leb]; case len, Nat.leb; trivial.
    cbn [option_map]; rewrite ?plus_n_Sm; trivial.
  Qed.

End NatSeq.
Notation seq := seq.

(***********************)
(** ** List comparison *)
(***********************)

Section Compare.

  Variable A : Type.
  Variable cmp : A -> A -> comparison.

  Local Notation list_compare := (@list_compare A cmp).

  Section Lemmas.

    Variable Hcmp : forall x y, cmp x y = Eq <-> x = y.

    Lemma list_compare_cons (x : A) (xs ys : list A) :
      list_compare (x :: xs) (x :: ys) = list_compare xs ys.
    Proof.
      simpl. rewrite (proj2 (Hcmp x x) eq_refl). reflexivity.
    Qed.

    Lemma list_compare_app (xs ys zs : list A) :
      list_compare (xs ++ ys) (xs ++ zs) = list_compare ys zs.
    Proof.
      induction xs as [|x xs IH]; [reflexivity|].
      rewrite <-!app_comm_cons, list_compare_cons. exact IH.
    Qed.

    Lemma prefix_eq {prefix1 prefix2 xs1 xs2 ys1 ys2 : list A} {x1 x2 y1 y2 : A} :
      prefix1 ++ x1 :: xs1 = prefix2 ++ x2 :: xs2 ->
      prefix1 ++ y1 :: ys1 = prefix2 ++ y2 :: ys2 ->
      x1 <> y1 ->
      x2 <> y2 ->
      prefix1 = prefix2.
    Proof.
      clear Hcmp cmp.
      intros Heq1 Heq2 Hne1 Hne2.
      revert prefix2 xs1 xs2 ys1 ys2 Heq1 Heq2.
      induction prefix1 as [|z prefix1 IH]; intros prefix2 xs1 xs2 ys1 ys2.
      - destruct prefix2; [reflexivity|]. simpl. intros H1 H2.
        injection H1; clear H1; intros ??; subst.
        injection H2; clear H2; intros ??; subst.
        exfalso. apply Hne1. reflexivity.
      - destruct prefix2.
        + simpl. intros H1 H2.
          injection H1; clear H1; intros ??; subst.
          injection H2; clear H2; intros ??; subst.
          exfalso. apply Hne2. reflexivity.
        + simpl. intros H1 H2.
          injection H1; clear H1; intros ??; subst.
          injection H2; clear H2; intros ?; subst.
          intros. f_equal. eapply IH; eassumption.
    Qed.

    #[local] Ltac list_auto :=
      repeat lazymatch goal with
      | |- ?x = ?x =>
          reflexivity
      | H : ?xs = ?xs ++ _ |- _ =>
          rewrite <-(app_nil_r xs) in H at 1
      | H : ?xs ++ _ = ?xs |- _ =>
          symmetry in H
      | H : ?xs ++ _ = ?xs ++ _ |- _ =>
          apply app_inv_head in H
      | H : _ :: _ = _ :: _ |- _ =>
          injection H; intros; clear H; subst
      | H : [] = _ :: _ |- _ =>
          inversion H
      | H : cmp ?x ?x = Lt |- _ =>
          rewrite (proj2 (Hcmp _ _) eq_refl) in H; discriminate
      | H : cmp ?x ?x = Gt |- _ =>
          rewrite (proj2 (Hcmp _ _) eq_refl) in H; discriminate
      | H1 : ?p1 ++ _ :: _ = ?p2 ++ _ :: _,
        H2 : ?p2 ++ _ :: _ = ?p1 ++ _ :: _ |- _ =>
          symmetry in H2
      | H1 : ?p1 ++ ?x1 :: ?xs1 = ?p2 ++ ?x2 :: ?xs2,
        H2 : ?p1 ++ ?y1 :: ?ys1 = ?p2 ++ ?y2 :: ?ys2 |- _ =>
          assert (p1 = p2) as Hp;
          [ eapply (prefix_eq H1 H2); intros Heq; subst
          | subst; apply app_inv_head in H1, H2 ]
      | H : cmp ?x ?x = _ |- _ =>
          rewrite (proj2 (Hcmp _ _) eq_refl) in H; try discriminate H
      | H1 : cmp ?x1 ?x2 = _,
        H2 : cmp ?x1 ?x2 = _ |- _ =>
          rewrite H1 in H2; discriminate H2
      | Htrans : forall (x y z : A) (c : comparison), cmp x y = c -> cmp y z = c -> cmp x z = c,
        H1 : cmp ?x1 ?x2 = ?c,
        H2 : cmp ?x2 ?x3 = ?c |- _ =>
          pose proof (Htrans x1 x2 x3 c H1 H2); clear H1 H2
      | Hcmp_opp : (forall x y, cmp y x = CompOpp (cmp x y)),
        H1 : cmp ?x1 ?x2 = ?c, H2 : cmp ?x2 ?x1 = ?c |- _ =>
          rewrite Hcmp_opp, H2 in H1; simpl in H1; discriminate H1
      end.

    Inductive ListCompareSpec (xs ys : list A) : forall (c : comparison), Prop :=
      | ListCompareEq :
          xs = ys ->
          ListCompareSpec xs ys Eq
      | ListCompareShorter y ys' :
          ys = xs ++ y :: ys' ->
          ListCompareSpec xs ys Lt
      | ListCompareLonger x xs' :
          xs = ys ++ x :: xs' ->
          ListCompareSpec xs ys Gt
      | ListCompareLt prefix x xs' y ys' :
          xs = prefix ++ x :: xs' ->
          ys = prefix ++ y :: ys' ->
          cmp x y = Lt ->
          ListCompareSpec xs ys Lt
      | ListCompareGt prefix x xs' y ys' :
          xs = prefix ++ x :: xs' ->
          ys = prefix ++ y :: ys' ->
          cmp x y = Gt ->
          ListCompareSpec xs ys Gt.

    Lemma list_compareP (xs ys : list A) :
      ListCompareSpec xs ys (list_compare xs ys).
    Proof.
      assert (xs = [] ++ xs) as Hxs by reflexivity.
      assert (ys = [] ++ ys) as Hys by reflexivity.
      revert Hxs Hys.
      generalize (@nil A) as prefix.
      generalize ys at 2 4.
      generalize xs at 2 4.
      intros xs'; induction xs' as [|x xs' IH]; intros ys' prefix -> ->.
      - destruct ys' as [|y ys']; rewrite app_nil_r; simpl.
        + apply ListCompareEq. reflexivity.
        + eapply ListCompareShorter; reflexivity.
      - destruct ys' as [|y ys']; rewrite ?app_nil_r; simpl.
        + eapply ListCompareLonger; reflexivity.
        + destruct (cmp x y) eqn:Hxy.
          * apply Hcmp in Hxy; subst y.
            apply (IH ys' (prefix ++ [x])); rewrite <-app_assoc; reflexivity.
          * eapply ListCompareLt; [reflexivity|reflexivity|exact Hxy].
          * eapply ListCompareGt; [reflexivity|reflexivity|exact Hxy].
    Qed.

    Lemma list_compare_refl (xs ys : list A) :
      list_compare xs ys = Eq <-> xs = ys.
    Proof.
      destruct (list_compareP xs ys); subst; split; intros.
      all: first [discriminate | list_auto].
    Qed.

    Lemma list_compare_antisym (xs ys : list A) :
      (forall x y, cmp y x = CompOpp (cmp x y)) ->
      list_compare ys xs = CompOpp (list_compare xs ys).
    Proof.
      intros Hcmp_opp.
      destruct (list_compareP xs ys), (list_compareP ys xs); subst.
      all: repeat rewrite <-app_assoc in *; simpl in *; list_auto.
    Qed.

    Lemma list_compare_trans (xs ys zs : list A) (c : comparison) :
      (forall x y z c, cmp x y = c -> cmp y z = c -> cmp x z = c) ->
      (forall x y, cmp y x = CompOpp (cmp x y)) ->
      list_compare xs ys = c -> list_compare ys zs = c -> list_compare xs zs = c.
    Proof.
      intros Hcmp_trans Hcmp_opp.
      destruct
        (list_compareP xs ys) as [?|???|???|p1 x1 xs1 y1 ys1 Hxy1 Hxy2 Hlt1|p1 x1 xs1 y1 ys1 Hxy1 Hxy2 Hgt1],
        (list_compareP ys zs) as [?|???|???|p2 y2 ys2 z2 zs2 Hyz1 Hyz2 Hlt2|p2 y2 ys2 z2 zs2 Hyz1 Hyz2 Hgt2],
        (list_compareP xs zs) as [?|???|???|p3 x3 xs3 z3 zs3 Hxz1 Hxz2 Hlt3|p3 x3 xs3 z3 zs3 Hxz1 Hxz2 Hgt3].
      all: intros <-; try discriminate; intros _; try reflexivity; exfalso.
      all: try (subst; rewrite <-?app_assoc in *; simpl in *; list_auto; fail).
      all: rewrite Hxy1 in Hxz1; rewrite Hxy2 in Hyz1; rewrite Hyz2 in Hxz2; clear Hxy1 Hxy2 Hyz2.
      all: revert p2 p3 xs1 ys1 ys2 zs2 xs3 zs3 Hyz1 Hxz1 Hxz2.
      all: induction p1 as [|h1 p1 IH]; intros; destruct p2 as [|h2 p2]; destruct p3 as [|h3 p3].
      all: simpl in *; list_auto.
      all: eapply IH; eassumption.
    Qed.

    Lemma list_compare_spec_complete (xs ys : list A) (c : comparison) :
      ListCompareSpec xs ys c -> list_compare xs ys = c.
    Proof.
      intros [->|??->|??->|?????->->Heq|?????->->Heq].
      - apply list_compare_refl. reflexivity.
      - rewrite <-(app_nil_r xs) at 1. apply list_compare_app.
      - rewrite <-(app_nil_r ys) at 2. apply list_compare_app.
      - rewrite list_compare_app. simpl. rewrite Heq. reflexivity.
      - rewrite list_compare_app. simpl. rewrite Heq. reflexivity.
    Qed.

  End Lemmas.

End Compare.
Notation list_compare := list_compare.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate.

    Variable P:A->Prop.

    Inductive Exists : list A -> Prop :=
      | Exists_cons_hd : forall x l, P x -> Exists (x::l)
      | Exists_cons_tl : forall x l, Exists l -> Exists (x::l).

    #[local]
    Hint Constructors Exists : core.

    Lemma Exists_exists (l:list A) :
      Exists l <-> (exists x, In x l /\ P x).
    Proof.
      split.
      - induction 1; firstorder.
      - induction l; firstorder (subst; auto).
    Qed.

    Lemma Exists_nth l :
      Exists l <-> exists i d, i < length l /\ P (nth i l d).
    Proof.
      split.
      - intros HE; apply Exists_exists in HE.
        destruct HE as [a [Hin HP]].
        apply (In_nth _ _ a) in Hin; destruct Hin as [i [Hl Heq]].
        rewrite <- Heq in HP.
        now exists i; exists a.
      - intros [i [d [Hl HP]]].
        apply Exists_exists; exists (nth i l d); split.
        + apply nth_In; assumption.
        + assumption.
    Qed.

    Lemma Exists_nil : Exists [] <-> False.
    Proof. split; inversion 1. Qed.

    Lemma Exists_cons x l:
      Exists (x::l) <-> P x \/ Exists l.
    Proof. split; inversion 1; auto. Qed.

    Lemma Exists_app l1 l2 :
      Exists (l1 ++ l2) <-> Exists l1 \/ Exists l2.
    Proof.
      induction l1; simpl; split; intros HE; try now intuition.
      - inversion_clear HE; intuition.
      - destruct HE as [HE|HE]; intuition.
        inversion_clear HE; intuition.
    Qed.

    Lemma Exists_rev l : Exists l -> Exists (rev l).
    Proof.
      induction l; intros HE; intuition.
      inversion_clear HE; simpl; apply Exists_app; intuition.
    Qed.

    Lemma Exists_dec l:
      (forall x:A, {P x} + { ~ P x }) ->
      {Exists l} + {~ Exists l}.
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - right. abstract now rewrite Exists_nil.
      - destruct Hrec as [Hl'|Hl'].
        + left. now apply Exists_cons_tl.
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Exists_cons_hd.
          * right. abstract now inversion 1.
    Defined.

    Lemma Exists_fold_right l :
      Exists l <-> fold_right (fun x => or (P x)) False l.
    Proof.
      induction l; simpl; split; intros HE; try now inversion HE; intuition.
    Qed.

    Lemma incl_Exists l1 l2 : incl l1 l2 -> Exists l1 -> Exists l2.
    Proof.
      intros Hincl HE.
      apply Exists_exists in HE; destruct HE as [a [Hin HP]].
      apply Exists_exists; exists a; intuition.
    Qed.

    #[local]
    Hint Constructors Forall : core.

    Local Notation Forall := (@Forall A P).

    Lemma Forall_inv : forall (a:A) l, Forall (a :: l) -> P a.
    Proof.
      intros a l H; inversion H; trivial.
    Qed.

    Theorem Forall_inv_tail : forall (a:A) l, Forall (a :: l) -> Forall l.
    Proof.
      intros a l H; inversion H; trivial.
    Qed.

    Lemma Forall_nil_iff : Forall [] <-> True.
    Proof.
      easy.
    Qed.

    Lemma Forall_cons_iff : forall (a:A) l, Forall (a :: l) <-> P a /\ Forall l.
    Proof.
      intros. now split; [intro H; inversion H|constructor].
    Qed.

    Lemma Forall_forall (l:list A):
      Forall l <-> (forall x, In x l -> P x).
    Proof.
      split.
      - induction 1; firstorder (subst; auto).
      - induction l; firstorder auto with datatypes.
    Qed.

    Lemma Forall_nth l :
      Forall l <-> forall i d, i < length l -> P (nth i l d).
    Proof.
      split.
      - intros HF i d Hl.
        apply (Forall_forall l).
        + assumption.
        + apply nth_In; assumption.
      - intros HF.
        apply Forall_forall; intros a Hin.
        apply (In_nth _ _ a) in Hin; destruct Hin as [i [Hl Heq]].
        rewrite <- Heq; intuition.
    Qed.

    Lemma Forall_app l1 l2 :
      Forall (l1 ++ l2) <-> Forall l1 /\ Forall l2.
    Proof.
      induction l1 as [|a l1 IH]; cbn.
      - now rewrite Forall_nil_iff.
      - now rewrite !Forall_cons_iff, IH, and_assoc.
    Qed.

    Lemma Forall_elt a l1 l2 : Forall (l1 ++ a :: l2) -> P a.
    Proof.
      intros HF; apply Forall_app in HF; destruct HF as [HF1 HF2]; now inversion HF2.
    Qed.

    Lemma Forall_rev l : Forall l -> Forall (rev l).
    Proof.
      induction l; intros HF; [assumption|].
      inversion_clear HF; simpl; apply Forall_app; intuition.
    Qed.

    Lemma Forall_rect : forall (Q : list A -> Type),
      Q [] -> (forall b l, P b -> Q (b :: l)) -> forall l, Forall l -> Q l.
    Proof.
      intros Q H H' l; induction l; intro; [|eapply H', Forall_inv]; eassumption.
    Qed.

    Lemma Forall_dec :
      (forall x:A, {P x} + { ~ P x }) ->
      forall l:list A, {Forall l} + {~ Forall l}.
    Proof.
      intros Pdec l. induction l as [|a l' Hrec].
      - left. apply Forall_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_cons.
          * right. abstract now inversion 1.
        + right. abstract now inversion 1.
    Defined.

    Lemma Forall_fold_right l :
      Forall l <-> fold_right (fun x => and (P x)) True l.
    Proof.
      induction l; simpl; split; intros HF; try now inversion HF; intuition.
    Qed.

    Lemma incl_Forall l1 l2 : incl l2 l1 -> Forall l1 -> Forall l2.
    Proof.
      intros Hincl HF.
      apply Forall_forall; intros a Ha.
      apply (Forall_forall l1); intuition.
    Qed.

  End One_predicate.
  Local Notation Forall := (@Forall A).

  Lemma map_ext_Forall B : forall (f g : A -> B) l,
    Forall (fun x => f x = g x) l -> map f l = map g l.
  Proof.
    intros; apply map_ext_in, Forall_forall; assumption.
  Qed.

  Theorem Exists_impl : forall (P Q : A -> Prop), (forall a : A, P a -> Q a) ->
    forall l, Exists P l -> Exists Q l.
  Proof.
    intros P Q H l H0.
    induction H0 as [x l H0|x l H0 IHExists].
    - apply (Exists_cons_hd Q x l (H x H0)).
    - apply (Exists_cons_tl x IHExists).
  Qed.

  Lemma Exists_or : forall (P Q : A -> Prop) l,
    Exists P l \/ Exists Q l -> Exists (fun x => P x \/ Q x) l.
  Proof.
    intros P Q l; induction l as [|a l IHl]; intros [H | H]; inversion H; subst.
    1,3: apply Exists_cons_hd; auto.
    all: apply Exists_cons_tl, IHl; auto.
  Qed.

  Lemma Exists_or_inv : forall (P Q : A -> Prop) l,
    Exists (fun x => P x \/ Q x) l -> Exists P l \/ Exists Q l.
  Proof.
    intros P Q l; induction l as [|a l IHl];
     intro Hl; inversion Hl as [ ? ? H | ? ? H ]; subst.
    - inversion H; now repeat constructor.
    - destruct (IHl H); now repeat constructor.
  Qed.

  Lemma Forall_impl : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
    forall l, Forall P l -> Forall Q l.
  Proof.
    intros P Q H l. rewrite !Forall_forall. firstorder.
  Qed.

  Lemma Forall_and : forall (P Q : A -> Prop) l,
    Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
  Proof.
    intros P Q l; induction l; intros HP HQ; constructor; inversion HP; inversion HQ; auto.
  Qed.

  Lemma Forall_and_inv : forall (P Q : A -> Prop) l,
    Forall (fun x => P x /\ Q x) l -> Forall P l /\ Forall Q l.
  Proof.
    intros P Q l; induction l; intro Hl; split; constructor; inversion Hl; firstorder.
  Qed.

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
    apply Exists_Forall_neg; intros x.
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

  Lemma incl_Forall_in_iff l l' :
    incl l l' <-> Forall (fun x => In x l') l.
  Proof. now rewrite Forall_forall; split. Qed.

End Exists_Forall.
Notation Forall := Forall.
Notation Forall_nil := ListDef.Forall_nil (only parsing).
Notation Forall_cons := ListDef.Forall_cons (only parsing).

#[global]
Hint Constructors Exists : core.
#[global]
Hint Constructors Forall : core.

Lemma Exists_map A B (f : A -> B) P l :
  Exists P (map f l) <-> Exists (fun x => P (f x)) l.
Proof.
  induction l as [|a l IHl].
  - cbn. now rewrite Exists_nil.
  - cbn. now rewrite ?Exists_cons, IHl.
Qed.

Lemma Exists_concat A P (ls : list (list A)) :
  Exists P (concat ls) <-> Exists (Exists P) ls.
Proof.
  induction ls as [|l ls IHls].
  - cbn. now rewrite Exists_nil.
  - cbn. now rewrite Exists_app, Exists_cons, IHls.
Qed.

Lemma Exists_flat_map A B P ls (f : A -> list B) :
  Exists P (flat_map f ls) <-> Exists (fun d => Exists P (f d)) ls.
Proof.
  now rewrite flat_map_concat_map, Exists_concat, Exists_map.
Qed.

Lemma Forall_map A B (f : A -> B) P l :
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  induction l as [|a l IHl]; cbn.
  - now rewrite !Forall_nil_iff.
  - now rewrite !Forall_cons_iff, IHl.
Qed.

Lemma Forall_concat A P (ls : list (list A)) :
  Forall P (concat ls) <-> Forall (Forall P) ls.
Proof.
  induction ls as [|l ls IHls]; cbn.
  - now rewrite !Forall_nil_iff.
  - now rewrite Forall_app, Forall_cons_iff, IHls.
Qed.

Lemma Forall_flat_map A B P ls (f : A -> list B) :
  Forall P (flat_map f ls) <-> Forall (fun d => Forall P (f d)) ls.
Proof.
  now rewrite flat_map_concat_map, Forall_concat, Forall_map.
Qed.

Lemma exists_Forall A B : forall (P : A -> B -> Prop) l,
  (exists k, Forall (P k) l) -> Forall (fun x => exists k, P k x) l.
Proof.
  intros P l; induction l as [|a l IHl]; intros [k HF]; constructor; inversion_clear HF.
  - now exists k.
  - now apply IHl; exists k.
Qed.

Lemma Forall_image A B : forall (f : A -> B) l,
  Forall (fun y => exists x, y = f x) l <-> exists l', l = map f l'.
Proof.
  intros f l; induction l as [|a l IHl]; split; intros HF.
  - exists nil; reflexivity.
  - constructor.
  - apply Forall_cons_iff in HF as [[x ->] [l' ->] %IHl].
    now exists (x :: l').
  - destruct HF as [l' Heq].
    symmetry in Heq; apply map_eq_cons in Heq.
    destruct Heq as (x & tl & ? & ? & ?); subst.
    constructor.
    + now exists x.
    + now apply IHl; exists tl.
Qed.

Lemma concat_nil_Forall A : forall (l : list (list A)),
  concat l = [] <-> Forall (fun x => x = []) l.
Proof.
  intro l; induction l as [|a l IHl]; simpl; split; intros Hc; auto.
  - apply app_eq_nil in Hc.
    constructor; firstorder.
  - inversion Hc; subst; simpl.
    now apply IHl.
Qed.

Lemma in_flat_map_Exists A B : forall (f : A -> list B) x l,
  In x (flat_map f l) <-> Exists (fun y => In x (f y)) l.
Proof.
  intros f x l; rewrite in_flat_map.
  split; apply Exists_exists.
Qed.

Lemma notin_flat_map_Forall A B : forall (f : A -> list B) x l,
  ~ In x (flat_map f l) <-> Forall (fun y => ~ In x (f y)) l.
Proof.
  intros f x l; rewrite Forall_Exists_neg.
  apply not_iff_compat, in_flat_map_Exists.
Qed.


Section Forall2.

  (** [Forall2]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Prop.

  Inductive Forall2 : list A -> list B -> Prop :=
    | Forall2_nil : Forall2 [] []
    | Forall2_cons : forall x y l l',
      R x y -> Forall2 l l' -> Forall2 (x::l) (y::l').

  #[local]
  Hint Constructors Forall2 : core.

  (* NB: when deprecation phase ends, instead of removing prove "Reflexive R -> Reflexive Forall2"
     and close #6131 *)
  #[deprecated(since = "8.18", use = Forall2_nil)]
  Theorem Forall2_refl : Forall2 [] [].
  Proof. intros; apply Forall2_nil. Qed.

  Theorem Forall2_cons_iff : forall x y l l',
    Forall2 (x :: l) (y :: l') <-> R x y /\ Forall2 l l'.
  Proof.
    intros x y l l'. split.
    - intros H. now inversion H.
    - intros [? ?]. now constructor.
  Qed.

  Theorem Forall2_length : forall l l',
    Forall2 l l' -> length l = length l'.
  Proof.
    intros l. induction l as [|x l IH]; intros l' Hl'; inversion Hl'.
    - reflexivity.
    - cbn. f_equal. now apply IH.
  Qed.

  Theorem Forall2_app_inv_l : forall l1 l2 l',
    Forall2 (l1 ++ l2) l' ->
    exists l1' l2', Forall2 l1 l1' /\ Forall2 l2 l2' /\ l' = l1' ++ l2'.
  Proof.
    intro l1; induction l1 as [|a l1 IHl1]; intros l2 l' H.
    - exists [], l'; auto.
    - simpl in H; inversion H as [|? y ? ? ? H4]; subst; clear H.
      apply IHl1 in H4 as (l1' & l2' & Hl1 & Hl2 & ->).
      exists (y::l1'), l2'; simpl; auto.
  Qed.

  Theorem Forall2_app_inv_r : forall l1' l2' l,
    Forall2 l (l1' ++ l2') ->
    exists l1 l2, Forall2 l1 l1' /\ Forall2 l2 l2' /\ l = l1 ++ l2.
  Proof.
    intro l1'; induction l1' as [|a l1' IHl1']; intros l2' l H.
    - exists [], l; auto.
    - simpl in H; inversion H as [|x ? ? ? ? H4]; subst; clear H.
      apply IHl1' in H4 as (l1 & l2 & Hl1 & Hl2 & ->).
      exists (x::l1), l2; simpl; auto.
  Qed.

  Theorem Forall2_app : forall l1 l2 l1' l2',
    Forall2 l1 l1' -> Forall2 l2 l2' -> Forall2 (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros l1 l2 l1' l2' H H0. induction l1 in l1', H, H0 |- *; inversion H; subst; simpl; auto.
  Qed.

  Theorem Forall_Exists_exists_Forall2 l1 l2 :
    Forall (fun a => Exists (R a) l2) l1 ->
    exists l2', Forall2 l1 l2' /\ incl l2' l2.
  Proof.
    induction l1 as [|a l1 IH].
    - intros _. now exists [].
    - intros [[b [Hb Hab]] %Exists_exists Hl1l2] %Forall_cons_iff.
      destruct (IH Hl1l2) as [l2' [Hl1l2' Hl2'l2]].
      exists (b :: l2'). now eauto using incl_cons.
  Qed.
End Forall2.

Lemma Forall2_impl (A B : Type) (R1 R2 : A -> B -> Prop) : (forall a b, R1 a b -> R2 a b) ->
  forall l1 l2, Forall2 R1 l1 l2 -> Forall2 R2 l1 l2.
Proof.
  intros HPQ l1 l2 HPl1l2. induction HPl1l2; now eauto using Forall2.
Qed.

Lemma Forall2_flip (A B : Type) (R : A -> B -> Prop) l1 l2 :
  Forall2 R l1 l2 -> Forall2 (fun b a => R a b) l2 l1.
Proof.
  intros HPl1l2. induction HPl1l2; now eauto using Forall2.
Qed.

#[global]
Hint Constructors Forall2 : core.

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
    | FOP_nil : ForallOrdPairs []
    | FOP_cons : forall a l,
      Forall (R a) l -> ForallOrdPairs l -> ForallOrdPairs (a::l).

  #[local]
  Hint Constructors ForallOrdPairs : core.

  Lemma ForallOrdPairs_In : forall l,
    ForallOrdPairs l ->
    forall x y, In x l -> In y l -> x=y \/ R x y \/ R y x.
  Proof.
    induction 1.
    - inversion 1.
    - simpl; destruct 1; destruct 1; subst; auto.
      + right; left. apply -> Forall_forall; eauto.
      + right; right. apply -> Forall_forall; eauto.
  Qed.

  (** [ForallPairs] implies [ForallOrdPairs]. The reverse implication is true
    only when [R] is symmetric and reflexive. *)

  Lemma ForallPairs_ForallOrdPairs l: ForallPairs l -> ForallOrdPairs l.
  Proof.
    induction l as [|a l IHl]; [easy|].
    intros H. constructor.
    - rewrite Forall_forall. intros; apply H; simpl; auto.
    - apply IHl. red; intros; apply H; simpl; auto.
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

Lemma NoDup_iff_ForallOrdPairs [A] (l: list A):
  NoDup l <-> ForallOrdPairs (fun a b => a <> b) l.
Proof.
  split; intro H.
  - induction H; constructor.
    + apply Forall_forall.
      intros y Hy ->. contradiction.
    + assumption.
  - induction H as [|a l H1 H2]; constructor.
    + rewrite Forall_forall in H1. intro E.
      contradiction (H1 a E). reflexivity.
    + assumption.
Qed.

Lemma NoDup_map_NoDup_ForallPairs [A B] (f: A->B) (l: list A) :
  ForallPairs (fun x y => f x = f y -> x = y) l -> NoDup l -> NoDup (map f l).
Proof.
  intros Hinj Hl.
  induction Hl as [|x ?? _ IH]; cbn; constructor.
  - intros [y [??]]%in_map_iff.
    destruct (Hinj y x); cbn; auto.
  - apply IH.
    intros x' y' Hx' Hy'.
    now apply Hinj; right.
Qed.

Lemma NoDup_concat [A] (L: list (list A)):
  Forall (@NoDup A) L ->
  ForallOrdPairs (fun l1 l2 => forall a, In a l1 -> ~ In a l2) L ->
  NoDup (concat L).
Proof.
  intros H1 H2. induction L as [|l1 L IHL]; [constructor|].
  cbn. apply NoDup_app.
  - apply Forall_inv in H1. assumption.
  - apply IHL.
    + apply Forall_inv_tail in H1. assumption.
    + inversion H2. assumption.
  - intros a aInl1 ainL%in_concat. destruct ainL as [l2 [l2inL ainL2]].
    inversion H2 as [|l L' H3].
    rewrite Forall_forall in H3.
    apply (H3 _ l2inL _ aInl1). assumption.
Qed.

Section Repeat.

  Variable A : Type.

  Local Notation repeat := (@repeat A).

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

  Lemma repeat_cons n a :
    a :: repeat a n = repeat a n ++ [a].
  Proof.
    induction n as [|n IHn]; simpl.
    - reflexivity.
    - f_equal; apply IHn.
  Qed.

  Lemma repeat_app x n m :
    repeat x (n + m) = repeat x n ++ repeat x m.
  Proof.
    induction n as [|n IHn]; simpl; auto.
    now rewrite IHn.
  Qed.

  Lemma repeat_eq_app x n l1 l2 :
    repeat x n = l1 ++ l2 -> repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
  Proof.
    revert n; induction l1 as [|a l1 IHl1]; simpl; intros n Hr; subst.
    - repeat split; now rewrite repeat_length.
    - destruct n; inversion Hr as [ [Heq Hr0] ]; subst.
      now apply IHl1 in Hr0 as [-> ->].
  Qed.

  Lemma repeat_eq_cons x y n l :
    repeat x n = y :: l -> x = y /\ repeat x (pred n) = l.
  Proof.
    intros Hr.
    destruct n; inversion_clear Hr; auto.
  Qed.

  Lemma repeat_eq_elt x y n l1 l2 :
    repeat x n = l1 ++ y :: l2 -> x = y /\ repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
  Proof.
    intros Hr; apply repeat_eq_app in Hr as [Hr1 Hr2]; subst.
    apply repeat_eq_cons in Hr2; intuition.
  Qed.

  Lemma Forall_eq_repeat x l :
    Forall (eq x) l -> l = repeat x (length l).
  Proof.
    induction l as [|a l IHl]; simpl; intros HF; auto.
    inversion_clear HF as [ | ? ? ? HF']; subst.
    now rewrite (IHl HF') at 1.
  Qed.

  Hypothesis decA : forall x y : A, {x = y}+{x <> y}.

  Lemma count_occ_repeat_eq x y n : x = y -> count_occ decA (repeat y n) x = n.
  Proof.
    intros ->.
    induction n; cbn; auto.
    destruct (decA y y); auto.
    exfalso; intuition.
  Qed.

  Lemma count_occ_repeat_neq x y n : x <> y -> count_occ decA (repeat y n) x = 0.
  Proof.
    intros Hneq.
    induction n; cbn; auto.
    destruct (decA y x); auto.
    exfalso; intuition.
  Qed.

  Lemma count_occ_unique x l : count_occ decA l x = length l -> l = repeat x (length l).
  Proof.
    induction l as [|h l]; cbn; intros Hocc; auto.
    destruct (decA h x).
    - f_equal; intuition.
    - assert (Hb := count_occ_bound decA x l).
      rewrite Hocc in Hb.
      exfalso; apply (Nat.nle_succ_diag_l _ Hb).
  Qed.

  Lemma count_occ_repeat_excl x l :
    (forall y, y <> x -> count_occ decA l y = 0) -> l = repeat x (length l).
  Proof.
    intros Hocc.
    apply Forall_eq_repeat, Forall_forall; intros z Hin.
    destruct (decA z x) as [Heq|Hneq]; auto.
    apply Hocc, count_occ_not_In in Hneq; intuition.
  Qed.

  Lemma count_occ_sgt l x : l = [x] <->
    count_occ decA l x = 1 /\ forall y, y <> x -> count_occ decA l y = 0.
  Proof.
    split.
    - intros ->; cbn; split; intros; destruct decA; subst; intuition.
    - intros [Heq Hneq].
      apply count_occ_repeat_excl in Hneq.
      rewrite Hneq, count_occ_repeat_eq in Heq; trivial.
      now rewrite Heq in Hneq.
  Qed.

  Lemma nth_repeat a m n :
    nth n (repeat a m) a = a.
  Proof.
    revert n. induction m as [|m IHm].
    - now intros [|n].
    - intros [|n]; [reflexivity|exact (IHm n)].
  Qed.

  Lemma nth_repeat_lt a m n d :
    n < m ->
    nth n (repeat a m) d = a.
  Proof.
    revert n. induction m as [|m IHm].
    - now intros [|n].
    - intros [|n]; [reflexivity|].
      intros Hlt%Nat.succ_lt_mono. apply (IHm _ Hlt).
  Qed.

  Lemma nth_error_repeat a m n :
    n < m -> nth_error (repeat a m) n = Some a.
  Proof.
    intro Hnm. rewrite (nth_error_nth' _ a).
    - now rewrite nth_repeat.
    - now rewrite repeat_length.
  Qed.

End Repeat.
Notation repeat := repeat.

Lemma repeat_to_concat A n (a:A) :
  repeat a n = concat (repeat [a] n).
Proof.
  induction n as [|n IHn]; simpl.
  - reflexivity.
  - f_equal; apply IHn.
Qed.

Lemma map_repeat A B (a:A) n (f : A -> B):
  map f (repeat a n) = repeat (f a) n.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - cbn. f_equal. exact IHn.
Qed.

Lemma map_const (A B : Type) (b : B) (l : list A) :
  map (fun _ => b) l = repeat b (length l).
Proof. induction l; cbn [repeat map length]; congruence. Qed.

Lemma rev_repeat A n (a:A):
  rev (repeat a n) = repeat a n.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - cbn. rewrite IHn. symmetry. apply repeat_cons.
Qed.

Lemma fst_list_prod [A B] l l' : map fst (@list_prod A B l l') =
  flat_map (fun a => repeat a (length l')) l.
Proof.
  revert l'; induction l; intros; trivial. cbn.
  erewrite map_app, map_map, map_ext, map_const; eauto using f_equal2.
Qed.
#[deprecated(use = fst_list_prod)]
Notation map_fst_list_prod := fst_list_prod (only parsing).

Lemma snd_list_prod [A B] l l' : map snd (@list_prod A B l l') =
  concat (repeat l' (length l)).
Proof.
  revert l'; induction l; intros; trivial. cbn.
  erewrite map_app, map_map, map_ext, map_id; eauto using f_equal2.
Qed.
#[deprecated(use = snd_list_prod)]
Notation map_snd_list_prod := snd_list_prod (only parsing).

(** Sum of elements of a list of [nat]: [list_sum] *)

Definition list_sum l := fold_right plus 0 l.

Lemma list_sum_app : forall l1 l2,
   list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof.
intro l1; induction l1 as [|a l1 IHl1]; intros l2; [ reflexivity | ].
simpl; rewrite IHl1.
apply Nat.add_assoc.
Qed.

Lemma length_concat A l:
  length (concat l) = list_sum (map (@length A) l).
Proof.
  induction l; [reflexivity|].
  simpl. rewrite length_app.
  f_equal. assumption.
Qed.

Lemma length_flat_map A B (f: A -> list B) l:
  length (flat_map f l) = list_sum (map (fun x => length (f x)) l).
Proof.
  rewrite flat_map_concat_map, length_concat, map_map. reflexivity.
Qed.

Corollary flat_map_constant_length A B c (f: A -> list B) l:
  (forall x, In x l -> length (f x) = c) -> length (flat_map f l) = (length l) * c.
Proof.
  intro H. rewrite length_flat_map.
  induction l as [ | a l IHl ]; [reflexivity|].
  simpl. rewrite IHl, H; [reflexivity | left; reflexivity | ].
  intros x Hx. apply H. right. assumption.
Qed.

Lemma length_list_power (A B:Type)(l:list A) (l':list B):
    length (list_power l l') = (length l')^(length l).
Proof.
  induction l as [ | a m IH ]; [reflexivity|].
  cbn. rewrite flat_map_constant_length with (c := length l').
  - rewrite IH. apply Nat.mul_comm.
  - intros x H. apply length_map.
Qed.

(** Max of elements of a list of [nat]: [list_max] *)

Definition list_max l := fold_right max 0 l.

Lemma list_max_app : forall l1 l2,
   list_max (l1 ++ l2) = max (list_max l1) (list_max l2).
Proof.
intro l1; induction l1 as [|a l1 IHl1]; intros l2; [ reflexivity | ].
now simpl; rewrite IHl1, Nat.max_assoc.
Qed.

Lemma list_max_le : forall l n,
  list_max l <= n <-> Forall (fun k => k <= n) l.
Proof.
  intro l; induction l as [|a l IHl]; simpl; intros n; split.
  - now intros.
  - intros. now apply Nat.le_0_l.
  - intros [? ?] %Nat.max_lub_iff. now constructor; [|apply IHl].
  - now rewrite Forall_cons_iff, <- IHl, Nat.max_lub_iff.
Qed.

Lemma list_max_lt : forall l n, l <> [] ->
  list_max l < n <-> Forall (fun k => k < n) l.
Proof.
intro l; induction l as [|a l IHl]; simpl; intros n Hnil; split; intros H; intuition.
- destruct l.
  + repeat constructor.
    now simpl in H; rewrite Nat.max_0_r in H.
  + apply Nat.max_lub_lt_iff in H.
    now constructor; [ | apply IHl ].
- destruct l; inversion_clear H as [ | ? ? Hlt HF ].
  + now simpl; rewrite Nat.max_0_r.
  + apply IHl in HF.
    * now apply Nat.max_lub_lt_iff.
    * intros Heq; inversion Heq.
Qed.


(** * Inversion of predicates over lists based on head symbol *)

Ltac is_list_constr c :=
 match c with
  | [] => idtac
  | _ :: _ => idtac
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


Global Hint Rewrite
  rev_involutive (* rev (rev l) = l *)
  rev_unit (* rev (l ++ a :: nil) = a :: rev l *)
  map_nth (* nth n (map f l) (f d) = f (nth n l d) *)
  length_map (* length (map f l) = length l *)
  length_seq (* length (seq start len) = len *)
  length_app (* length (l ++ l') = length l + length l' *)
  length_rev (* length (rev l) = length l *)
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
#[deprecated(since = "8.18", use = app_assoc)]
Notation ass_app := app_assoc (only parsing).
#[deprecated(since = "8.18", use = app_assoc)]
Notation app_ass := app_assoc_reverse_deprecated (only parsing).
Notation In_split := in_split (only parsing).
Notation In_rev := in_rev (only parsing).
Notation In_dec := in_dec (only parsing).
Notation distr_rev := rev_app_distr (only parsing).
Notation rev_acc := rev_append (only parsing).
Notation rev_acc_rev := rev_append_rev (only parsing).
Notation AllS := Forall (only parsing). (* was formerly in TheoryList *)

#[deprecated(since = "8.18", use = app_nil_r)]
Notation app_nil_end := app_nil_end_deprecated (only parsing).
#[deprecated(since = "8.18", use = app_assoc)]
Notation app_assoc_reverse := app_assoc_reverse_deprecated (only parsing).
#[deprecated(since = "8.20", use = nth_error_cons_succ)]
Notation nth_error_cons_S := nth_error_cons_succ.

#[global]
Hint Resolve app_nil_end_deprecated : datatypes.

#[deprecated(since = "8.20", use = length_app)]
Notation app_length := length_app (only parsing).
#[deprecated(since = "8.20", use = length_rev)]
Notation rev_length := length_rev (only parsing).
#[deprecated(since = "8.20", use = length_map)]
Notation map_length := length_map (only parsing).
#[deprecated(since = "8.20", use = fold_left_S_0)]
Notation fold_left_length := fold_left_S_0 (only parsing).
#[deprecated(since = "8.20", use = length_fst_split)]
Notation split_length_l := length_fst_split (only parsing).
#[deprecated(since = "8.20", use = length_snd_split)]
Notation split_length_r := length_snd_split (only parsing).
#[deprecated(since = "8.20", use = length_combine)]
Notation combine_length := length_combine (only parsing).
#[deprecated(since = "8.20", use = length_prod)]
Notation prod_length := length_prod (only parsing).
#[deprecated(since = "8.20", use = length_firstn)]
Notation firstn_length := length_firstn (only parsing).
#[deprecated(since = "8.20", use = length_skipn)]
Notation skipn_length := length_skipn (only parsing).
#[deprecated(since = "8.20", use = length_seq)]
Notation seq_length := length_seq (only parsing).
#[deprecated(since = "8.20", use = length_concat)]
Notation concat_length := length_concat (only parsing).
#[deprecated(since = "8.20", use = length_flat_map)]
Notation flat_map_length := length_flat_map (only parsing).
#[deprecated(since = "8.20", use = length_list_power)]
Notation nth_error_O := nth_error_0 (only parsing).
Notation firstn_O := firstn_0 (only parsing).
Notation skipn_O := skipn_0 (only parsing).
Notation list_power_length := length_list_power (only parsing).
(* end hide *)


(* Unset Universe Polymorphism. *)
