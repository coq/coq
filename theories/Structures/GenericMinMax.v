(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Require Import OrderedType2 OrderedType2Facts Setoid Morphisms Basics.

(** * A Generic construction of min and max based on OrderedType *)

(** ** First, an interface for types with [max] and/or [min] *)

Module Type HasMax (Import O:OrderedTypeFull).
 Parameter Inline max : t -> t -> t.
 Parameter max_spec : forall x y,
   (lt x y /\ eq (max x y) y)  \/  (le y x /\ eq (max x y) x).
End HasMax.

Module Type HasMin (Import O:OrderedTypeFull).
 Parameter Inline min : t -> t -> t.
 Parameter min_spec : forall x y,
   (lt x y /\ eq (min x y) x)  \/  (le y x /\ eq (min x y) y).
End HasMin.

Module Type HasMinMax (Import O:OrderedTypeFull).
 Include Type HasMax O.
 Include Type HasMin O.
End HasMinMax.


(** ** Any [OrderedTypeFull] can be equipped by [max] and [min]
    based on the compare function. *)

Definition gmax {A} (cmp : A->A->comparison) x y :=
 match cmp x y with Lt => y | _ => x end.
Definition gmin {A} (cmp : A->A->comparison) x y :=
 match cmp x y with Gt => y | _ => x end.

Module GenericMinMax (Import O:OrderedTypeFull) <: HasMinMax O.

 Definition max := gmax O.compare.
 Definition min := gmin O.compare.

 Lemma max_spec : forall x y,
   (lt x y /\ eq (max x y) y)  \/  (le y x /\ eq (max x y) x).
 Proof.
  intros. rewrite le_lteq. unfold max, gmax.
  destruct (compare_spec x y); auto with relations.
 Qed.

 Lemma min_spec : forall x y,
   (lt x y /\ eq (min x y) x)  \/  (le y x /\ eq (min x y) y).
 Proof.
  intros. rewrite le_lteq. unfold min, gmin.
  destruct (compare_spec x y); auto with relations.
 Qed.

End GenericMinMax.


(** ** Consequences of the minimalist interface: facts about [max]. *)

Module MaxProperties (Import O:OrderedTypeFull)(Import M:HasMax O).
 Module Import OF := OrderedTypeFullFacts O.
 Infix "<" := lt.
 Infix "==" := eq (at level 70).
 Infix "<=" := le.

Instance max_compat : Proper (eq==>eq==>eq) max.
Proof.
intros x x' Hx y y' Hy.
assert (H1 := max_spec x y). assert (H2 := max_spec x' y').
set (m := max x y) in *; set (m' := max x' y') in *; clearbody m m'.
rewrite <- Hx, <- Hy in *.
destruct (compare_spec x y); intuition; order.
Qed.

(** An alias to the [max_spec] of the interface. *)

Lemma max_spec : forall n m,
  (n < m /\ max n m == m)  \/ (m <= n /\ max n m == n).
Proof. exact max_spec. Qed.

(** A more symmetric version of [max_spec], based only on [le].
    Beware that left and right alternatives overlap. *)

Lemma max_spec_le : forall n m,
 (n <= m /\ max n m == m) \/ (m <= n /\ max n m == n).
Proof.
 intros. destruct (max_spec n m); [left|right]; intuition; order.
Qed.

(** Another function satisfying the same specification is equal to [max]. *)

Lemma max_unicity : forall n m p,
 ((n < m /\ p == m)  \/ (m <= n /\ p == n)) ->  p == max n m.
Proof.
 intros. assert (Hm := max_spec n m).
 destruct (compare_spec n m); intuition; order.
Qed.

Lemma max_unicity_ext : forall f,
 (forall n m, (n < m /\ f n m == m)  \/ (m <= n /\ f n m == n)) ->
 (forall n m, f n m == max n m).
Proof.
 intros. apply max_unicity; auto.
Qed.

(** Induction principles for [max]. *)

Lemma max_case_strong : forall n m (P:t -> Type),
  (forall x y, x==y -> P x -> P y) ->
  (m<=n -> P n) -> (n<=m -> P m) -> P (max n m).
Proof.
intros n m P Compat Hl Hr.
assert (H:=compare_spec n m). assert (H':=max_spec n m).
destruct (compare n m).
apply (Compat m), Hr; inversion_clear H; intuition; order.
apply (Compat m), Hr; inversion_clear H; intuition; order.
apply (Compat n), Hl; inversion_clear H; intuition; order.
Qed.

Lemma max_case : forall n m (P:t -> Type),
  (forall x y, x == y -> P x -> P y) ->
  P n -> P m -> P (max n m).
Proof.
 intros. apply max_case_strong; auto.
Defined.

(** [max] returns one of its arguments. *)

Lemma max_dec : forall n m, {max n m == n} + {max n m == m}.
Proof.
 intros n m. apply max_case; auto with relations.
 intros x y H [E|E]; [left|right]; order.
Defined.

(** [max] commutes with monotone functions. *)

Lemma max_monotone: forall f,
 (Proper (eq ==> eq) f) ->
 (Proper (le ==> le) f) ->
 forall x y, max (f x) (f y) == f (max x y).
Proof.
 intros f Eqf Lef x y.
 destruct (M.max_spec x y) as [(H,E)|(H,E)]; rewrite E;
  destruct (M.max_spec (f x) (f y)) as [(H',E')|(H',E')]; auto.
 assert (f x <= f y) by (apply Lef; order). order.
 assert (f y <= f x) by (apply Lef; order). order.
Qed.

(** *** Semi-lattice algebraic properties of [max] *)

Lemma max_id : forall n, max n n == n.
Proof.
 intros. destruct (M.max_spec n n); intuition.
Qed.

Lemma max_assoc : forall m n p, max m (max n p) == max (max m n) p.
Proof.
 intros.
 destruct (M.max_spec n p) as [(H,Eq)|(H,Eq)]; rewrite Eq.
 destruct (M.max_spec m n) as [(H',Eq')|(H',Eq')]; rewrite Eq'.
 destruct (max_spec m p); intuition; order. order.
 destruct (M.max_spec m n) as [(H',Eq')|(H',Eq')]; rewrite Eq'. order.
 destruct (max_spec m p); intuition; order.
Qed.

Lemma max_comm : forall n m, max n m == max m n.
Proof.
 intros.
 destruct (M.max_spec n m) as [(H,Eq)|(H,Eq)]; rewrite Eq.
 destruct (M.max_spec m n) as [(H',Eq')|(H',Eq')]; rewrite Eq'; order.
 destruct (M.max_spec m n) as [(H',Eq')|(H',Eq')]; rewrite Eq'; order.
Qed.

(** *** Least-upper bound properties of [max] *)

Lemma max_l : forall n m, m <= n -> max n m == n.
Proof.
 intros. destruct (M.max_spec n m); intuition; order.
Qed.

Lemma max_r : forall n m, n <= m -> max n m == m.
Proof.
 intros. destruct (M.max_spec n m); intuition; order.
Qed.

Lemma le_max_l : forall n m, n <= max n m.
Proof.
 intros; destruct (M.max_spec n m); intuition; order.
Qed.

Lemma le_max_r : forall n m, m <= max n m.
Proof.
 intros; destruct (M.max_spec n m); intuition; order.
Qed.

Lemma max_le : forall n m p, p <= max n m -> p <= n \/ p <= m.
Proof.
 intros n m p H; destruct (M.max_spec n m);
  [right|left]; intuition; order.
Qed.

Lemma max_le_iff : forall n m p, p <= max n m <-> p <= n \/ p <= m.
Proof.
 intros. split. apply max_le.
 destruct (M.max_spec n m); intuition; order.
Qed.

Lemma max_lt_iff : forall n m p, p < max n m <-> p < n \/ p < m.
Proof.
 intros. destruct (M.max_spec n m); intuition;
  order || (right; order) || (left; order).
Qed.

Lemma max_lub_l : forall n m p, max n m <= p -> n <= p.
Proof.
 intros; destruct (M.max_spec n m); intuition; order.
Qed.

Lemma max_lub_r : forall n m p, max n m <= p -> m <= p.
Proof.
 intros; destruct (M.max_spec n m); intuition; order.
Qed.

Lemma max_lub : forall n m p, n <= p -> m <= p -> max n m <= p.
Proof.
 intros; destruct (M.max_spec n m); intuition; order.
Qed.

Lemma max_lub_iff : forall n m p, max n m <= p <-> n <= p /\ m <= p.
Proof.
 intros; destruct (M.max_spec n m); intuition; order.
Qed.

Lemma max_lub_lt : forall n m p, n < p -> m < p -> max n m < p.
Proof.
 intros; destruct (M.max_spec n m); intuition; order.
Qed.

Lemma max_lub_lt_iff : forall n m p, max n m < p <-> n < p /\ m < p.
Proof.
 intros; destruct (M.max_spec n m); intuition; order.
Qed.

Lemma max_le_compat_l : forall n m p, n <= m -> max p n <= max p m.
Proof.
 intros.
 destruct (M.max_spec p n) as [(LT,E)|(LE,E)]; rewrite E.
 assert (LE' := le_max_r p m). order.
 apply le_max_l.
Qed.

Lemma max_le_compat_r : forall n m p, n <= m -> max n p <= max m p.
Proof.
 intros. rewrite (max_comm n p), (max_comm m p).
 auto using max_le_compat_l.
Qed.

Lemma max_le_compat : forall n m p q, n <= m -> p <= q ->
 max n p <= max m q.
Proof.
 intros  n m p q Hnm Hpq.
 assert (LE := max_le_compat_l _ _ m Hpq).
 assert (LE' := max_le_compat_r _ _ p Hnm).
 order.
Qed.

End MaxProperties.


(** ** Properties concernant [min], then both [min] and [max].

   To avoid duplication of code, we exploit that [min] can be
   seen as a [max] of the reversed order.
*)

Module MinMaxProperties (Import O:OrderedTypeFull)(Import M:HasMinMax O).
 Include MaxProperties O M.

 Module ORev := OrderedTypeRev O.
 Module MRev <: HasMax ORev.
  Definition max x y := M.min y x.
  Definition max_spec x y := M.min_spec y x.
 End MRev.
 Module MPRev := MaxProperties ORev MRev.

Instance min_compat : Proper (eq==>eq==>eq) min.
Proof. intros x x' Hx y y' Hy. apply MPRev.max_compat; assumption. Qed.

Lemma min_spec : forall n m,
 (n < m /\ min n m == n) \/ (m <= n /\ min n m == m).
Proof. exact min_spec. Qed.

Lemma min_spec_le : forall n m,
 (n <= m /\ min n m == n) \/ (m <= n /\ min n m == m).
Proof. intros. exact (MPRev.max_spec_le m n). Qed.

Lemma min_case_strong : forall n m (P:O.t -> Type),
 (forall x y, x == y -> P x -> P y) ->
 (n<=m -> P n) -> (m<=n -> P m) -> P (min n m).
Proof. intros. apply (MPRev.max_case_strong m n P); auto. Qed.

Lemma min_case : forall n m (P:O.t -> Type),
  (forall x y, x == y -> P x -> P y) ->
  P n -> P m -> P (min n m).
Proof. intros. apply min_case_strong; auto. Defined.

Lemma min_dec : forall n m, {min n m == n} + {min n m == m}.
Proof.
 intros. destruct (MPRev.max_dec m n); [right|left]; assumption.
Defined.

Lemma min_monotone: forall f,
 (Proper (eq ==> eq) f) ->
 (Proper (le ==> le) f) ->
 forall x y, min (f x) (f y) == f (min x y).
Proof.
 intros. apply MPRev.max_monotone; auto. compute in *; eauto.
Qed.

Lemma min_unicity : forall n m p,
 ((n < m /\ p == n)  \/ (m <= n /\ p == m)) ->  p == min n m.
Proof. intros n m p. apply MPRev.max_unicity. Qed.

Lemma min_unicity_ext : forall f,
 (forall n m, (n < m /\ f n m == n)  \/ (m <= n /\ f n m == m)) ->
 (forall n m, f n m == min n m).
Proof. intros f H n m. apply MPRev.max_unicity, H; auto. Qed.

Lemma min_id : forall n, min n n == n.
Proof. intros. exact (MPRev.max_id n). Qed.

Lemma min_assoc : forall m n p, min m (min n p) == min (min m n) p.
Proof. intros. symmetry; apply MPRev.max_assoc. Qed.

Lemma min_comm : forall n m, min n m == min m n.
Proof. intros. exact (MPRev.max_comm m n). Qed.

Lemma min_l : forall n m, n <= m -> min n m == n.
Proof. intros n m. exact (MPRev.max_r m n). Qed.

Lemma min_r : forall n m, m <= n -> min n m == m.
Proof. intros n m. exact (MPRev.max_l m n). Qed.

Lemma le_min_r : forall n m, min n m <= m.
Proof. intros. exact (MPRev.le_max_l m n). Qed.

Lemma le_min_l : forall n m, min n m <= n.
Proof. intros. exact (MPRev.le_max_r m n). Qed.

Lemma min_le : forall n m p, min n m <= p -> n <= p \/ m <= p.
Proof. intros n m p H. destruct (MPRev.max_le _ _ _ H); auto. Qed.

Lemma min_le_iff : forall n m p, min n m <= p <-> n <= p \/ m <= p.
Proof. intros n m p. rewrite (MPRev.max_le_iff m n p); intuition. Qed.

Lemma min_lt_iff : forall n m p, min n m < p <-> n < p \/ m < p.
Proof. intros n m p. rewrite (MPRev.max_lt_iff m n p); intuition. Qed.

Lemma min_glb_l : forall n m p, p <= min n m -> p <= n.
Proof. intros n m. exact (MPRev.max_lub_r m n). Qed.

Lemma min_glb_r : forall n m p, p <= min n m -> p <= m.
Proof. intros n m. exact (MPRev.max_lub_l m n). Qed.

Lemma min_glb : forall n m p, p <= n -> p <= m -> p <= min n m.
Proof. intros. apply MPRev.max_lub; auto. Qed.

Lemma min_glb_iff : forall n m p, p <= min n m <-> p <= n /\ p <= m.
Proof. intros. rewrite (MPRev.max_lub_iff m n p); intuition. Qed.

Lemma min_glb_lt : forall n m p, p < n -> p < m -> p < min n m.
Proof. intros. apply MPRev.max_lub_lt; auto. Qed.

Lemma min_glb_lt_iff : forall n m p, p < min n m <-> p < n /\ p < m.
Proof. intros. rewrite (MPRev.max_lub_lt_iff m n p); intuition. Qed.

Lemma min_le_compat_l : forall n m p, n <= m -> min p n <= min p m.
Proof. intros n m. exact (MPRev.max_le_compat_r m n). Qed.

Lemma min_le_compat_r : forall n m p, n <= m -> min n p <= min m p.
Proof. intros n m. exact (MPRev.max_le_compat_l m n). Qed.

Lemma min_le_compat : forall n m p q, n <= m -> p <= q ->
 min n p <= min m q.
Proof. intros. apply MPRev.max_le_compat; auto. Qed.


(** *** Combined properties of min and max *)

Lemma min_max_absorption : forall n m, max n (min n m) == n.
Proof.
 intros.
 destruct (M.min_spec n m) as [(C,E)|(C,E)]; rewrite E.
 apply max_l. OF.order.
 destruct (M.max_spec n m); intuition; OF.order.
Qed.

Lemma max_min_absorption : forall n m, min n (max n m) == n.
Proof.
 intros.
 destruct (M.max_spec n m) as [(C,E)|(C,E)]; rewrite E.
 destruct (M.min_spec n m) as [(C',E')|(C',E')]; auto. OF.order.
 apply min_l; auto. OF.order.
Qed.

(** Distributivity *)

Lemma max_min_distr : forall n m p,
 max n (min m p) == min (max n m) (max n p).
Proof.
 intros. symmetry. apply min_monotone.
 eauto with *.
 repeat red; intros. apply max_le_compat_l; auto.
Qed.

Lemma min_max_distr : forall n m p,
 min n (max m p) == max (min n m) (min n p).
Proof.
 intros. symmetry. apply max_monotone.
 eauto with *.
 repeat red; intros. apply min_le_compat_l; auto.
Qed.

(** Modularity *)

Lemma max_min_modular : forall n m p,
 max n (min m (max n p)) == min (max n m) (max n p).
Proof.
 intros. rewrite <- max_min_distr.
 destruct (max_spec n p) as [(C,E)|(C,E)]; rewrite E. reflexivity.
 destruct (min_spec m n) as [(C',E')|(C',E')]; rewrite E'.
 rewrite 2 max_l; try OF.order. rewrite min_le_iff; auto.
 rewrite 2 max_l; try OF.order. rewrite min_le_iff; auto.
Qed.

Lemma min_max_modular : forall n m p,
 min n (max m (min n p)) == max (min n m) (min n p).
Proof.
 intros. rewrite <- min_max_distr.
 destruct (min_spec n p) as [(C,E)|(C,E)]; rewrite E.
 destruct (max_spec m n) as [(C',E')|(C',E')]; rewrite E'.
 rewrite 2 min_l; try OF.order. rewrite max_le_iff; right; OF.order.
 rewrite 2 min_l; try OF.order. rewrite max_le_iff; auto. reflexivity.
Qed.

(** Disassociativity *)

Lemma max_min_disassoc : forall n m p,
 min n (max m p) <= max (min n m) p.
Proof.
 intros. rewrite min_max_distr.
 auto using max_le_compat_l, le_min_r.
Qed.

(** Anti-monotonicity swaps the role of [min] and [max] *)

Lemma max_min_antimonotone : forall f,
 Proper (eq==>eq) f ->
 Proper (le==>inverse le) f ->
 forall x y, max (f x) (f y) == f (min x y).
Proof.
 intros f Eqf Lef x y.
 destruct (M.min_spec x y) as [(H,E)|(H,E)]; rewrite E;
  destruct (M.max_spec (f x) (f y)) as [(H',E')|(H',E')]; auto.
 assert (f y <= f x) by (apply Lef; OF.order). OF.order.
 assert (f x <= f y) by (apply Lef; OF.order). OF.order.
Qed.


Lemma min_max_antimonotone : forall f,
 Proper (eq==>eq) f ->
 Proper (le==>inverse le) f ->
 forall x y, min (f x) (f y) == f (max x y).
Proof.
 intros f Eqf Lef x y.
 destruct (M.max_spec x y) as [(H,E)|(H,E)]; rewrite E;
  destruct (M.min_spec (f x) (f y)) as [(H',E')|(H',E')]; auto.
 assert (f y <= f x) by (apply Lef; OF.order). OF.order.
 assert (f x <= f y) by (apply Lef; OF.order). OF.order.
Qed.

End MinMaxProperties.



(** TODO: Some Remaining questions...

--> Compare with a type-classes version ?

--> Is max_unicity and max_unicity_ext really convenient to express
    that any possible definition of max will in fact be equivalent ?

--> Is it possible to avoid copy-paste about min even more ?

*)
