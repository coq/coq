(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Compatibility functors between FSetInterface and MSetInterface. *)

Require Import FSetInterface FSetFacts MSetInterface MSetFacts.
Set Implicit Arguments.
Unset Strict Implicit.

(** * From new Weak Sets to old ones *)

Module Backport_WSets
 (E:DecidableType.DecidableType)
 (M:MSetInterface.WSets with Definition E.t := E.t
                        with Definition E.eq := E.eq)
 <: FSetInterface.WSfun E.

 Definition elt := E.t.
 Definition t := M.t.

 Implicit Type s : t.
 Implicit Type x y : elt.
 Implicit Type f : elt -> bool.

 Definition In : elt -> t -> Prop := M.In.
 Definition Equal s s' := forall a : elt, In a s <-> In a s'.
 Definition Subset s s' := forall a : elt, In a s -> In a s'.
 Definition Empty s := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.
 Definition empty : t := M.empty.
 Definition is_empty : t -> bool := M.is_empty.
 Definition mem : elt -> t -> bool := M.mem.
 Definition add : elt -> t -> t := M.add.
 Definition singleton : elt -> t := M.singleton.
 Definition remove : elt -> t -> t := M.remove.
 Definition union : t -> t -> t := M.union.
 Definition inter : t -> t -> t := M.inter.
 Definition diff : t -> t -> t := M.diff.
 Definition eq : t -> t -> Prop := M.eq.
 Definition eq_dec : forall s s', {eq s s'}+{~eq s s'}:= M.eq_dec.
 Definition equal : t -> t -> bool := M.equal.
 Definition subset : t -> t -> bool := M.subset.
 Definition fold : forall A : Type, (elt -> A -> A) -> t -> A -> A := M.fold.
 Definition for_all : (elt -> bool) -> t -> bool := M.for_all.
 Definition exists_ : (elt -> bool) -> t -> bool := M.exists_.
 Definition filter : (elt -> bool) -> t -> t := M.filter.
 Definition partition : (elt -> bool) -> t -> t * t:= M.partition.
 Definition cardinal : t -> nat := M.cardinal.
 Definition elements : t -> list elt := M.elements.
 Definition choose : t -> option elt := M.choose.

 Module MF := MSetFacts.WFacts M.

 Definition In_1 : forall s x y, E.eq x y -> In x s -> In y s
  := MF.In_1.
 Definition eq_refl : forall s, eq s s
  := @Equivalence_Reflexive _ _ M.eq_equiv.
 Definition eq_sym : forall s s', eq s s' -> eq s' s
  := @Equivalence_Symmetric _ _ M.eq_equiv.
 Definition eq_trans : forall s s' s'', eq s s' -> eq s' s'' -> eq s s''
  := @Equivalence_Transitive _ _ M.eq_equiv.
 Definition mem_1 : forall s x, In x s -> mem x s = true
  := MF.mem_1.
 Definition mem_2 : forall s x, mem x s = true -> In x s
  := MF.mem_2.
 Definition equal_1 : forall s s', Equal s s' -> equal s s' = true
  := MF.equal_1.
 Definition equal_2 : forall s s', equal s s' = true -> Equal s s'
  := MF.equal_2.
 Definition subset_1 : forall s s', Subset s s' -> subset s s' = true
  := MF.subset_1.
 Definition subset_2 : forall s s', subset s s' = true -> Subset s s'
  := MF.subset_2.
 Definition empty_1 : Empty empty := MF.empty_1.
 Definition is_empty_1 : forall s, Empty s -> is_empty s = true
  := MF.is_empty_1.
 Definition is_empty_2 : forall s, is_empty s = true -> Empty s
  := MF.is_empty_2.
 Definition add_1 : forall s x y, E.eq x y -> In y (add x s)
  := MF.add_1.
 Definition add_2 : forall s x y, In y s -> In y (add x s)
  := MF.add_2.
 Definition add_3 : forall s x y, ~ E.eq x y -> In y (add x s) -> In y s
  := MF.add_3.
 Definition remove_1 : forall s x y, E.eq x y -> ~ In y (remove x s)
  := MF.remove_1.
 Definition remove_2 : forall s x y, ~ E.eq x y -> In y s -> In y (remove x s)
  := MF.remove_2.
 Definition remove_3 : forall s x y, In y (remove x s) -> In y s
  := MF.remove_3.
 Definition union_1 : forall s s' x, In x (union s s') -> In x s \/ In x s'
  := MF.union_1.
 Definition union_2 : forall s s' x, In x s -> In x (union s s')
  := MF.union_2.
 Definition union_3 : forall s s' x, In x s' -> In x (union s s')
  := MF.union_3.
 Definition inter_1 : forall s s' x, In x (inter s s') -> In x s
  := MF.inter_1.
 Definition inter_2 : forall s s' x, In x (inter s s') -> In x s'
  := MF.inter_2.
 Definition inter_3 : forall s s' x, In x s -> In x s' -> In x (inter s s')
  := MF.inter_3.
 Definition diff_1 : forall s s' x, In x (diff s s') -> In x s
  := MF.diff_1.
 Definition diff_2 : forall s s' x, In x (diff s s') -> ~ In x s'
  := MF.diff_2.
 Definition diff_3 : forall s s' x, In x s -> ~ In x s' -> In x (diff s s')
  := MF.diff_3.
 Definition singleton_1 : forall x y, In y (singleton x) -> E.eq x y
  := MF.singleton_1.
 Definition singleton_2 : forall x y, E.eq x y -> In y (singleton x)
  := MF.singleton_2.
 Definition fold_1 : forall s (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (fun a e => f e a) (elements s) i
  := MF.fold_1.
 Definition cardinal_1 : forall s, cardinal s = length (elements s)
  := MF.cardinal_1.
 Definition filter_1 : forall s x f, compat_bool E.eq f ->
  In x (filter f s) -> In x s
  := MF.filter_1.
 Definition filter_2 : forall s x f, compat_bool E.eq f ->
  In x (filter f s) -> f x = true
  := MF.filter_2.
 Definition filter_3 : forall s x f, compat_bool E.eq f ->
  In x s -> f x = true -> In x (filter f s)
  := MF.filter_3.
 Definition for_all_1 : forall s f, compat_bool E.eq f ->
  For_all (fun x => f x = true) s -> for_all f s = true
  := MF.for_all_1.
 Definition for_all_2 : forall s f, compat_bool E.eq f ->
  for_all f s = true -> For_all (fun x => f x = true) s
  := MF.for_all_2.
 Definition exists_1 : forall s f, compat_bool E.eq f ->
  Exists (fun x => f x = true) s -> exists_ f s = true
  := MF.exists_1.
 Definition exists_2 : forall s f, compat_bool E.eq f ->
  exists_ f s = true -> Exists (fun x => f x = true) s
  := MF.exists_2.
 Definition partition_1 : forall s f, compat_bool E.eq f ->
  Equal (fst (partition f s)) (filter f s)
  := MF.partition_1.
 Definition partition_2 : forall s f, compat_bool E.eq f ->
  Equal (snd (partition f s)) (filter (fun x => negb (f x)) s)
  := MF.partition_2.
 Definition choose_1 : forall s x, choose s = Some x -> In x s
  := MF.choose_1.
 Definition choose_2 : forall s, choose s = None -> Empty s
  := MF.choose_2.
 Definition elements_1 : forall s x, In x s -> InA E.eq x (elements s)
  := MF.elements_1.
 Definition elements_2 : forall s x, InA E.eq x (elements s) -> In x s
  := MF.elements_2.
 Definition elements_3w : forall s, NoDupA E.eq (elements s)
  := MF.elements_3w.

End Backport_WSets.


(** * From new Sets to new ones *)

Module Backport_Sets
 (O:OrderedType.OrderedType)
 (M:MSetInterface.Sets with Definition E.t := O.t
                       with Definition E.eq := O.eq
                       with Definition E.lt := O.lt)
 <: FSetInterface.S with Module E:=O.

  Include Backport_WSets O M.

  Implicit Type s : t.
  Implicit Type x y : elt.

  Definition lt : t -> t -> Prop := M.lt.
  Definition min_elt : t -> option elt := M.min_elt.
  Definition max_elt : t -> option elt := M.max_elt.
  Definition min_elt_1 : forall s x, min_elt s = Some x -> In x s
   := M.min_elt_spec1.
  Definition min_elt_2 : forall s x y,
   min_elt s = Some x -> In y s -> ~ O.lt y x
   := M.min_elt_spec2.
  Definition min_elt_3 : forall s, min_elt s = None -> Empty s
   := M.min_elt_spec3.
  Definition max_elt_1 : forall s x, max_elt s = Some x -> In x s
   := M.max_elt_spec1.
  Definition max_elt_2 : forall s x y,
   max_elt s = Some x -> In y s -> ~ O.lt x y
   := M.max_elt_spec2.
  Definition max_elt_3 : forall s, max_elt s = None -> Empty s
   := M.max_elt_spec3.
  Definition elements_3 : forall s, sort O.lt (elements s)
   := M.elements_spec2.
  Definition choose_3 : forall s s' x y,
   choose s = Some x -> choose s' = Some y -> Equal s s' -> O.eq x y
   := M.choose_spec3.
  Definition lt_trans : forall s s' s'', lt s s' -> lt s' s'' -> lt s s''
   := @StrictOrder_Transitive _ _ M.lt_strorder.
  Lemma lt_not_eq : forall s s',  lt s s' -> ~ eq s s'.
  Proof.
   unfold lt, eq. intros s s' Hlt Heq. rewrite Heq in Hlt.
   apply (StrictOrder_Irreflexive s'); auto.
  Qed.
  Definition compare : forall s s', Compare lt eq s s'.
  Proof.
   intros s s'; destruct (CompSpec2Type (M.compare_spec s s'));
    [ apply EQ | apply LT | apply GT ]; auto.
  Defined.

  Module E := O.

End Backport_Sets.


(** * From old Weak Sets to new ones. *)

Module Update_WSets
 (E:Equalities.DecidableType)
 (M:FSetInterface.WS with Definition E.t := E.t
                     with Definition E.eq := E.eq)
 <: MSetInterface.WSetsOn E.

 Definition elt := E.t.
 Definition t := M.t.

 Implicit Type s : t.
 Implicit Type x y : elt.
 Implicit Type f : elt -> bool.

 Definition In : elt -> t -> Prop := M.In.
 Definition Equal s s' := forall a : elt, In a s <-> In a s'.
 Definition Subset s s' := forall a : elt, In a s -> In a s'.
 Definition Empty s := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.
 Definition empty : t := M.empty.
 Definition is_empty : t -> bool := M.is_empty.
 Definition mem : elt -> t -> bool := M.mem.
 Definition add : elt -> t -> t := M.add.
 Definition singleton : elt -> t := M.singleton.
 Definition remove : elt -> t -> t := M.remove.
 Definition union : t -> t -> t := M.union.
 Definition inter : t -> t -> t := M.inter.
 Definition diff : t -> t -> t := M.diff.
 Definition eq : t -> t -> Prop := M.eq.
 Definition eq_dec : forall s s', {eq s s'}+{~eq s s'}:= M.eq_dec.
 Definition equal : t -> t -> bool := M.equal.
 Definition subset : t -> t -> bool := M.subset.
 Definition fold : forall A : Type, (elt -> A -> A) -> t -> A -> A := M.fold.
 Definition for_all : (elt -> bool) -> t -> bool := M.for_all.
 Definition exists_ : (elt -> bool) -> t -> bool := M.exists_.
 Definition filter : (elt -> bool) -> t -> t := M.filter.
 Definition partition : (elt -> bool) -> t -> t * t:= M.partition.
 Definition cardinal : t -> nat := M.cardinal.
 Definition elements : t -> list elt := M.elements.
 Definition choose : t -> option elt := M.choose.

 Module MF := FSetFacts.WFacts M.

 Instance In_compat : Proper (E.eq==>Logic.eq==>iff) In.
 Proof. intros x x' Hx s s' Hs. subst. apply MF.In_eq_iff; auto. Qed.

 Instance eq_equiv : Equivalence eq := _.

 Section Spec.
  Variable s s': t.
  Variable x y : elt.

  Lemma mem_spec : mem x s = true <-> In x s.
  Proof. intros; symmetry; apply MF.mem_iff. Qed.

  Lemma equal_spec : equal s s' = true <-> Equal s s'.
  Proof. intros; symmetry; apply MF.equal_iff. Qed.

  Lemma subset_spec : subset s s' = true <-> Subset s s'.
  Proof. intros; symmetry; apply MF.subset_iff. Qed.

  Definition empty_spec : Empty empty := M.empty_1.

  Lemma is_empty_spec : is_empty s = true <-> Empty s.
  Proof. intros; symmetry; apply MF.is_empty_iff. Qed.
  
  Declare Equivalent Keys In M.In.

  Lemma add_spec : In y (add x s) <-> E.eq y x \/ In y s.
  Proof. intros. rewrite MF.add_iff. intuition. Qed.

  Lemma remove_spec : In y (remove x s) <-> In y s /\ ~E.eq y x.
  Proof. intros. rewrite MF.remove_iff. intuition. Qed.

  Lemma singleton_spec : In y (singleton x) <-> E.eq y x.
  Proof. intros; rewrite MF.singleton_iff. intuition. Qed.

  Definition union_spec : In x (union s s') <-> In x s \/ In x s'
   := @MF.union_iff s s' x.
  Definition inter_spec : In x (inter s s') <-> In x s /\ In x s'
   := @MF.inter_iff s s' x.
  Definition diff_spec : In x (diff s s') <-> In x s /\ ~In x s'
   := @MF.diff_iff s s' x.
  Definition fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (flip f) (elements s) i
   := @M.fold_1 s.
  Definition cardinal_spec : cardinal s = length (elements s)
   := @M.cardinal_1 s.

  Lemma elements_spec1 : InA E.eq x (elements s) <-> In x s.
  Proof. intros; symmetry; apply MF.elements_iff. Qed.

  Definition elements_spec2w : NoDupA E.eq (elements s)
   := @M.elements_3w s.
  Definition choose_spec1 : choose s = Some x -> In x s
   := @M.choose_1 s x.
  Definition choose_spec2 : choose s = None -> Empty s
   := @M.choose_2 s.
  Definition filter_spec : forall f, Proper (E.eq==>Logic.eq) f ->
   (In x (filter f s) <-> In x s /\ f x = true)
   := @MF.filter_iff s x.
  Definition partition_spec1 : forall f, Proper (E.eq==>Logic.eq) f ->
   Equal (fst (partition f s)) (filter f s)
   := @M.partition_1 s.
  Definition partition_spec2 : forall f, Proper (E.eq==>Logic.eq) f ->
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s)
   := @M.partition_2 s.

  Lemma for_all_spec : forall f, Proper (E.eq==>Logic.eq) f ->
    (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof. intros; symmetry; apply MF.for_all_iff; auto. Qed.

  Lemma exists_spec : forall f, Proper (E.eq==>Logic.eq) f ->
    (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof. intros; symmetry; apply MF.exists_iff; auto. Qed.

  End Spec.

End Update_WSets.


(** * From old Sets to new ones. *)

Module Update_Sets
 (O:Orders.OrderedType)
 (M:FSetInterface.S with Definition E.t := O.t
                    with Definition E.eq := O.eq
                    with Definition E.lt := O.lt)
 <: MSetInterface.Sets with Module E:=O.

  Include Update_WSets O M.

  Implicit Type s : t.
  Implicit Type x y : elt.

  Definition lt : t -> t -> Prop := M.lt.
  Definition min_elt : t -> option elt := M.min_elt.
  Definition max_elt : t -> option elt := M.max_elt.
  Definition min_elt_spec1 : forall s x, min_elt s = Some x -> In x s
   := M.min_elt_1.
  Definition min_elt_spec2 : forall s x y,
   min_elt s = Some x -> In y s -> ~ O.lt y x
   := M.min_elt_2.
  Definition min_elt_spec3 : forall s, min_elt s = None -> Empty s
   := M.min_elt_3.
  Definition max_elt_spec1 : forall s x, max_elt s = Some x -> In x s
   := M.max_elt_1.
  Definition max_elt_spec2 : forall s x y,
   max_elt s = Some x -> In y s -> ~ O.lt x y
   := M.max_elt_2.
  Definition max_elt_spec3 : forall s, max_elt s = None -> Empty s
   := M.max_elt_3.
  Definition elements_spec2 : forall s, sort O.lt (elements s)
   := M.elements_3.
  Definition choose_spec3 : forall s s' x y,
   choose s = Some x -> choose s' = Some y -> Equal s s' -> O.eq x y
   := M.choose_3.

  Instance lt_strorder : StrictOrder lt.
  Proof.
   split.
   intros x Hx. apply (M.lt_not_eq Hx); auto with *.
   exact M.lt_trans.
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  apply proper_sym_impl_iff_2; auto with *.
  intros s s' Hs u u' Hu H.
  assert (H0 : lt s' u).
   destruct (M.compare s' u) as [H'|H'|H']; auto.
   elim (M.lt_not_eq H). transitivity s'; auto with *.
   elim (M.lt_not_eq (M.lt_trans H H')); auto.
  destruct (M.compare s' u') as [H'|H'|H']; auto.
  elim (M.lt_not_eq H).
   transitivity u'; auto with *. transitivity s'; auto with *.
  elim (M.lt_not_eq (M.lt_trans H' H0)); auto with *.
  Qed.

  Definition compare s s' :=
   match M.compare s s' with
    | EQ _ => Eq
    | LT _ => Lt
    | GT _ => Gt
   end.

  Lemma compare_spec : forall s s', CompSpec eq lt s s' (compare s s').
  Proof. intros; unfold compare; destruct M.compare; auto. Qed.

  Module E := O.

End Update_Sets.
