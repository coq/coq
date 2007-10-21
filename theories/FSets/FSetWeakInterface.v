(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * Finite sets library *)

(** Set interfaces for types with only a decidable equality, but no ordering *)

Require Export Bool DecidableType.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Non-dependent signature

    Signature [S] presents sets as purely informative programs 
    together with axioms *)

Module Type S.

  Declare Module E : DecidableType.
  Definition elt := E.t.

  Parameter t : Set. (** the abstract type of sets *)

  (** Logical predicates *)
  Parameter In : elt -> t -> Prop.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.
  
  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).

  Parameter empty : t.
  (** The empty set. *)

  Parameter is_empty : t -> bool.
  (** Test whether a set is empty or not. *)

  Parameter mem : elt -> t -> bool.
  (** [mem x s] tests whether [x] belongs to the set [s]. *)

  Parameter add : elt -> t -> t.
  (** [add x s] returns a set containing all elements of [s],
  plus [x]. If [x] was already in [s], [s] is returned unchanged. *)

  Parameter singleton : elt -> t.
  (** [singleton x] returns the one-element set containing only [x]. *)

  Parameter remove : elt -> t -> t.
  (** [remove x s] returns a set containing all elements of [s],
  except [x]. If [x] was not in [s], [s] is returned unchanged. *)

  Parameter union : t -> t -> t.
  (** Set union. *)

  Parameter inter : t -> t -> t.
  (** Set intersection. *)

  Parameter diff : t -> t -> t.
  (** Set difference. *)

  Parameter equal : t -> t -> bool.
  (** [equal s1 s2] tests whether the sets [s1] and [s2] are
  equal, that is, contain equal elements. *)

  Parameter subset : t -> t -> bool.
  (** [subset s1 s2] tests whether the set [s1] is a subset of
  the set [s2]. *)

  (** Coq comment: [iter] is useless in a purely functional world *)
  (**  iter: (elt -> unit) -> set -> unit. i*)
  (** [iter f s] applies [f] in turn to all elements of [s].
  The order in which the elements of [s] are presented to [f]
  is unspecified. *)

  Parameter fold : forall A : Type, (elt -> A -> A) -> t -> A -> A.
  (** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)],
  where [x1 ... xN] are the elements of [s].
  The order in which elements of [s] are presented to [f] is
  unspecified. *)

  Parameter for_all : (elt -> bool) -> t -> bool.
  (** [for_all p s] checks if all elements of the set
  satisfy the predicate [p]. *)

  Parameter exists_ : (elt -> bool) -> t -> bool.
  (** [exists p s] checks if at least one element of
  the set satisfies the predicate [p]. *)

  Parameter filter : (elt -> bool) -> t -> t.
  (** [filter p s] returns the set of all elements in [s]
  that satisfy predicate [p]. *)

  Parameter partition : (elt -> bool) -> t -> t * t.
  (** [partition p s] returns a pair of sets [(s1, s2)], where
  [s1] is the set of all the elements of [s] that satisfy the
  predicate [p], and [s2] is the set of all the elements of
  [s] that do not satisfy [p]. *)

  Parameter cardinal : t -> nat.
  (** Return the number of elements of a set. *)
  (** Coq comment: nat instead of int ... *)

  Parameter elements : t -> list elt.
  (** Return the list of all elements of the given set, in any order. *)

  Parameter choose : t -> option elt.
  (** Return one element of the given set, or raise [Not_found] if
  the set is empty. Which element is chosen is unspecified.
  Equal sets could return different elements. *)
  (** Coq comment: [Not_found] is represented by the option type *)

  Section Spec. 

  Variable s s' : t.
  Variable x y : elt.

  (** Specification of [In] *)
  Parameter In_1 : E.eq x y -> In x s -> In y s.
 
  (** Specification of [mem] *)
  Parameter mem_1 : In x s -> mem x s = true.
  Parameter mem_2 : mem x s = true -> In x s. 
 
  (** Specification of [equal] *) 
  Parameter equal_1 : Equal s s' -> equal s s' = true.
  Parameter equal_2 : equal s s' = true -> Equal s s'.

  (** Specification of [subset] *)
  Parameter subset_1 : Subset s s' -> subset s s' = true.
  Parameter subset_2 : subset s s' = true -> Subset s s'.

  (** Specification of [empty] *)
  Parameter empty_1 : Empty empty.

  (** Specification of [is_empty] *)
  Parameter is_empty_1 : Empty s -> is_empty s = true. 
  Parameter is_empty_2 : is_empty s = true -> Empty s.
 
  (** Specification of [add] *)
  Parameter add_1 : E.eq x y -> In y (add x s).
  Parameter add_2 : In y s -> In y (add x s).
  Parameter add_3 : ~ E.eq x y -> In y (add x s) -> In y s. 

  (** Specification of [remove] *)
  Parameter remove_1 : E.eq x y -> ~ In y (remove x s).
  Parameter remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
  Parameter remove_3 : In y (remove x s) -> In y s.

  (** Specification of [singleton] *)
  Parameter singleton_1 : In y (singleton x) -> E.eq x y. 
  Parameter singleton_2 : E.eq x y -> In y (singleton x). 

  (** Specification of [union] *)
  Parameter union_1 : In x (union s s') -> In x s \/ In x s'.
  Parameter union_2 : In x s -> In x (union s s'). 
  Parameter union_3 : In x s' -> In x (union s s').

  (** Specification of [inter] *)
  Parameter inter_1 : In x (inter s s') -> In x s.
  Parameter inter_2 : In x (inter s s') -> In x s'.
  Parameter inter_3 : In x s -> In x s' -> In x (inter s s').

  (** Specification of [diff] *)
  Parameter diff_1 : In x (diff s s') -> In x s. 
  Parameter diff_2 : In x (diff s s') -> ~ In x s'.
  Parameter diff_3 : In x s -> ~ In x s' -> In x (diff s s').
 
  (** Specification of [fold] *)  
  Parameter fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.

  (** Specification of [cardinal] *)  
  Parameter cardinal_1 : cardinal s = length (elements s).

  Section Filter.
  
  Variable f : elt -> bool.

  (** Specification of [filter] *)
  Parameter filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s. 
  Parameter filter_2 : compat_bool E.eq f -> In x (filter f s) -> f x = true. 
  Parameter filter_3 :
      compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).

  (** Specification of [for_all] *)
  Parameter for_all_1 :
      compat_bool E.eq f ->
      For_all (fun x => f x = true) s -> for_all f s = true.
  Parameter for_all_2 :
      compat_bool E.eq f ->
      for_all f s = true -> For_all (fun x => f x = true) s.

  (** Specification of [exists] *)
  Parameter exists_1 :
      compat_bool E.eq f ->
      Exists (fun x => f x = true) s -> exists_ f s = true.
  Parameter exists_2 :
      compat_bool E.eq f ->
      exists_ f s = true -> Exists (fun x => f x = true) s.

  (** Specification of [partition] *)
  Parameter partition_1 :
      compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
  Parameter partition_2 :
      compat_bool E.eq f ->
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).

  End Filter.

  (** Specification of [elements] *)
  Parameter elements_1 : In x s -> InA E.eq x (elements s).
  Parameter elements_2 : InA E.eq x (elements s) -> In x s.
  Parameter elements_3 : NoDupA E.eq (elements s).

  (** Specification of [choose] *)
  Parameter choose_1 : choose s = Some x -> In x s.
  Parameter choose_2 : choose s = None -> Empty s.

  End Spec.

  Hint Resolve mem_1 equal_1 subset_1 empty_1
    is_empty_1 choose_1 choose_2 add_1 add_2 remove_1
    remove_2 singleton_2 union_1 union_2 union_3
    inter_3 diff_3 fold_1 filter_3 for_all_1 exists_1
    partition_1 partition_2 elements_1 elements_3 
    : set.
  Hint Immediate In_1 mem_2 equal_2 subset_2 is_empty_2 add_3
    remove_3 singleton_1 inter_1 inter_2 diff_1 diff_2
    filter_1 filter_2 for_all_2 exists_2 elements_2 
    : set.
  (* for compatibility with earlier hints *)
  Hint Resolve In_1 mem_2 equal_2 subset_2 is_empty_2 add_3
    remove_3 singleton_1 inter_1 inter_2 diff_1 diff_2
    filter_1 filter_2 for_all_2 exists_2 elements_2 
    : oldset.


End S.
