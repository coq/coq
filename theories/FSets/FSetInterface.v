(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite set library *)

(** Set interfaces, inspired by the one of Ocaml. When compared with
    Ocaml, the main differences are:
    - the lack of [iter] function, useless since Coq is purely functional
    - the use of [option] types instead of [Not_found] exceptions
    - the use of [nat] instead of [int] for the [cardinal] function

    Several variants of the set interfaces are available:
    - [WSfun] : functorial signature for weak sets, non-dependent style
    - [WS]    : self-contained version of [WSfun]
    - [Sfun]  : functorial signature for ordered sets, non-dependent style
    - [S]     : self-contained version of [Sfun]
    - [Sdep]  : analog of [S] written using dependent style

    If unsure, [S] is probably what you're looking for: other signatures
    are subsets of it, apart from [Sdep] which is isomorphic to [S] (see
    [FSetBridge]).
*)

Require Export Bool OrderedType DecidableType.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Non-dependent signatures

    The following signatures presents sets as purely informative
    programs together with axioms *)



(** ** Functorial signature for weak sets

    Weak sets are sets without ordering on base elements, only
    a decidable equality. *)

Module Type WSfun (E : DecidableType).

  Definition elt := E.t.

  Parameter t : Type. (** the abstract type of sets *)

  (** Logical predicates *)
  Parameter In : elt -> t -> Prop.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Notation "s  [=]  t" := (Equal s t) (at level 70, no associativity).
  Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

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

  Definition eq : t -> t -> Prop := Equal.

  Parameter eq_dec : forall s s', { eq s s' } + { ~ eq s s' }.

  Parameter equal : t -> t -> bool.
  (** [equal s1 s2] tests whether the sets [s1] and [s2] are
  equal, that is, contain equal elements. *)

  Parameter subset : t -> t -> bool.
  (** [subset s1 s2] tests whether the set [s1] is a subset of
  the set [s2]. *)

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

  Parameter elements : t -> list elt.
  (** Return the list of all elements of the given set, in any order. *)

  Parameter choose : t -> option elt.
  (** Return one element of the given set, or [None] if
  the set is empty. Which element is chosen is unspecified.
  Equal sets could return different elements. *)

  Section Spec.

  Variable s s' s'': t.
  Variable x y : elt.

  (** Specification of [In] *)
  Parameter In_1 : E.eq x y -> In x s -> In y s.

  (** Specification of [eq] *)
  Parameter eq_refl : eq s s.
  Parameter eq_sym : eq s s' -> eq s' s.
  Parameter eq_trans : eq s s' -> eq s' s'' -> eq s s''.

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
  (** When compared with ordered sets, here comes the only
      property that is really weaker: *)
  Parameter elements_3w : NoDupA E.eq (elements s).

  (** Specification of [choose] *)
  Parameter choose_1 : choose s = Some x -> In x s.
  Parameter choose_2 : choose s = None -> Empty s.

  End Spec.

  Hint Transparent elt.
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

End WSfun.



(** ** Static signature for weak sets

    Similar to the functorial signature [SW], except that the
    module [E] of base elements is incorporated in the signature. *)

Module Type WS.
  Declare Module E : DecidableType.
  Include WSfun E.
End WS.



(** ** Functorial signature for sets on ordered elements

    Based on [WSfun], plus ordering on sets and [min_elt] and [max_elt]
    and some stronger specifications for other functions. *)

Module Type Sfun (E : OrderedType).
  Include WSfun E.

  Parameter lt : t -> t -> Prop.
  Parameter compare : forall s s' : t, Compare lt eq s s'.
  (** Total ordering between sets. Can be used as the ordering function
  for doing sets of sets. *)

  Parameter min_elt : t -> option elt.
  (** Return the smallest element of the given set
  (with respect to the [E.compare] ordering),
  or [None] if the set is empty. *)

  Parameter max_elt : t -> option elt.
  (** Same as [min_elt], but returns the largest element of the
  given set. *)

  Section Spec.

  Variable s s' s'' : t.
  Variable x y : elt.

  (** Specification of [lt] *)
  Parameter lt_trans : lt s s' -> lt s' s'' -> lt s s''.
  Parameter lt_not_eq : lt s s' -> ~ eq s s'.

  (** Additional specification of [elements] *)
  Parameter elements_3 : sort E.lt (elements s).

  (** Remark: since [fold] is specified via [elements], this stronger
   specification of [elements] has an indirect impact on [fold],
   which can now be proved to receive elements in increasing order.
  *)

  (** Specification of [min_elt] *)
  Parameter min_elt_1 : min_elt s = Some x -> In x s.
  Parameter min_elt_2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
  Parameter min_elt_3 : min_elt s = None -> Empty s.

  (** Specification of [max_elt] *)
  Parameter max_elt_1 : max_elt s = Some x -> In x s.
  Parameter max_elt_2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
  Parameter max_elt_3 : max_elt s = None -> Empty s.

  (** Additional specification of [choose] *)
  Parameter choose_3 : choose s = Some x -> choose s' = Some y ->
    Equal s s' -> E.eq x y.

  End Spec.

  Hint Resolve elements_3 : set.
  Hint Immediate
    min_elt_1 min_elt_2 min_elt_3 max_elt_1 max_elt_2 max_elt_3 : set.

End Sfun.


(** ** Static signature for sets on ordered elements

    Similar to the functorial signature [Sfun], except that the
    module [E] of base elements is incorporated in the signature. *)

Module Type S.
  Declare Module E : OrderedType.
  Include Sfun E.
End S.


(** ** Some subtyping tests
<<
WSfun ---> WS
 |         |
 |         |
 V         V
Sfun  ---> S

Module S_WS (M : S) <: WS := M.
Module Sfun_WSfun (E:OrderedType)(M : Sfun E) <: WSfun E := M.
Module S_Sfun (M : S) <: Sfun M.E := M.
Module WS_WSfun (M : WS) <: WSfun M.E := M.
>>
*)

(** * Dependent signature

    Signature [Sdep] presents ordered sets using dependent types *)

Module Type Sdep.

  Declare Module E : OrderedType.
  Definition elt := E.t.

  Parameter t : Type.

  Parameter In : elt -> t -> Prop.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Add x s s' := forall y, In y s' <-> E.eq x y \/ In y s.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).

  Definition eq : t -> t -> Prop := Equal.
  Parameter lt : t -> t -> Prop.
  Parameter compare : forall s s' : t, Compare lt eq s s'.

  Parameter eq_refl : forall s : t, eq s s.
  Parameter eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Parameter eq_trans : forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Parameter lt_trans : forall s s' s'' : t, lt s s' -> lt s' s'' -> lt s s''.
  Parameter lt_not_eq : forall s s' : t, lt s s' -> ~ eq s s'.

  Parameter eq_In : forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.

  Parameter empty : {s : t | Empty s}.

  Parameter is_empty : forall s : t, {Empty s} + {~ Empty s}.

  Parameter mem : forall (x : elt) (s : t), {In x s} + {~ In x s}.

  Parameter add : forall (x : elt) (s : t), {s' : t | Add x s s'}.

  Parameter
    singleton : forall x : elt, {s : t | forall y : elt, In y s <-> E.eq x y}.

  Parameter
    remove :
      forall (x : elt) (s : t),
      {s' : t | forall y : elt, In y s' <-> ~ E.eq x y /\ In y s}.

  Parameter
    union :
      forall s s' : t,
      {s'' : t | forall x : elt, In x s'' <-> In x s \/ In x s'}.

  Parameter
    inter :
      forall s s' : t,
      {s'' : t | forall x : elt, In x s'' <-> In x s /\ In x s'}.

  Parameter
    diff :
      forall s s' : t,
      {s'' : t | forall x : elt, In x s'' <-> In x s /\ ~ In x s'}.

  Parameter equal : forall s s' : t, {s[=]s'} + {~ s[=]s'}.

  Parameter subset : forall s s' : t, {Subset s s'} + {~ Subset s s'}.

  Parameter
    filter :
      forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
        (s : t),
      {s' : t | compat_P E.eq P -> forall x : elt, In x s' <-> In x s /\ P x}.

  Parameter
    for_all :
      forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
        (s : t),
      {compat_P E.eq P -> For_all P s} + {compat_P E.eq P -> ~ For_all P s}.

  Parameter
    exists_ :
      forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
        (s : t),
      {compat_P E.eq P -> Exists P s} + {compat_P E.eq P -> ~ Exists P s}.

  Parameter
    partition :
      forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
        (s : t),
      {partition : t * t |
      let (s1, s2) := partition in
      compat_P E.eq P ->
      For_all P s1 /\
      For_all (fun x => ~ P x) s2 /\
      (forall x : elt, In x s <-> In x s1 \/ In x s2)}.

  Parameter
    elements :
      forall s : t,
      {l : list elt |
      sort E.lt l /\ (forall x : elt, In x s <-> InA E.eq x l)}.

  Parameter
    fold :
      forall (A : Type) (f : elt -> A -> A) (s : t) (i : A),
      {r : A | let (l,_) := elements s in
                  r = fold_left (fun a e => f e a) l i}.

  Parameter
    cardinal :
      forall s : t,
      {r : nat | let (l,_) := elements s in r = length l }.

  Parameter
    min_elt :
      forall s : t,
      {x : elt | In x s /\ For_all (fun y => ~ E.lt y x) s} + {Empty s}.

  Parameter
    max_elt :
      forall s : t,
      {x : elt | In x s /\ For_all (fun y => ~ E.lt x y) s} + {Empty s}.

  Parameter choose : forall s : t, {x : elt | In x s} + {Empty s}.

  (** The [choose_3] specification of [S] cannot be packed
        in the dependent version of [choose], so we leave it separate. *)
  Parameter choose_equal : forall s s', Equal s s' ->
     match choose s, choose s' with
       | inleft (exist _ x _), inleft (exist _ x' _) => E.eq x x'
       | inright _, inright _  => True
       | _, _  => False
     end.

End Sdep.

