(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** Set interfaces *)

Require Export Bool.
Require Export PolyList.
Require Export Sorting.
Require Export Setoid.
Set Implicit Arguments.

(** Misc properties used in specifications. *)

Section Misc.
Variable A,B : Set.
Variable eqA : A -> A -> Prop. 
Variable eqB : B -> B -> Prop.

(** Compatibility of a  boolean function with respect to an equality. *)
Definition compat_bool := [f:A->bool] (x,y:A)(eqA x y) -> (f x)=(f y).

(** Compatibility of a predicate with respect to an equality. *)
Definition compat_P := [P:A->Prop](x,y:A)(eqA x y) -> (P x) -> (P y).

(** Being in a list modulo an equality relation. *)
Inductive InList [x:A] : (list A) -> Prop :=
  | InList_cons_hd : (y:A)(l:(list A))(eqA x y) -> (InList x (cons y l))
  | InList_cons_tl : (y:A)(l:(list A))(InList x l) -> (InList x (cons y l)).

(** A list without redondancy. *)
Inductive Unique : (list A) -> Prop := 
  | Unique_nil : (Unique (nil A)) 
  | Unique_cons : (x:A)(l:(list A)) ~(InList x l) -> (Unique l) -> (Unique (cons x l)).

End Misc.

Hint InList := Constructors InList.
Hint InList := Constructors Unique.
Hint sort := Constructors sort.
Hint lelistA := Constructors lelistA.
Hints Unfold compat_bool compat_P.

(** * Ordered types *)

Inductive Compare [X:Set; lt,eq:X->X->Prop; x,y:X] : Set :=
  | Lt : (lt x y) -> (Compare lt eq x y)
  | Eq : (eq x y) -> (Compare lt eq x y)
  | Gt : (lt y x) -> (Compare lt eq x y).

Module Type OrderedType.

  Parameter t : Set.

  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : (x:t) (eq x x).
  Axiom eq_sym : (x,y:t) (eq x y) -> (eq y x).
  Axiom eq_trans : (x,y,z:t) (eq x y) -> (eq y z) -> (eq x z).
 
  Axiom lt_trans : (x,y,z:t) (lt x y) -> (lt y z) -> (lt x z).
  Axiom lt_not_eq : (x,y:t) (lt x y) -> ~(eq x y).

  Parameter compare : (x,y:t)(Compare lt eq x y).

  Hints Immediate eq_sym.
  Hints Resolve eq_refl eq_trans lt_not_eq lt_trans.

End OrderedType.

(** * Non-dependent signature

    Signature [S] presents sets as purely informative programs 
    together with axioms *)

Module Type S.

  Declare Module E : OrderedType.
  Definition elt := E.t.

  Parameter t : Set. (** the abstract type of sets *)
 
  Parameter empty: t.
  (** The empty set. *)

  Parameter is_empty: t -> bool.
  (** Test whether a set is empty or not. *)

  Parameter mem: elt -> t -> bool.
  (** [mem x s] tests whether [x] belongs to the set [s]. *)

  Parameter add: elt -> t -> t.
  (** [add x s] returns a set containing all elements of [s],
  plus [x]. If [x] was already in [s], [s] is returned unchanged. *)

  Parameter singleton: elt -> t.
  (** [singleton x] returns the one-element set containing only [x]. *)

  Parameter remove: elt -> t -> t.
  (** [remove x s] returns a set containing all elements of [s],
  except [x]. If [x] was not in [s], [s] is returned unchanged. *)

  Parameter union: t -> t -> t.
  (** Set union. *)

  Parameter inter: t -> t -> t.
  (** Set intersection. *)

  Parameter diff:  t -> t -> t.
  (** Set difference. *)

  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.
  Parameter compare: (s,s':t)(Compare lt eq s s').
  (** Total ordering between sets. Can be used as the ordering function
  for doing sets of sets. *)

  Parameter equal:  t -> t -> bool.
  (** [equal s1 s2] tests whether the sets [s1] and [s2] are
  equal, that is, contain equal elements. *)

  Parameter subset:  t -> t -> bool.
  (** [subset s1 s2] tests whether the set [s1] is a subset of
  the set [s2]. *)

  (** Coq comment: [iter] is useless in a purely functional world *)
  (**  iter: (elt -> unit) -> set -> unit. i*)
  (** [iter f s] applies [f] in turn to all elements of [s].
  The order in which the elements of [s] are presented to [f]
  is unspecified. *)

  Parameter fold:  (A:Set)(elt -> A -> A) -> t -> A -> A.
  (** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)],
  where [x1 ... xN] are the elements of [s].
  The order in which elements of [s] are presented to [f] is
  unspecified. *)

  Parameter for_all:  (elt -> bool) -> t -> bool.
  (** [for_all p s] checks if all elements of the set
  satisfy the predicate [p]. *)

  Parameter exists:  (elt -> bool) -> t -> bool.
  (** [exists p s] checks if at least one element of
  the set satisfies the predicate [p]. *)

  Parameter filter:  (elt -> bool) -> t -> t.
  (** [filter p s] returns the set of all elements in [s]
  that satisfy predicate [p]. *)

  Parameter partition:  (elt -> bool) -> t -> t * t.
  (** [partition p s] returns a pair of sets [(s1, s2)], where
  [s1] is the set of all the elements of [s] that satisfy the
  predicate [p], and [s2] is the set of all the elements of
  [s] that do not satisfy [p]. *)

  Parameter cardinal: t -> nat.
  (** Return the number of elements of a set. *)
  (** Coq comment: nat instead of int ... *)

  Parameter elements: t -> (list elt).
  (** Return the list of all elements of the given set.
  The returned list is sorted in increasing order with respect
  to the ordering [Ord.compare], where [Ord] is the argument
  given to {!Set.Make}. *)

  Parameter min_elt: t -> (option elt).
  (** Return the smallest element of the given set
  (with respect to the [Ord.compare] ordering), or raise
  [Not_found] if the set is empty. *)
  (** Coq comment: [Not_found] is represented by the option type *)

  Parameter max_elt: t -> (option elt).
  (** Same as {!Set.S.min_elt}, but returns the largest element of the
  given set. *)
  (** Coq comment: [Not_found] is represented by the option type *)

  Parameter choose: t -> (option elt).
  (** Return one element of the given set, or raise [Not_found] if
  the set is empty. Which element is chosen is unspecified,
  but equal elements will be chosen for equal sets. *)
  (** Coq comment: [Not_found] is represented by the option type *)
  (** Coq comment: We do not necessary choose equal elements from 
     equal sets. *)

  Section Spec. 

  Variable s,s',s'' : t.
  Variable x,y,z : elt.

  Parameter In : elt -> t -> Prop.
  Definition Equal := [s,s'](a:elt)(In a s)<->(In a s').
  Definition Subset := [s,s'](a:elt)(In a s)->(In a s').
  Definition Add := [x:elt;s,s':t](y:elt)(In y s') <-> ((E.eq y x)\/(In y s)).
  Definition Empty := [s](a:elt)~(In a s).
  Definition For_all := [P:elt->Prop; s:t](x:elt)(In x s)->(P x).
  Definition Exists := [P:elt->Prop; s:t](EX x:elt | (In x s)/\(P x)).

  (** Specification of [In] *)
  Parameter In_1: (E.eq x y) -> (In x s) -> (In y s).

  (** Specification of [eq] *)
  Parameter eq_refl: (eq s s). 
  Parameter eq_sym: (eq s s') -> (eq s' s).
  Parameter eq_trans: (eq s s') -> (eq s' s'') -> (eq s s'').
 
  (** Specification of [lt] *)
  Parameter lt_trans : (lt s s') -> (lt s' s'') -> (lt s s'').
  Parameter lt_not_eq : (lt s s') -> ~(eq s s').

  (** Specification of [mem] *)
  Parameter mem_1: (In x s) -> (mem x s)=true.
  Parameter mem_2: (mem x s)=true -> (In x s). 
 
  (** Specification of [equal] *) 
  Parameter equal_1: (Equal s s') -> (equal s s')=true.
  Parameter equal_2: (equal s s')=true -> (Equal s s').

  (** Specification of [subset] *)
  Parameter subset_1: (Subset s s') -> (subset s s')=true.
  Parameter subset_2: (subset s s')=true -> (Subset s s').

  (** Specification of [empty] *)
  Parameter empty_1: (Empty empty).

  (** Specification of [is_empty] *)
  Parameter is_empty_1: (Empty s) -> (is_empty s)=true. 
  Parameter is_empty_2: (is_empty s)=true -> (Empty s).
 
  (** Specification of [add] *)
  Parameter add_1: (In x (add x s)).
  Parameter add_2: (In y s) -> (In y (add x s)).
  Parameter add_3: ~(E.eq x y) -> (In y (add x s)) -> (In y s). 

  (** Specification of [remove] *)
  Parameter remove_1: ~(In x (remove x s)).
  Parameter remove_2: ~(E.eq x y) -> (In y s) -> (In y (remove x s)).
  Parameter remove_3: (In y (remove x s)) -> (In y s).

  (** Specification of [singleton] *)
  Parameter singleton_1: (In y (singleton x)) -> (E.eq x y). 
  Parameter singleton_2: (E.eq x y) -> (In y (singleton x)). 

  (** Specification of [union] *)
  Parameter union_1: (In x (union s s')) -> (In x s)\/(In x s').
  Parameter union_2: (In x s) -> (In x (union s s')). 
  Parameter union_3: (In x s') ->  (In x (union s s')).

  (** Specification of [inter] *)
  Parameter inter_1: (In x (inter s s')) -> (In x s).
  Parameter inter_2: (In x (inter s s')) -> (In x s').
  Parameter inter_3: (In x s) -> (In x s') ->  (In x (inter s s')).

  (** Specification of [diff] *)
  Parameter diff_1: (In x (diff s s')) -> (In x s). 
  Parameter diff_2: (In x (diff s s')) -> ~(In x s').
  Parameter diff_3: (In x s) -> ~(In x s') -> (In x (diff s s')).
 
  (** Specification of [fold] *)  
  Parameter fold_1: 
   (A:Set)(i:A)(f:elt->A->A)
   (EX l:(list elt) | 
       (Unique E.eq l) /\ 
       ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
       (fold f s i)=(fold_right f i l)).

  (** Specification of [cardinal] *)  
  Parameter cardinal_1: 
    (EX l:(list elt) | 
        (Unique E.eq l) /\
        ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
        (cardinal s)=(length l)).

  Section Filter.
  
  Variable f:elt->bool.

  (** Specification of [filter] *)
  Parameter filter_1: (compat_bool E.eq f) -> (In x (filter f s)) -> (In x s). 
  Parameter filter_2: (compat_bool E.eq f) -> (In x (filter f s)) -> (f x)=true. 
  Parameter filter_3: 
    (compat_bool E.eq f) -> (In x s) -> (f x)=true -> (In x (filter f s)).

  (** Specification of [for_all] *)
  Parameter for_all_1: 
    (compat_bool E.eq f) -> (For_all [x](f x)=true s) -> (for_all f s)=true.
  Parameter for_all_2: 
    (compat_bool E.eq f) -> (for_all f s)=true -> (For_all [x](f x)=true s).

  (** Specification of [exists] *)
  Parameter exists_1: 
    (compat_bool E.eq f) -> (Exists [x](f x)=true s) -> (exists f s)=true.
  Parameter exists_2: 
    (compat_bool E.eq f) -> (exists f s)=true -> (Exists [x](f x)=true s).

  (** Specification of [partition] *)
  Parameter partition_1: 
    (compat_bool E.eq f) -> (Equal (fst ? ? (partition f s)) (filter f s)).
  Parameter partition_2: 
    (compat_bool E.eq f) -> 
    (Equal (snd ? ? (partition f s)) (filter [x](negb (f x)) s)).

  (** Specification of [elements] *)
  Parameter elements_1: (In x s) -> (InList E.eq x (elements s)).
  Parameter elements_2: (InList E.eq x (elements s)) -> (In x s).
  Parameter elements_3: (sort E.lt (elements s)).  

  (** Specification of [min_elt] *)
  Parameter min_elt_1: (min_elt s) = (Some ? x) -> (In x s). 
  Parameter min_elt_2: (min_elt s) = (Some ? x) -> (In y s) -> ~(E.lt y x). 
  Parameter min_elt_3: (min_elt s) = (None ?) -> (Empty s).

  (** Specification of [max_elt] *)  
  Parameter max_elt_1: (max_elt s) = (Some ? x) -> (In x s). 
  Parameter max_elt_2: (max_elt s) = (Some ? x) -> (In y s) -> ~(E.lt x y). 
  Parameter max_elt_3: (max_elt s) = (None ?) -> (Empty s).

  (** Specification of [choose] *)
  Parameter choose_1: (choose s)=(Some ? x) -> (In x s).
  Parameter choose_2: (choose s)=(None ?) -> (Empty s).
  (*i Parameter choose_equal: 
      (equal s s')=true -> (compare (choose s) (choose s'))=E. i*)

  End Filter.
  End Spec.

  Notation "∅" := empty.
  Notation "a ⋃ b" := (union a b) (at level 1).
  Notation "a ⋂ b" := (inter a b) (at level 1). 
  Notation "∥ a ∥" := (cardinal a) (at level 1).
  Notation "a ∈ b" := (In a b) (at level 1).
  Notation "a ∉ b" := ~(In a b) (at level 1).
  Notation "a ≡ b" := (Equal a b) (at level 1).
  Notation "a ≢ b" := ~(Equal a b) (at level 1).
  Notation "a ⊆ b" := (Subset a b) (at level 1).
  Notation "a ⊈ b" := ~(Subset a b) (at level 1).  

  Hints Immediate 
  In_1.
  
  Hints Resolve 
  mem_1 mem_2
  equal_1 equal_2
  subset_1 subset_2
  empty_1
  is_empty_1 is_empty_2
  choose_1
  choose_2
  add_1 add_2 add_3
  remove_1 remove_2 remove_3
  singleton_1 singleton_2
  union_1 union_2 union_3
  inter_1 inter_2 inter_3 
  diff_1 diff_2 diff_3
  filter_1 filter_2 filter_3
  for_all_1 for_all_2
  exists_1 exists_2
  partition_1 partition_2
  elements_1 elements_2 elements_3
  min_elt_1 min_elt_2 min_elt_3
  max_elt_1 max_elt_2 max_elt_3.

End S.

(** * Dependent signature 

    Signature [Sdep] presents sets using dependent types *)

Module Type Sdep.

  Declare Module E : OrderedType.
  Definition elt := E.t.

  Parameter t : Set.

  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.
  Parameter compare: (s,s':t)(Compare lt eq s s').

  Parameter eq_refl: (s:t)(eq s s). 
  Parameter eq_sym: (s,s':t)(eq s s') -> (eq s' s).
  Parameter eq_trans: (s,s',s'':t)(eq s s') -> (eq s' s'') -> (eq s s'').
  Parameter lt_trans : (s,s',s'':t)(lt s s') -> (lt s' s'') -> (lt s s'').
  Parameter lt_not_eq : (s,s':t)(lt s s') -> ~(eq s s').

  Parameter In : elt -> t -> Prop.
  Definition Equal := [s,s'](a:elt)(In a s)<->(In a s').
  Definition Subset := [s,s'](a:elt)(In a s)->(In a s').
  Definition Add := [x:elt;s,s':t](y:elt)(In y s') <-> ((E.eq y x)\/(In y s)).
  Definition Empty := [s](a:elt)~(In a s).
  Definition For_all := [P:elt->Prop; s:t](x:elt)(In x s)->(P x).
  Definition Exists := [P:elt->Prop; s:t](EX x:elt | (In x s)/\(P x)).

  Parameter eq_In: (s:t)(x,y:elt)(E.eq x y) -> (In x s) -> (In y s).

  Parameter empty : { s:t | Empty s }.

  Parameter is_empty : (s:t){ Empty s }+{ ~(Empty s) }.

  Parameter mem : (x:elt) (s:t) { (In x s) } + { ~(In x s) }.

  Parameter add : (x:elt) (s:t) { s':t | (Add x s s') }.

  Parameter singleton : (x:elt){ s:t | (y:elt)(In y s) <-> (E.eq x y)}.
  
  Parameter remove : (x:elt)(s:t)
                     { s':t | (y:elt)(In y s') <-> (~(E.eq y x) /\ (In y s))}.

  Parameter union : (s,s':t)
                    { s'':t | (x:elt)(In x s'') <-> ((In x s)\/(In x s'))}.

  Parameter inter : (s,s':t)
                    { s'':t | (x:elt)(In x s'') <-> ((In x s)/\(In x s'))}.

  Parameter diff : (s,s':t)
                    { s'':t | (x:elt)(In x s'') <-> ((In x s)/\~(In x s'))}.

  Parameter equal : (s,s':t){ Equal s s' } + { ~(Equal s s') }.
 
  Parameter subset : (s,s':t) { Subset s s' } + { ~(Subset s s') }.

  Parameter fold : 
   (A:Set)(f:elt->A->A)(s:t)(i:A) 
   { r : A | (EX l:(list elt) | 
                  (Unique E.eq l) /\
                  ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
                  r = (fold_right f i l)) }.

  Parameter cardinal : 
    (s:t) { r : nat | (EX l:(list elt) | 
                              (Unique E.eq l) /\ 
                              ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
                              r = (length l)) }.

  Parameter filter : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { s':t | (compat_P E.eq P) -> (x:elt)(In x s') <-> ((In x s)/\(P x)) }.

  Parameter for_all : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { (compat_P E.eq P) -> (For_all P s) } + 
     { (compat_P E.eq P) -> ~(For_all P s) }.
  
  Parameter exists : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { (compat_P E.eq P) -> (Exists P s) } + 
     { (compat_P E.eq P) -> ~(Exists P s) }.

  Parameter partition : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { partition : t*t | 
        let (s1,s2) = partition in 
	(compat_P E.eq P) -> 
	((For_all P s1) /\ 
	 (For_all ([x]~(P x)) s2) /\
	 (x:elt)(In x s)<->((In x s1)\/(In x s2))) }.

  Parameter elements : 
     (s:t){ l:(list elt) | (sort E.lt l) /\ (x:elt)(In x s)<->(InList E.eq x l)}.

  Parameter min_elt : 
     (s:t){ x:elt | (In x s) /\ (For_all [y]~(E.lt y x) s) } + { Empty s }.

  Parameter max_elt : 
     (s:t){ x:elt | (In x s) /\ (For_all [y]~(E.lt x y) s) } + { Empty s }.

  Parameter choose : (s:t) { x:elt | (In x s)} + { Empty s }.

  Notation "∅" := empty.
  Notation "a ⋃ b" := (union a b) (at level 1).
  Notation "a ⋂ b" := (inter a b) (at level 1).
  Notation "a ∈ b" := (In a b) (at level 1).
  Notation "a ∉ b" := ~(In a b) (at level 1).
  Notation "a ≡ b" := (Equal a b) (at level 1).
  Notation "a ≢ b" := ~(Equal a b) (at level 1).
  Notation "a ⊆ b" := (Subset a b) (at level 1).
  Notation "a ⊈ b" := ~(Subset a b) (at level 1).  
	
End Sdep.

(** * Ordered types properties *)

(** Additional properties that can be derived from signature
    [OrderedType]. *)

Module MoreOrderedType [O:OrderedType]. 

  Lemma gt_not_eq : (x,y:O.t)(O.lt y x) -> ~(O.eq x y).
  Proof.
   Intros; Intro; Absurd (O.eq y x); Auto.
  Qed.	
 
  Lemma eq_not_lt : (x,y:O.t)(O.eq x y) -> ~(O.lt x y).
  Proof. 
   Intros; Intro; Absurd (O.eq x y); Auto.
  Qed.

  Hints Resolve gt_not_eq eq_not_lt.

  Lemma eq_not_gt : (x,y:O.t)(O.eq x y) -> ~(O.lt y x).
  Proof. 
   Auto. 
  Qed.
  
  Lemma lt_antirefl : (x:O.t)~(O.lt x x).
  Proof.
   Intros; Intro; Absurd (O.eq x x); Auto. 
  Qed.

  Lemma lt_not_gt : (x,y:O.t)(O.lt x y) -> ~(O.lt y x).
  Proof. 
   Intros; Intro; Absurd (O.eq x x); EAuto.
  Qed.

  Hints Resolve eq_not_gt lt_antirefl lt_not_gt.

  Lemma lt_eq : (x,y,z:O.t)(O.lt x y) -> (O.eq y z) -> (O.lt x z).
  Proof. 
   Intros; Case (O.compare x z); Intros; Auto.
   Absurd (O.eq x y); EAuto.
   Absurd (O.eq z y); EAuto. 
  Qed. 
 
  Lemma eq_lt : (x,y,z:O.t)(O.eq x y) -> (O.lt y z) -> (O.lt x z).    
  Proof.
    Intros; Case (O.compare x z); Intros; Auto.
   Absurd (O.eq y z); EAuto.
   Absurd (O.eq x y); EAuto. 
  Qed. 

  Hints Immediate eq_lt lt_eq.

  Lemma elim_compare_eq: 
   (x,y:O.t) (O.eq x y) -> 
      (EX H : (O.eq x y) | (O.compare x y) = (Eq ? H)).
  Proof. 
   Intros; Case (O.compare x y); Intros H'.
   Absurd (O.eq x y); Auto. 
   Exists H'; Auto.   
   Absurd (O.eq x y); Auto.
  Qed.

  Lemma elim_compare_lt: 
   (x,y:O.t) (O.lt x y) -> 
      (EX H : (O.lt x y) | (O.compare x y) = (Lt ? H)).
  Proof. 
   Intros; Case (O.compare x y); Intros H'.
   Exists H'; Auto.   
   Absurd (O.eq x y); Auto. 
   Absurd (O.lt x x); EAuto.
  Qed.

  Lemma elim_compare_gt: 
   (x,y:O.t) (O.lt y x) -> 
      (EX H : (O.lt y x) | (O.compare x y) = (Gt ? H)).
  Proof. 
   Intros; Case (O.compare x y); Intros H'.
   Absurd (O.lt x x); EAuto.
   Absurd (O.eq x y); Auto.
   Exists H'; Auto.   
  Qed.

  Tactic Definition Comp_eq x y := 
    Elim (!elim_compare_eq x y); 
    [Intros _1 _2; Rewrite _2; Clear _1 _2 | Auto]. 

  Tactic Definition Comp_lt x y := 
    Elim (!elim_compare_lt x y); 
    [Intros _1 _2; Rewrite _2; Clear _1 _2 | Auto]. 

  Tactic Definition Comp_gt x y := 
    Elim (!elim_compare_gt x y); 
    [Intros _1 _2; Rewrite _2; Clear _1 _2 | Auto].

  Lemma eq_dec : (x,y:O.t){(O.eq x y)}+{~(O.eq x y)}.
  Proof.
   Intros; Elim (O.compare x y);[Right|Left|Right];Auto.
  Qed.
 
  Lemma lt_dec : (x,y:O.t){(O.lt x y)}+{~(O.lt x y)}.
  Proof.
   Intros; Elim (O.compare x y);[Left|Right|Right];Auto.
  Qed.

  (** Results concerning lists modulo E.eq *)
  
  Notation "'Sort' l" := (sort O.lt l) (at level 10, l at level 8).
  Notation "'Inf' x l" := (lelistA O.lt x l) (at level 10, x,l at level 8).
  Notation "'In' x l" := (InList O.eq x l) (at level 10, x,l at level 8).

  Lemma In_eq: (s:(list O.t))(x,y:O.t)(O.eq x y) -> (In x s) -> (In y s).
  Proof. 
   Intros; Elim H0; Intuition; EAuto.
  Qed.
  Hints Immediate In_eq.
  
  Lemma Inf_lt : (s:(list O.t))(x,y:O.t)(O.lt x y) -> (Inf y s) -> (Inf x s).
  Proof.
  Intro s; Case s; Constructor; Inversion H0; EAuto.
  Qed.
 
  Lemma Inf_eq : (s:(list O.t))(x,y:O.t)(O.eq x y) -> (Inf y s) -> (Inf x s).
  Proof.
  Intro s; Case s; Constructor; Inversion H0; EApply eq_lt; EAuto.
  Qed.
  Hints Resolve Inf_lt Inf_eq. 

  Lemma In_sort: (s:(list O.t))(x,a:O.t)(Inf a s) -> (In x s) -> (Sort s) -> (O.lt a x).
  Proof. 
  Induction s.
  Intros; Inversion H0.
  Intros.
  Inversion_clear H0; Inversion_clear H2; Inversion_clear H1.
  EApply lt_eq; EAuto.
  EAuto.
  Qed.
  
  Lemma Inf_In : (l:(list O.t))(x:O.t)
    ((y:O.t)(PolyList.In y l) -> (O.lt x y)) -> (Inf x l).
  Proof.
    Induction l; Simpl; Intros; Constructor; Auto.
  Save.
 
  Lemma Inf_In_2 : (l:(list O.t))(x:O.t)
    ((y:O.t)(In y l) -> (O.lt x y)) -> (Inf x l).
  Proof.
    Induction l; Simpl; Intros; Constructor; Auto.
  Save.
  
  Lemma In_InList : (l:(list O.t))(x:O.t)(PolyList.In x l) -> (In x l).
  Proof.
   Induction l; Simpl; Intuition.
    Subst; Auto.  
  Save.
  Hints Resolve In_InList.

  Lemma Sort_Unique : (l:(list O.t))(Sort l) -> (Unique O.eq l).
  Proof.
  Induction l; Auto.
  Intros x l' H H0.
  Inversion_clear H0.
  Constructor; Auto.  
  Intro.
  Absurd (O.lt x x); Auto.
  EApply In_sort; EAuto.
  Qed.

End MoreOrderedType.

