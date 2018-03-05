(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite map library *)

(** This file proposes interfaces for finite maps *)

Require Export Bool DecidableType OrderedType.
Set Implicit Arguments.
Unset Strict Implicit.

(** When compared with Ocaml Map, this signature has been split in
    several parts :

   - The first parts [WSfun] and [WS] propose signatures for weak
     maps, which are maps with no ordering on the key type nor the
     data type.  [WSfun] and [WS] are almost identical, apart from the
     fact that [WSfun] is expressed in a functorial way whereas [WS]
     is self-contained. For obtaining an instance of such signatures,
     a decidable equality on keys in enough (see for example
     [FMapWeakList]). These signatures contain the usual operators
     (add, find, ...). The only function that asks for more is
     [equal], whose first argument should be a comparison on data.

   - Then comes [Sfun] and [S], that extend [WSfun] and [WS] to the
     case where the key type is ordered. The main novelty is that
     [elements] is required to produce sorted lists.

   - Finally, [Sord] extends [S] with a complete comparison function. For
     that, the data type should have a decidable total ordering as well.

   If unsure, what you're looking for is probably [S]: apart from [Sord],
   all other signatures are subsets of [S].

   Some additional differences with Ocaml:

    - no [iter] function, useless since Coq is purely functional
    - [option] types are used instead of [Not_found] exceptions
    - more functions are provided: [elements] and [cardinal] and [map2]

*)


Definition Cmp (elt:Type)(cmp:elt->elt->bool) e1 e2 := cmp e1 e2 = true.

(** ** Weak signature for maps

    No requirements for an ordering on keys nor elements, only decidability
    of equality on keys. First, a functorial signature: *)

Module Type WSfun (E : DecidableType).

  Definition key := E.t.
  Hint Transparent key.

  Parameter t : Type -> Type.
  (** the abstract type of maps *)

  Section Types.

    Variable elt:Type.

    Parameter empty : t elt.
    (** The empty map. *)

    Parameter is_empty : t elt -> bool.
    (** Test whether a map is empty or not. *)

    Parameter add : key -> elt -> t elt -> t elt.
    (** [add x y m] returns a map containing the same bindings as [m],
	plus a binding of [x] to [y]. If [x] was already bound in [m],
	its previous binding disappears. *)

    Parameter find : key -> t elt -> option elt.
    (** [find x m] returns the current binding of [x] in [m],
	or [None] if no such binding exists. *)

    Parameter remove : key -> t elt -> t elt.
    (** [remove x m] returns a map containing the same bindings as [m],
	except for [x] which is unbound in the returned map. *)

    Parameter mem : key -> t elt -> bool.
    (** [mem x m] returns [true] if [m] contains a binding for [x],
	and [false] otherwise. *)

    Variable elt' elt'' : Type.

    Parameter map : (elt -> elt') -> t elt -> t elt'.
    (** [map f m] returns a map with same domain as [m], where the associated
	value a of all bindings of [m] has been replaced by the result of the
	application of [f] to [a]. Since Coq is purely functional, the order
        in which the bindings are passed to [f] is irrelevant. *)

    Parameter mapi : (key -> elt -> elt') -> t elt -> t elt'.
    (** Same as [map], but the function receives as arguments both the
	key and the associated value for each binding of the map. *)

    Parameter map2 :
     (option elt -> option elt' -> option elt'') -> t elt -> t elt' ->  t elt''.
    (** [map2 f m m'] creates a new map whose bindings belong to the ones
        of either [m] or [m']. The presence and value for a key [k] is
        determined by [f e e'] where [e] and [e'] are the (optional) bindings
        of [k] in [m] and [m']. *)

    Parameter elements : t elt -> list (key*elt).
    (** [elements m] returns an assoc list corresponding to the bindings
        of [m], in any order. *)

    Parameter cardinal : t elt -> nat.
    (** [cardinal m] returns the number of bindings in [m]. *)

    Parameter fold : forall A: Type, (key -> elt -> A -> A) -> t elt -> A -> A.
    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)],
	where [k1] ... [kN] are the keys of all bindings in [m]
	(in any order), and [d1] ... [dN] are the associated data. *)

    Parameter equal : (elt -> elt -> bool) -> t elt -> t elt -> bool.
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal,
      that is, contain equal keys and associate them with equal data.
      [cmp] is the equality predicate used to compare the data associated
      with the keys. *)

    Section Spec.

      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.

      Parameter MapsTo : key -> elt -> t elt -> Prop.

      Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.

      Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

      Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').

      Definition eq_key_elt (p p':key*elt) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

    (** Specification of [MapsTo] *)
      Parameter MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.

    (** Specification of [mem] *)
      Parameter mem_1 : In x m -> mem x m = true.
      Parameter mem_2 : mem x m = true -> In x m.

    (** Specification of [empty] *)
      Parameter empty_1 : Empty empty.

    (** Specification of [is_empty] *)
      Parameter is_empty_1 : Empty m -> is_empty m = true.
      Parameter is_empty_2 : is_empty m = true -> Empty m.

    (** Specification of [add] *)
      Parameter add_1 : E.eq x y -> MapsTo y e (add x e m).
      Parameter add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      Parameter add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.

    (** Specification of [remove] *)
      Parameter remove_1 : E.eq x y -> ~ In y (remove x m).
      Parameter remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      Parameter remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.

    (** Specification of [find] *)
      Parameter find_1 : MapsTo x e m -> find x m = Some e.
      Parameter find_2 : find x m = Some e -> MapsTo x e m.

    (** Specification of [elements] *)
      Parameter elements_1 :
        MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
      Parameter elements_2 :
        InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
      (** When compared with ordered maps, here comes the only
         property that is really weaker: *)
      Parameter elements_3w : NoDupA eq_key (elements m).

    (** Specification of [cardinal] *)
      Parameter cardinal_1 : cardinal m = length (elements m).

    (** Specification of [fold] *)
      Parameter fold_1 :
	forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.

    (** Equality of maps *)

    (** Caveat: there are at least three distinct equality predicates on maps.
      - The simpliest (and maybe most natural) way is to consider keys up to
        their equivalence [E.eq], but elements up to Leibniz equality, in
        the spirit of [eq_key_elt] above. This leads to predicate [Equal].
      - Unfortunately, this [Equal] predicate can't be used to describe
        the [equal] function, since this function (for compatibility with
        ocaml) expects a boolean comparison [cmp] that may identify more
        elements than Leibniz. So logical specification of [equal] is done
        via another predicate [Equivb]
      - This predicate [Equivb] is quite ad-hoc with its boolean [cmp],
        it can be generalized in a [Equiv] expecting a more general
        (possibly non-decidable) equality predicate on elements *)

     Definition Equal m m' := forall y, find y m = find y m'.
     Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
         (forall k, In k m <-> In k m') /\
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
     Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

     (** Specification of [equal] *)

     Variable cmp : elt -> elt -> bool.

     Parameter equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
     Parameter equal_2 : equal cmp m m' = true -> Equivb cmp m m'.

    End Spec.
   End Types.

    (** Specification of [map] *)
      Parameter map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
      Parameter map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
        In x (map f m) -> In x m.

    (** Specification of [mapi] *)
      Parameter mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
      Parameter mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.

    (** Specification of [map2] *)
      Parameter map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''),
	In x m \/ In x m' ->
        find x (map2 f m m') = f (find x m) (find x m').

     Parameter map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''),
        In x (map2 f m m') -> In x m \/ In x m'.

  Hint Immediate MapsTo_1 mem_2 is_empty_2
    map_2 mapi_2 add_3 remove_3 find_2
    : map.
  Hint Resolve mem_1 is_empty_1 is_empty_2 add_1 add_2 remove_1
    remove_2 find_1 fold_1 map_1 mapi_1 mapi_2
    : map.

End WSfun.


(** ** Static signature for Weak Maps

    Similar to [WSfun] but expressed in a self-contained way. *)

Module Type WS.
  Declare Module E : DecidableType.
  Include WSfun E.
End WS.



(** ** Maps on ordered keys, functorial signature *)

Module Type Sfun (E : OrderedType).
  Include WSfun E.
  Section elt.
  Variable elt:Type.
   Definition lt_key (p p':key*elt) := E.lt (fst p) (fst p').
   (* Additional specification of [elements] *)
   Parameter elements_3 : forall m, sort lt_key (elements m).
   (** Remark: since [fold] is specified via [elements], this stronger
   specification of [elements] has an indirect impact on [fold],
   which can now be proved to receive elements in increasing order. *)
  End elt.
End Sfun.



(** ** Maps on ordered keys, self-contained signature *)

Module Type S.
  Declare Module E : OrderedType.
  Include Sfun E.
End S.



(** ** Maps with ordering both on keys and datas *)

Module Type Sord.

  Declare Module Data : OrderedType.
  Declare Module MapS : S.
  Import MapS.

  Definition t := MapS.t Data.t.

  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : forall m : t, eq m m.
  Axiom eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Axiom eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Axiom lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Axiom lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

  Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.

  Parameter eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
  Parameter eq_2 : forall m m', eq m m' -> Equivb cmp m m'.

  Parameter compare : forall m1 m2, Compare lt eq m1 m2.
  (** Total ordering between maps. [Data.compare] is a total ordering
      used to compare data associated with equal keys in the two maps. *)

End Sord.
