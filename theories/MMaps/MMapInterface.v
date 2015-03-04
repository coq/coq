(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Finite map library *)

(** This file proposes interfaces for finite maps *)

Require Export Bool Equalities Orders SetoidList.
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
     [bindings] is required to produce sorted lists.

   - Finally, [Sord] extends [S] with a complete comparison function. For
     that, the data type should have a decidable total ordering as well.

   If unsure, what you're looking for is probably [S]: apart from [Sord],
   all other signatures are subsets of [S].

   Some additional differences with Ocaml:

    - no [iter] function, useless since Coq is purely functional
    - [option] types are used instead of [Not_found] exceptions

*)


Definition Cmp {elt:Type}(cmp:elt->elt->bool) e1 e2 := cmp e1 e2 = true.

(** ** Weak signature for maps

    No requirements for an ordering on keys nor elements, only decidability
    of equality on keys. First, a functorial signature: *)

Module Type WSfun (E : DecidableType).

  Definition key := E.t.
  Hint Transparent key.

  Definition eq_key {elt} (p p':key*elt) := E.eq (fst p) (fst p').

  Definition eq_key_elt {elt} (p p':key*elt) :=
      E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Parameter t : Type -> Type.
  (** the abstract type of maps *)

  Section Ops.

    Parameter empty : forall {elt}, t elt.
    (** The empty map. *)

    Variable elt:Type.

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

    Parameter bindings : t elt -> list (key*elt).
    (** [bindings m] returns an assoc list corresponding to the bindings
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

    Variable elt' elt'' : Type.

    Parameter map : (elt -> elt') -> t elt -> t elt'.
    (** [map f m] returns a map with same domain as [m], where the associated
	value a of all bindings of [m] has been replaced by the result of the
	application of [f] to [a]. Since Coq is purely functional, the order
        in which the bindings are passed to [f] is irrelevant. *)

    Parameter mapi : (key -> elt -> elt') -> t elt -> t elt'.
    (** Same as [map], but the function receives as arguments both the
	key and the associated value for each binding of the map. *)

    Parameter merge : (key -> option elt -> option elt' -> option elt'') ->
                      t elt -> t elt' ->  t elt''.
    (** [merge f m m'] creates a new map whose bindings belong to the ones
        of either [m] or [m']. The presence and value for a key [k] is
        determined by [f k e e'] where [e] and [e'] are the (optional)
        bindings of [k] in [m] and [m']. *)

  End Ops.
  Section Specs.

    Variable elt:Type.

    Parameter MapsTo : key -> elt -> t elt -> Prop.

    Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.

    Global Declare Instance MapsTo_compat :
      Proper (E.eq==>Logic.eq==>Logic.eq==>iff) MapsTo.

    Variable m m' : t elt.
    Variable x y : key.
    Variable e : elt.

    Parameter find_spec : find x m = Some e <-> MapsTo x e m.
    Parameter mem_spec : mem x m = true <-> In x m.
    Parameter empty_spec : find x (@empty elt) = None.
    Parameter is_empty_spec : is_empty m = true <-> forall x, find x m = None.
    Parameter add_spec1 : find x (add x e m) = Some e.
    Parameter add_spec2 : ~E.eq x y -> find y (add x e m) = find y m.
    Parameter remove_spec1 : find x (remove x m) = None.
    Parameter remove_spec2 : ~E.eq x y -> find y (remove x m) = find y m.

    (** Specification of [bindings] *)
    Parameter bindings_spec1 :
      InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
    (** When compared with ordered maps, here comes the only
        property that is really weaker: *)
    Parameter bindings_spec2w : NoDupA eq_key (bindings m).

    (** Specification of [cardinal] *)
    Parameter cardinal_spec : cardinal m = length (bindings m).

    (** Specification of [fold] *)
    Parameter fold_spec :
      forall {A} (i : A) (f : key -> elt -> A -> A),
      fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.

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

    Definition Equal (m m':t elt) := forall y, find y m = find y m'.
    Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
      (forall k, In k m <-> In k m') /\
      (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
    Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

    (** Specification of [equal] *)
    Parameter equal_spec : forall cmp : elt -> elt -> bool,
      equal cmp m m' = true <-> Equivb cmp m m'.

  End Specs.
  Section SpecMaps.

    Variables elt elt' elt'' : Type.

    Parameter map_spec : forall (f:elt->elt') m x,
      find x (map f m) = option_map f (find x m).

    Parameter mapi_spec : forall (f:key->elt->elt') m x,
      exists y:key, E.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).

    Parameter merge_spec1 :
      forall (f:key->option elt->option elt'->option elt'') m m' x,
      In x m \/ In x m' ->
      exists y:key, E.eq y x /\
                    find x (merge f m m') = f y (find x m) (find x m').

    Parameter merge_spec2 :
      forall (f:key -> option elt->option elt'->option elt'') m m' x,
      In x (merge f m m') -> In x m \/ In x m'.

  End SpecMaps.
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

  Definition lt_key {elt} (p p':key*elt) := E.lt (fst p) (fst p').

  (** Additional specification of [bindings] *)

  Parameter bindings_spec2 : forall {elt}(m : t elt), sort lt_key (bindings m).

  (** Remark: since [fold] is specified via [bindings], this stronger
   specification of [bindings] has an indirect impact on [fold],
   which can now be proved to receive bindings in increasing order. *)

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

  Include HasEq <+ HasLt <+ IsEq <+ IsStrOrder.

  Definition cmp e e' :=
    match Data.compare e e' with Eq => true | _ => false end.

  Parameter eq_spec : forall m m', eq m m' <-> Equivb cmp m m'.

  Parameter compare : t -> t -> comparison.

  Parameter compare_spec : forall m1 m2, CompSpec eq lt m1 m2 (compare m1 m2).

End Sord.


(* TODO: provides filter + partition *)

(* TODO: provide split
   Parameter split : key -> t elt -> t elt * option elt * t elt.

   Parameter split_spec k m :
     split k m = (filter (fun x -> E.compare x k) m, find k m, filter ...)

   min_binding, max_binding, choose ?
*)
