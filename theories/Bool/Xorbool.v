(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Here are collected some results about the type xorbool (see INIT/Specif.v)
   [xorbool A B], which is written [{A}(+){B}], is the informative
   disjunction "A or B", where A and B are logical propositions.
   Its extraction is isomorphic to the type of booleans. *)

(** A boolean is either [true] or [false], and this is decidable *)

Definition xorbool_of_bool : forall b:bool, {b = true} (+) {b = false}.
  destruct b; firstorder.
Defined.

Hint Resolve xorbool_of_bool: bool.

(** Logic connectives on type [xorbool] *)

Section connectives.

  Variables A B C D : Prop.

  Hypothesis H1 : {A} (+) {B}.
  Hypothesis H2 : {C} (+) {D}.

  Definition xorbool_and : {A /\ C} (+) {B \/ D}.
    case H1; case H2; firstorder.
  Defined.

  Definition xorbool_or : {A \/ C} (+) {B /\ D}.
    case H1; case H2; firstorder.
  Defined.

  Definition xorbool_not : {B} (+) {A}.
    case H1; firstorder.
  Defined.

End connectives.

Hint Resolve xorbool_and xorbool_or: core.
Hint Immediate xorbool_not : core.

(** Any decidability function in type [xorbool] can be turned into a function
    returning a boolean with the corresponding specification: *)

Definition sumbool_of_xorbool {A B} (x : {A} (+) {B}) : {A} + {B} :=
  match x with
    | left a => left (proj1 a)
    | right a => right (proj2 a)
  end.

Definition xorbool_of_sumbool {A} (x : {A} + {~A}) : {A} (+) {~A} :=
  match x with
    | left a => left (conj a (fun nota => nota a))
    | right a => right (conj a a)
  end.

Definition bool_of_xorbool :
  forall A B:Prop, {A} (+) {B} -> {b : bool | if b then A else B}.
  intros A B H.
  elim H; intro; [exists true; apply a | exists false; apply b].
Defined.
Arguments bool_of_xorbool : default implicits.
