(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Here are collected some results about the type sumbool (see INIT/Specif.v)
   [sumbool A B], which is written [{A}+{B}], is the informative
   disjunction "A or B", where A and B are logical propositions.
   Its extraction is isomorphic to the type of booleans. *)

(** A boolean is either [true] or [false], and this is decidable *)

Require Import Logic Datatypes Specif.

Definition sumbool_of_bool (b : bool) : {b = true} + {b = false} :=
  if b return {b = true} + {b = false} then left eq_refl else right eq_refl.

#[global]
Hint Resolve sumbool_of_bool: bool.

Definition bool_eq_rec :
  forall (b:bool) (P:bool -> Set),
    (b = true -> P true) -> (b = false -> P false) -> P b :=
  fun b =>
    if b return forall P, (b = true -> P true) -> (b = false -> P false) -> P b
    then fun _ H _ => H eq_refl else fun _ _ H => H eq_refl.

Definition bool_eq_ind :
  forall (b:bool) (P:bool -> Prop),
    (b = true -> P true) -> (b = false -> P false) -> P b :=
  fun b =>
    if b return forall P, (b = true -> P true) -> (b = false -> P false) -> P b
    then fun _ H _ => H eq_refl else fun _ _ H => H eq_refl.

(** Logic connectives on type [sumbool] *)

Section connectives.

  Variables A B C D : Prop.

  Hypothesis H1 : {A} + {B}.
  Hypothesis H2 : {C} + {D}.

  Definition sumbool_and : {A /\ C} + {B \/ D} :=
    match H1, H2 with
    | left a, left c => left (conj a c)
    | left a, right d => right (or_intror d)
    | right b, left c => right (or_introl b)
    | right b, right d => right (or_intror d)
    end.

  Definition sumbool_or : {A \/ C} + {B /\ D} :=
    match H1, H2 with
    | left a, left c => left (or_intror c)
    | left a, right d => left (or_introl a)
    | right b, left c => left (or_intror c)
    | right b, right d => right (conj b d)
    end.

  Definition sumbool_not : {B} + {A} :=
    match H1 with
    | left a => right a
    | right b => left b
    end.

End connectives.

#[global]
Hint Resolve sumbool_and sumbool_or: core.
#[global]
Hint Immediate sumbool_not : core.

(** Any decidability function in type [sumbool] can be turned into a function
    returning a boolean with the corresponding specification: *)

Definition bool_of_sumbool (A B : Prop) :
    {A} + {B} -> {b : bool | if b then A else B} :=
  sumbool_rec _ (exist _ true) (exist _ false).
Arguments bool_of_sumbool : default implicits.
