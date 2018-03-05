(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

Definition sumbool_of_bool : forall b:bool, {b = true} + {b = false}.
  destruct b; auto.
Defined.

Hint Resolve sumbool_of_bool: bool.

Definition bool_eq_rec :
  forall (b:bool) (P:bool -> Set),
    (b = true -> P true) -> (b = false -> P false) -> P b.
  destruct b; auto.
Defined.

Definition bool_eq_ind :
  forall (b:bool) (P:bool -> Prop),
    (b = true -> P true) -> (b = false -> P false) -> P b.
  destruct b; auto.
Defined.


(** Logic connectives on type [sumbool] *)

Section connectives.

  Variables A B C D : Prop.

  Hypothesis H1 : {A} + {B}.
  Hypothesis H2 : {C} + {D}.

  Definition sumbool_and : {A /\ C} + {B \/ D}.
    case H1; case H2; auto.
  Defined.

  Definition sumbool_or : {A \/ C} + {B /\ D}.
    case H1; case H2; auto.
  Defined.

  Definition sumbool_not : {B} + {A}.
    case H1; auto.
  Defined.

End connectives.

Hint Resolve sumbool_and sumbool_or: core.
Hint Immediate sumbool_not : core.

(** Any decidability function in type [sumbool] can be turned into a function
    returning a boolean with the corresponding specification: *)

Definition bool_of_sumbool :
  forall A B:Prop, {A} + {B} -> {b : bool | if b then A else B}.
  intros A B H.
  elim H; intro; [exists true | exists false]; assumption.
Defined.
Arguments bool_of_sumbool : default implicits.
