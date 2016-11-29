(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constr

(** Monotonous state enforced by typing.

    This module allows to constrain uses of evarmaps in a monotonous fashion,
    and in particular statically suppress evar leaks and the like. To this
    ends, it defines a type of indexed evarmaps whose phantom typing ensures
    monotonous use.
*)

(** {5 Stages} *)

type ('a, 'b) le
(** Relationship stating that stage ['a] is anterior to stage ['b] *)

val refl : ('a, 'a) le
(** Reflexivity of anteriority *)

val cons : ('a, 'b) le -> ('b, 'c) le -> ('a, 'c) le
(** Transitivity of anteriority *)

val (+>) : ('a, 'b) le -> ('b, 'c) le -> ('a, 'c) le
(** Alias for {!cons} *)

(** {5 Monotonous evarmaps} *)

type 'r t
(** Stage-indexed evarmaps. This is just a plain evarmap with a phantom type. *)

type ('a, 'r) sigma = Sigma : 'a * 's t * ('r, 's) le -> ('a, 'r) sigma
(** Return values at a later stage *)

type 'r evar
(** Stage-indexed evars *)

(** {5 Constructors} *)

val here : 'a -> 'r t -> ('a, 'r) sigma
(** [here x s] is a shorthand for [Sigma (x, s, refl)] *)

(** {5 Postponing} *)

val lift_evar : 'r evar -> ('r, 's) le -> 's evar
(** Any evar existing at stage ['r] is also valid at any later stage. *)

(** {5 Downcasting} *)

val to_evar_map : 'r t -> Evd.evar_map
val to_evar : 'r evar -> Evar.t

(** {5 Monotonous API} *)

type 'r fresh = Fresh : 's evar * 's t * ('r, 's) le -> 'r fresh

val new_evar : 'r t -> ?name:Id.t ->
  Evd.evar_info -> 'r fresh

val define : 'r evar -> Constr.t -> 'r t -> (unit, 'r) sigma

(** Polymorphic universes *)

val new_univ_level_variable : ?loc:Loc.t -> ?name:string ->
  Evd.rigid -> 'r t -> (Univ.universe_level, 'r) sigma
val new_univ_variable : ?loc:Loc.t -> ?name:string ->
  Evd.rigid -> 'r t -> (Univ.universe, 'r) sigma
val new_sort_variable : ?loc:Loc.t -> ?name:string ->
  Evd.rigid -> 'r t -> (Sorts.t, 'r) sigma

val fresh_sort_in_family : ?loc:Loc.t -> ?rigid:Evd.rigid -> Environ.env ->
  'r t -> Term.sorts_family -> (Term.sorts, 'r) sigma
val fresh_constant_instance :
  ?loc:Loc.t -> Environ.env -> 'r t -> constant -> (pconstant, 'r) sigma
val fresh_inductive_instance :
  ?loc:Loc.t -> Environ.env -> 'r t -> inductive -> (pinductive, 'r) sigma
val fresh_constructor_instance : ?loc:Loc.t -> Environ.env -> 'r t -> constructor ->
  (pconstructor, 'r) sigma

val fresh_global : ?loc:Loc.t -> ?rigid:Evd.rigid -> ?names:Univ.Instance.t -> Environ.env ->
  'r t -> Globnames.global_reference -> (constr, 'r) sigma

(** FILLME *)

(** {5 Run} *)

type 'a run = { run : 'r. 'r t -> ('a, 'r) sigma }

val run : Evd.evar_map -> 'a run -> 'a * Evd.evar_map

(** {5 Imperative monotonic functions} *)

type evdref
(** Monotonic references over evarmaps *)

val apply : evdref -> 'a run -> 'a
(** Apply a monotonic function on a reference. *)

val purify : (evdref -> 'a) -> 'a run
(** Converse of {!apply}. *)

(** {5 Unsafe primitives} *)

module Unsafe :
sig
  val le : ('a, 'b) le
  val of_evar_map : Evd.evar_map -> 'r t
  val of_evar : Evd.evar -> 'r evar
  val of_ref : Evd.evar_map ref -> evdref
  val of_pair : ('a * Evd.evar_map) -> ('a, 'r) sigma
end

(** {5 Notations} *)

module Notations :
sig
  type ('a, 'r) sigma_ = ('a, 'r) sigma =
    Sigma : 'a * 's t * ('r, 's) le -> ('a, 'r) sigma_

  type 'a run_ = 'a run = { run : 'r. 'r t -> ('a, 'r) sigma }

  val (+>) : ('a, 'b) le -> ('b, 'c) le -> ('a, 'c) le
  (** Alias for {!cons} *)
end
