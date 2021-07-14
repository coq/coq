(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Univ
open Environ

(** {6 Typing functions (not yet tagged as safe) }

    They return unsafe judgments that are "in context" of a set of
   (local) universe variables (the ones that appear in the term) and
   associated constraints. In case of polymorphic definitions, these
   variables and constraints will be generalized.

    When typechecking a term it may be updated to fix relevance marks.
   Do not discard the result. *)

val infer      : env -> constr       -> unsafe_judgment
val infer_type : env -> types        -> unsafe_type_judgment

val check_context :
  env -> Constr.rel_context -> env * Constr.rel_context

(** {6 Basic operations of the typing machine. } *)

(** If [j] is the judgement {% $ %}c:t{% $ %}, then [assumption_of_judgement env j]
   returns the type {% $ %}c{% $ %}, checking that {% $ %}t{% $ %} is a sort. *)

val assumption_of_judgment :  env -> unsafe_judgment -> Sorts.relevance
val type_judgment          :  env -> unsafe_judgment -> unsafe_type_judgment

val check_binder_annot : Sorts.t -> Name.t Context.binder_annot -> Name.t Context.binder_annot

(** {6 Type of sorts. } *)
val type1 : types
val type_of_sort : Sorts.t -> types
val judge_of_prop : unsafe_judgment
val judge_of_set  : unsafe_judgment
val judge_of_type           : Universe.t -> unsafe_judgment

(** {6 Type of a bound variable. } *)
val type_of_relative : env -> int -> types
val judge_of_relative : env -> int -> unsafe_judgment

(** {6 Type of variables } *)
val type_of_variable : env -> variable -> types
val judge_of_variable : env -> variable -> unsafe_judgment

(** {6 type of a constant } *)
val type_of_constant_in : env -> pconstant -> types
val judge_of_constant : env -> pconstant -> unsafe_judgment

(** {6 type of an applied projection } *)
val judge_of_projection : env -> Projection.t -> unsafe_judgment -> unsafe_judgment

(** {6 Type of application. } *)
val judge_of_apply :
  env -> unsafe_judgment -> unsafe_judgment array
    -> unsafe_judgment

(** {6 Type of an abstraction. } *)
(* val judge_of_abstraction : *)
(*   env -> Name.t -> unsafe_type_judgment -> unsafe_judgment *)
(*     -> unsafe_judgment *)

(** {6 Type of a product. } *)
val sort_of_product : env -> Sorts.t -> Sorts.t -> Sorts.t
val type_of_product : env -> Name.t Context.binder_annot -> Sorts.t -> Sorts.t -> types
(* val judge_of_product : *)
(*   env -> Name.t -> unsafe_type_judgment -> unsafe_type_judgment *)
(*     -> unsafe_judgment *)

(** s Type of a let in. *)
(* val judge_of_letin : *)
(*   env -> Name.t -> unsafe_judgment -> unsafe_type_judgment -> unsafe_judgment *)
(*     -> unsafe_judgment *)

(** {6 Type of a cast. } *)
val judge_of_cast :
  env -> unsafe_judgment -> cast_kind -> unsafe_type_judgment ->
  unsafe_judgment

(** {6 Inductive types. } *)
val judge_of_inductive : env -> inductive puniverses -> unsafe_judgment
val judge_of_constructor : env -> constructor puniverses -> unsafe_judgment

(** {6 Type of global references. } *)

val type_of_global_in_context : env -> GlobRef.t -> types * Univ.AbstractContext.t
(** Returns the type of the global reference, by creating a fresh
    instance of polymorphic references and computing their
    instantiated universe context. The type should not be used
    without pushing it's universe context in the environmnent of
    usage. For non-universe-polymorphic constants, it does not
    matter. *)

(** {6 Miscellaneous. } *)

(** Check that hyps are included in env and fails with error otherwise *)
val check_hyps_inclusion : env -> ?evars:(existential->constr option) ->
  GlobRef.t -> Constr.named_context -> unit

(** Types for primitives *)

val type_of_int : env -> types
val judge_of_int : env -> Uint63.t -> unsafe_judgment

val type_of_float : env -> types
val judge_of_float : env -> Float64.t -> unsafe_judgment

val type_of_array : env -> Univ.Instance.t -> types
val judge_of_array : env -> Univ.Instance.t -> unsafe_judgment array -> unsafe_judgment -> unsafe_judgment

val type_of_prim_type : env -> Univ.Instance.t -> 'a CPrimitives.prim_type -> types
val type_of_prim : env -> Univ.Instance.t -> CPrimitives.t -> types
val type_of_prim_or_type : env -> Univ.Instance.t -> CPrimitives.op_or_type -> types

val warn_bad_relevance_name : string
(** Allow the checker to make this warning into an error. *)

val should_invert_case : env -> case_info -> bool
(** We have case inversion exactly when going from irrelevant nonempty
   (ie 1 constructor) inductive to relevant type. *)
