(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ

(** {6 Typing functions (not yet tagged as safe) }

    They return unsafe judgments that are "in context" of a set of
   (local) universe variables (the ones that appear in the term) and
   associated constraints. In case of polymorphic definitions, these
   variables and constraints will be generalized.

    When typechecking a term it may be updated to fix relevance marks.
   Do not discard the result. *)

val infer      : env -> constr       -> unsafe_judgment
val infer_hconstr : env -> HConstr.t -> unsafe_judgment
val infer_type : env -> types        -> unsafe_type_judgment

val check_context :
  env -> Constr.rel_context -> env * Constr.rel_context

(** {6 Basic operations of the typing machine. } *)

(** If [j] is the judgement {% $ %}c:t{% $ %}, then [assumption_of_judgement env j]
   returns the type {% $ %}c{% $ %}, checking that {% $ %}t{% $ %} is a sort. *)

val assumption_of_judgment :  env -> unsafe_judgment -> Sorts.relevance

(** {6 Type of sorts. } *)
val type1 : types
val type_of_sort : Sorts.t -> types

(** {6 Type of a bound variable. } *)
val type_of_relative : env -> int -> types

(** {6 Type of variables } *)
val type_of_variable : env -> variable -> types

(** {6 type of a constant } *)
val type_of_constant_in : env -> pconstant -> types

(** {6 type of an applied projection } *)
val type_of_projection : env -> Projection.t -> constr -> types -> Sorts.relevance * types

(** {6 Type of a product. } *)
val sort_of_product : env -> Sorts.t -> Sorts.t -> Sorts.t

(** {6 Type of a cast. } *)
val check_cast :
  env -> unsafe_judgment -> cast_kind -> unsafe_type_judgment -> unit

(** {6 Type of global references. } *)

val type_of_global_in_context : env -> GlobRef.t -> types * UVars.AbstractContext.t
(** Returns the type of the global reference, by creating a fresh
    instance of polymorphic references and computing their
    instantiated universe context. The type should not be used
    without pushing it's universe context in the environmnent of
    usage. For non-universe-polymorphic constants, it does not
    matter. *)

(** {6 Miscellaneous. } *)

(** Check that hyps are included in env and fails with error otherwise *)
val check_hyps_inclusion : env -> ?evars:CClosure.evar_handler ->
  GlobRef.t -> Constr.named_context -> unit

(** Types for primitives *)

val type_of_int : env -> types
val type_of_float : env -> types
val type_of_string : env -> types
val type_of_array : env -> UVars.Instance.t -> types
val type_of_prim_type : env -> UVars.Instance.t -> 'a CPrimitives.prim_type -> types
val type_of_prim : env -> UVars.Instance.t -> CPrimitives.t -> types
val type_of_prim_or_type : env -> UVars.Instance.t -> CPrimitives.op_or_type -> types

val should_invert_case : env -> Sorts.relevance -> case_info -> bool
(** Matches must be annotated with the indices when going from SProp to non SProp
    (implies 1 or 0 constructors). *)
