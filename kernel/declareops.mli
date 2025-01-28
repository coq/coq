(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Mod_subst
open UVars

(** Operations concerning types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

val universes_context : universes -> AbstractContext.t

val abstract_universes : Entries.universes_entry -> UVars.sort_level_subst * universes

(** {6 Constants} *)

val subst_const_body : substitution -> constant_body -> constant_body

(** Is there a actual body in const_body ? *)

val constant_has_body : ('a, 'b) pconstant_body -> bool

val constant_polymorphic_context : ('a, 'b) pconstant_body -> AbstractContext.t

(** Is the constant polymorphic? *)
val constant_is_polymorphic : ('a, 'b) pconstant_body -> bool

(** Return the universe context, in case the definition is polymorphic, otherwise
    the context is empty. *)

val is_opaque : ('a, 'b) pconstant_body -> bool

(** {6 Inductive types} *)

val eq_recarg : recarg -> recarg -> bool

val pr_recarg : recarg -> Pp.t
val pr_wf_paths : wf_paths -> Pp.t

val subst_recarg : substitution -> recarg -> recarg

val mk_norec : wf_paths
val mk_paths : recarg -> wf_paths list array -> wf_paths
val dest_recarg : wf_paths -> recarg
val dest_subterms : wf_paths -> wf_paths list array
val recarg_length : wf_paths -> int -> int

val subst_wf_paths : substitution -> wf_paths -> wf_paths

val subst_mind_body : substitution -> mutual_inductive_body -> mutual_inductive_body

val subst_rewrite_rules : substitution -> rewrite_rules_body -> rewrite_rules_body

val inductive_polymorphic_context : mutual_inductive_body -> AbstractContext.t

(** Is the inductive polymorphic? *)
val inductive_is_polymorphic : mutual_inductive_body -> bool
(** Is the inductive cumulative? *)
val inductive_is_cumulative : mutual_inductive_body -> bool

(** Anomaly when not a primitive record or invalid proj_arg *)
val inductive_make_projection : Names.inductive -> mutual_inductive_body -> proj_arg:int ->
  Names.Projection.Repr.t * Sorts.relevance

val inductive_make_projections : Names.inductive -> mutual_inductive_body ->
  (Names.Projection.Repr.t * Sorts.relevance) array option

(** {6 Kernel flags} *)

(** A default, safe set of flags for kernel type-checking *)
val safe_flags : Conv_oracle.oracle -> typing_flags

(** {6 Hash-consing} *)

(** Here, strictly speaking, we don't perform true hash-consing
    of the structure, but simply hash-cons all inner constr
    and other known elements *)

val hcons_const_body : ?hbody:(Constr.t -> Constr.t) ->
  ('a, 'b) pconstant_body -> ('a, 'b) pconstant_body
val hcons_mind : mutual_inductive_body -> mutual_inductive_body
