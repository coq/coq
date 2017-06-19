(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Mod_subst
open Univ
open Entries

(** Operations concerning types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

(** {6 Arities} *)

val map_decl_arity : ('a -> 'c) -> ('b -> 'd) ->
  ('a, 'b) declaration_arity -> ('c, 'd) declaration_arity

(** {6 Constants} *)

val subst_const_body : substitution -> constant_body -> constant_body

(** Is there a actual body in const_body ? *)

val constant_has_body : constant_body -> bool

val constant_polymorphic_instance : constant_body -> universe_instance
val constant_polymorphic_context : constant_body -> universe_context

(** Is the constant polymorphic? *)
val constant_is_polymorphic : constant_body -> bool

(** Accessing const_body, forcing access to opaque proof term if needed.
    Only use this function if you know what you're doing. *)

val body_of_constant :
  Opaqueproof.opaquetab -> constant_body -> Term.constr option
val type_of_constant : constant_body -> constant_type
val constraints_of_constant :
  Opaqueproof.opaquetab -> constant_body -> Univ.constraints
val universes_of_constant :
  Opaqueproof.opaquetab -> constant_body -> Univ.universe_context

(** Return the universe context, in case the definition is polymorphic, otherwise
    the context is empty. *)

val universes_of_polymorphic_constant :
  Opaqueproof.opaquetab -> constant_body -> Univ.universe_context

val is_opaque : constant_body -> bool

(** Side effects *)

val string_of_side_effect : side_effect -> string

(** {6 Inductive types} *)

val eq_recarg : recarg -> recarg -> bool

val subst_recarg : substitution -> recarg -> recarg

val mk_norec : wf_paths
val mk_paths : recarg -> wf_paths list array -> wf_paths
val dest_recarg : wf_paths -> recarg
val dest_subterms : wf_paths -> wf_paths list array
val recarg_length : wf_paths -> int -> int

val subst_wf_paths : substitution -> wf_paths -> wf_paths

val subst_mind_body : substitution -> mutual_inductive_body -> mutual_inductive_body

val inductive_polymorphic_instance : mutual_inductive_body -> universe_instance
val inductive_polymorphic_context : mutual_inductive_body -> universe_context

(** Is the inductive polymorphic? *)
val inductive_is_polymorphic : mutual_inductive_body -> bool
(** Is the inductive cumulative? *)
val inductive_is_cumulative : mutual_inductive_body -> bool

(** {6 Kernel flags} *)

(** A default, safe set of flags for kernel type-checking *)
val safe_flags : typing_flags

(** {6 Hash-consing} *)

(** Here, strictly speaking, we don't perform true hash-consing
    of the structure, but simply hash-cons all inner constr
    and other known elements *)

val hcons_const_body : constant_body -> constant_body
val hcons_mind : mutual_inductive_body -> mutual_inductive_body
val hcons_module_body : module_body -> module_body
