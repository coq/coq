(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Mod_subst
open Univ
open Context

(** Operations concerning types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

(** {6 Arities} *)

val map_decl_arity : ('a -> 'c) -> ('b -> 'd) ->
  ('a, 'b) declaration_arity -> ('c, 'd) declaration_arity

(** {6 Constants} *)

val subst_const_body : substitution -> constant_body -> constant_body

(** Is there a actual body in const_body ? *)

val constant_has_body : constant_body -> bool

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

type side_effects
val no_seff : side_effects
val iter_side_effects : (side_effect -> unit) -> side_effects -> unit
val fold_side_effects : ('a -> side_effect -> 'a) -> 'a -> side_effects -> 'a
val uniquize_side_effects : side_effects -> side_effects
val union_side_effects : side_effects -> side_effects -> side_effects
val flatten_side_effects : side_effects list -> side_effects
val side_effects_of_list : side_effect list -> side_effects
val cons_side_effects : side_effect -> side_effects -> side_effects
val side_effects_is_empty : side_effects -> bool

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

val inductive_instance : mutual_inductive_body -> universe_instance
val inductive_context : mutual_inductive_body -> universe_context

(** {6 Hash-consing} *)

(** Here, strictly speaking, we don't perform true hash-consing
    of the structure, but simply hash-cons all inner constr
    and other known elements *)

val hcons_const_body : constant_body -> constant_body
val hcons_mind : mutual_inductive_body -> mutual_inductive_body
