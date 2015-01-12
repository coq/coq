(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context
open Declarations
open Univ

(** Unsafe environments. We define here a datatype for environments.
   Since typing is not yet defined, it is not possible to check the
   informations added in environments, and that is why we speak here
   of ``unsafe'' environments. *)

(** Environments have the following components:
   - a context for de Bruijn variables
   - a context for de Bruijn variables vm values
   - a context for section variables and goal assumptions
   - a context for section variables and goal assumptions vm values
   - a context for global constants and axioms
   - a context for inductive definitions
   - a set of universe constraints
   - a flag telling if Set is, can be, or cannot be set impredicative *)




type env
val pre_env : env -> Pre_env.env
val env_of_pre_env : Pre_env.env -> env
val oracle : env -> Conv_oracle.oracle
val set_oracle : env -> Conv_oracle.oracle -> env

type named_context_val
val eq_named_context_val : named_context_val -> named_context_val -> bool

val empty_env : env

val universes     : env -> Univ.universes
val rel_context   : env -> rel_context
val named_context : env -> named_context
val named_context_val : env -> named_context_val

val opaque_tables : env -> Opaqueproof.opaquetab
val set_opaque_tables : env -> Opaqueproof.opaquetab -> env


val engagement    : env -> engagement option
val is_impredicative_set : env -> bool

val type_in_type  : env -> bool

(** is the local context empty *)
val empty_context : env -> bool

(** {5 Context of de Bruijn variables ([rel_context]) } *)

val nb_rel           : env -> int
val push_rel         : rel_declaration -> env -> env
val push_rel_context :     rel_context -> env -> env
val push_rec_types   : rec_declaration -> env -> env

(** Looks up in the context of local vars referred by indice ([rel_context]) 
   raises [Not_found] if the index points out of the context *)
val lookup_rel    : int -> env -> rel_declaration
val evaluable_rel : int -> env -> bool

(** {6 Recurrence on [rel_context] } *)

val fold_rel_context :
  (env -> rel_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

(** {5 Context of variables (section variables and goal assumptions) } *)

val named_context_of_val : named_context_val -> named_context
val named_vals_of_val : named_context_val -> Pre_env.named_vals
val val_of_named_context : named_context -> named_context_val
val empty_named_context_val : named_context_val


(** [map_named_val f ctxt] apply [f] to the body and the type of
   each declarations.
   *** /!\ ***   [f t] should be convertible with t *)
val map_named_val :
   (constr -> constr) -> named_context_val -> named_context_val

val push_named : named_declaration -> env -> env
val push_named_context : named_context -> env -> env
val push_named_context_val  :
    named_declaration -> named_context_val -> named_context_val



(** Looks up in the context of local vars referred by names ([named_context]) 
   raises [Not_found] if the Id.t is not found *)

val lookup_named     : variable -> env -> named_declaration
val lookup_named_val : variable -> named_context_val -> named_declaration
val evaluable_named  : variable -> env -> bool
val named_type : variable -> env -> types
val named_body : variable -> env -> constr option

(** {6 Recurrence on [named_context]: older declarations processed first } *)

val fold_named_context :
  (env -> named_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

(** Recurrence on [named_context] starting from younger decl *)
val fold_named_context_reverse :
  ('a -> named_declaration -> 'a) -> init:'a -> env -> 'a

(** This forgets named and rel contexts *)
val reset_context : env -> env

(** This forgets rel context and sets a new named context *)
val reset_with_named_context : named_context_val -> env -> env

(** This removes the [n] last declarations from the rel context *)
val pop_rel_context : int -> env -> env

(** {5 Global constants }
  {6 Add entries to global environment } *)

val add_constant : constant -> constant_body -> env -> env
val add_constant_key : constant -> constant_body -> Pre_env.link_info ->
  env -> env

(** Looks up in the context of global constant names 
   raises [Not_found] if the required path is not found *)
val lookup_constant    : constant -> env -> constant_body
val evaluable_constant : constant -> env -> bool

(** New-style polymorphism *)
val polymorphic_constant  : constant -> env -> bool
val polymorphic_pconstant : pconstant -> env -> bool

(** Old-style polymorphism *)
val template_polymorphic_constant  : constant -> env -> bool
val template_polymorphic_pconstant : pconstant -> env -> bool

(** {6 ... } *)
(** [constant_value env c] raises [NotEvaluableConst Opaque] if
   [c] is opaque and [NotEvaluableConst NoBody] if it has no
   body and [NotEvaluableConst IsProj] if [c] is a projection 
   and [Not_found] if it does not exist in [env] *)

type const_evaluation_result = NoBody | Opaque | IsProj
exception NotEvaluableConst of const_evaluation_result

val constant_value : env -> constant puniverses -> constr constrained
val constant_type : env -> constant puniverses -> constant_type constrained

val constant_opt_value : env -> constant puniverses -> (constr * Univ.constraints) option
val constant_value_and_type : env -> constant puniverses -> 
  constr option * constant_type * Univ.constraints
(** The universe context associated to the constant, empty if not 
    polymorphic *)
val constant_context : env -> constant -> Univ.universe_context

(* These functions should be called under the invariant that [env] 
   already contains the constraints corresponding to the constant 
   application. *)
val constant_value_in : env -> constant puniverses -> constr
val constant_type_in : env -> constant puniverses -> constant_type
val constant_opt_value_in : env -> constant puniverses -> constr option

(** {6 Primitive projections} *)

val lookup_projection    : Names.projection -> env -> projection_body
val is_projection : constant -> env -> bool

(** {5 Inductive types } *)
val add_mind_key : mutual_inductive -> Pre_env.mind_key -> env -> env
val add_mind : mutual_inductive -> mutual_inductive_body -> env -> env

(** Looks up in the context of global inductive names 
   raises [Not_found] if the required path is not found *)
val lookup_mind : mutual_inductive -> env -> mutual_inductive_body

(** New-style polymorphism *)
val polymorphic_ind  : inductive -> env -> bool
val polymorphic_pind : pinductive -> env -> bool

(** Old-style polymorphism *)
val template_polymorphic_ind : inductive -> env -> bool
val template_polymorphic_pind : pinductive -> env -> bool

(** {5 Modules } *)

val add_modtype : module_type_body -> env -> env

(** [shallow_add_module] does not add module components *)
val shallow_add_module : module_body -> env -> env

val lookup_module : module_path -> env -> module_body
val lookup_modtype : module_path -> env -> module_type_body

(** {5 Universe constraints } *)

(** Add universe constraints to the environment.
    @raises UniverseInconsistency
*)
val add_constraints : Univ.constraints -> env -> env

(** Check constraints are satifiable in the environment. *)
val check_constraints : Univ.constraints -> env -> bool
val push_context : Univ.universe_context -> env -> env
val push_context_set : Univ.universe_context_set -> env -> env
val push_constraints_to_env : 'a Univ.constrained -> env -> env

val set_engagement : engagement -> env -> env

val set_type_in_type : env -> env

(** {6 Sets of referred section variables }
   [global_vars_set env c] returns the list of [id]'s occurring either
   directly as [Var id] in [c] or indirectly as a section variable
   dependent in a global reference occurring in [c] *)

val global_vars_set : env -> constr -> Id.Set.t

(** the constr must be a global reference *)
val vars_of_global : env -> constr -> Id.Set.t

(** closure of the input id set w.r.t. dependency *)
val really_needed : env -> Id.Set.t -> Id.Set.t

(** like [really_needed] but computes a well ordered named context *)
val keep_hyps : env -> Id.Set.t -> section_context

(** {5 Unsafe judgments. }
    We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type unsafe_judgment = {
  uj_val  : constr;
  uj_type : types }

val make_judge : constr -> types -> unsafe_judgment
val j_val  : unsafe_judgment -> constr
val j_type : unsafe_judgment -> types

type unsafe_type_judgment = {
  utj_val  : constr;
  utj_type : sorts }


(** {6 Compilation of global declaration } *)

val compile_constant_body : env -> constant_def -> Cemitcodes.body_code

exception Hyp_not_found

(** [apply_to_hyp sign id f] split [sign] into [tail::(id,_,_)::head] and
   return [tail::(f head (id,_,_) (rev tail))::head].
   the value associated to id should not change *)
val apply_to_hyp : named_context_val -> variable ->
  (named_context -> named_declaration -> named_context -> named_declaration) ->
    named_context_val

(** [apply_to_hyp_and_dependent_on sign id f g] split [sign] into
   [tail::(id,_,_)::head] and
   return [(g tail)::(f (id,_,_))::head]. *)
val apply_to_hyp_and_dependent_on : named_context_val -> variable ->
  (named_declaration -> named_context_val -> named_declaration) ->
    (named_declaration -> named_context_val -> named_declaration) ->
      named_context_val

val insert_after_hyp : named_context_val -> variable ->
  named_declaration ->
    (named_context -> unit) -> named_context_val

val remove_hyps : Id.Set.t -> (named_declaration -> named_declaration) -> (Pre_env.lazy_val -> Pre_env.lazy_val) -> named_context_val -> named_context_val



open Retroknowledge
(** functions manipulating the retroknowledge 
    @author spiwack *)
val retroknowledge : (retroknowledge->'a) -> env -> 'a

val registered : env -> field -> bool

val register : env -> field -> Retroknowledge.entry -> env

(** Native compiler *)
val no_link_info : Pre_env.link_info
