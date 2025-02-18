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
open Univ
open UVars
open Declarations
open Mod_declarations

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

(** Linking information for the native compiler *)
type link_info =
  | Linked of string
  | NotLinked

type key = int CEphemeron.key option ref

type constant_key = constant_body * (link_info ref * key)

type mind_key = mutual_inductive_body * link_info ref

type named_context_val = private {
  env_named_ctx : Constr.named_context;
  env_named_map : Constr.named_declaration Id.Map.t;
  (** Identifier-indexed version of [env_named_ctx] *)
  env_named_idx : Constr.named_declaration Range.t;
  (** Same as env_named_ctx but with a fast-access list. *)
}

type rel_context_val = private {
  env_rel_ctx : Constr.rel_context;
  env_rel_map : Constr.rel_declaration Range.t;
}

type env
(** Type of global environments. *)

type rewrule_not_allowed = Symb | Rule
exception RewriteRulesNotAllowed of rewrule_not_allowed

val oracle : env -> Conv_oracle.oracle
val set_oracle : env -> Conv_oracle.oracle -> env

val eq_named_context_val : named_context_val -> named_context_val -> bool

val empty_env : env

val universes     : env -> UGraph.t
val qualities     : env -> Sorts.QVar.Set.t
val rel_context   : env -> Constr.rel_context
val rel_context_val : env -> rel_context_val
val named_context : env -> Constr.named_context
val named_context_val : env -> named_context_val

val set_universes : UGraph.t -> env -> env

val typing_flags    : env -> typing_flags
val is_impredicative_set : env -> bool
val type_in_type : env -> bool
val deactivated_guard : env -> bool
val indices_matter : env -> bool

val is_impredicative_sort : env -> Sorts.t -> bool
val is_impredicative_family : env -> Sorts.family -> bool

(** is the local context empty *)
val empty_context : env -> bool

(** {5 Context of de Bruijn variables ([rel_context]) } *)

val nb_rel           : env -> int
val push_rel         : Constr.rel_declaration -> env -> env
val push_rel_context : Constr.rel_context -> env -> env
val push_rec_types   : rec_declaration -> env -> env

val push_rel_context_val : Constr.rel_declaration -> rel_context_val -> rel_context_val
val set_rel_context_val : rel_context_val -> env -> env
val empty_rel_context_val : rel_context_val

(** Looks up in the context of local vars referred by indice ([rel_context])
   raises [Not_found] if the index points out of the context *)
val lookup_rel    : int -> env -> Constr.rel_declaration
val evaluable_rel : int -> env -> bool
val env_of_rel     : int -> env -> env

(** {6 Recurrence on [rel_context] } *)

val fold_rel_context :
  (env -> Constr.rel_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

(** {5 Context of variables (section variables and goal assumptions) } *)

val named_context_of_val : named_context_val -> Constr.named_context
val val_of_named_context : Constr.named_context -> named_context_val
val empty_named_context_val : named_context_val
val ids_of_named_context_val : named_context_val -> Id.Set.t


(** [map_named_val f ctxt] apply [f] to the body and the type of
   each declarations.
   *** /!\ ***   [f t] should be convertible with t, and preserve the name *)
val map_named_val :
   (named_declaration -> named_declaration) -> named_context_val -> named_context_val

val push_named : Constr.named_declaration -> env -> env
val push_named_context : Constr.named_context -> env -> env
val push_named_context_val  :
    Constr.named_declaration -> named_context_val -> named_context_val



(** Looks up in the context of local vars referred by names ([named_context])
   raises [Not_found] if the Id.t is not found *)

val lookup_named     : variable -> env -> Constr.named_declaration
val lookup_named_ctxt : variable -> named_context_val -> Constr.named_declaration
val evaluable_named  : variable -> env -> bool
val named_type : variable -> env -> types
val named_body : variable -> env -> constr option

(** {6 Recurrence on [named_context]: older declarations processed first } *)

val fold_named_context :
  (env -> Constr.named_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

val match_named_context_val : named_context_val -> (named_declaration * named_context_val) option

(** Recurrence on [named_context] starting from younger decl *)
val fold_named_context_reverse :
  ('a -> Constr.named_declaration -> 'a) -> init:'a -> env -> 'a

(** This forgets named and rel contexts *)
val reset_context : env -> env

(** This forgets rel context and sets a new named context *)
val reset_with_named_context : named_context_val -> env -> env

(** This removes the [n] last declarations from the rel context *)
val pop_rel_context : int -> env -> env

(** Useful for printing *)
val fold_constants : (Constant.t -> constant_body -> 'a -> 'a) -> env -> 'a -> 'a
val fold_inductives : (MutInd.t -> Declarations.mutual_inductive_body -> 'a -> 'a) -> env -> 'a -> 'a

(** {5 Global constants }
  {6 Add entries to global environment } *)

val add_constant : Constant.t -> constant_body -> env -> env
val add_constant_key : Constant.t -> constant_body -> link_info ->
  env -> env
val lookup_constant_key :  Constant.t -> env -> constant_key

(** Looks up in the context of global constant names
   raises an anomaly if the required path is not found *)
val lookup_constant    : Constant.t -> env -> constant_body
val evaluable_constant : Constant.t -> env -> bool
val constant_relevance : Constant.t -> env -> Sorts.relevance

val mem_constant : Constant.t -> env -> bool

val add_rewrite_rules : (Constant.t * rewrite_rule) list -> env -> env
val lookup_rewrite_rules : Constant.t -> env -> rewrite_rule list

(** New-style polymorphism *)
val polymorphic_constant  : Constant.t -> env -> bool
val polymorphic_pconstant : pconstant -> env -> bool
val type_in_type_constant : Constant.t -> env -> bool

(** {6 ... } *)
(** [constant_value env c] raises [NotEvaluableConst Opaque] if
   [c] is opaque, [NotEvaluableConst NoBody] if it has no
   body, [NotEvaluableConst IsProj] if [c] is a projection,
   [NotEvaluableConst (IsPrimitive p)] if [c] is primitive [p]
   and an anomaly if it does not exist in [env] *)

type const_evaluation_result =
  | NoBody
  | Opaque
  | IsPrimitive of Instance.t * CPrimitives.t
  | HasRules of Instance.t * bool * rewrite_rule list
exception NotEvaluableConst of const_evaluation_result

val constant_type : env -> Constant.t puniverses -> types constrained

val constant_value_and_type : env -> Constant.t puniverses ->
  constr option * types * Constraints.t
(** The universe context associated to the constant, empty if not
    polymorphic *)
val constant_context : env -> Constant.t -> AbstractContext.t

(* These functions should be called under the invariant that [env]
   already contains the constraints corresponding to the constant
   application. *)
val constant_value_in : env -> Constant.t puniverses -> constr
val constant_type_in : env -> Constant.t puniverses -> types
val constant_opt_value_in : env -> Constant.t puniverses -> constr option

val is_symbol : env -> Constant.t -> bool
val is_primitive : env -> Constant.t -> bool
val get_primitive : env -> Constant.t -> CPrimitives.t option

val is_array_type : env -> Constant.t -> bool
val is_int63_type : env -> Constant.t -> bool
val is_float64_type : env -> Constant.t -> bool
val is_string_type : env -> Constant.t -> bool
val is_primitive_type : env -> Constant.t -> bool


(** {6 Primitive projections} *)

(** Checks that the number of parameters is correct. *)
val lookup_projection : Names.Projection.t -> env -> Sorts.relevance * types

(** Anomaly when not a primitive record or invalid proj_arg. *)
val get_projection : env -> inductive -> proj_arg:int -> Names.Projection.Repr.t * Sorts.relevance

val get_projections : env -> inductive -> (Names.Projection.Repr.t * Sorts.relevance) array option

(** {5 Inductive types } *)
val lookup_mind_key : MutInd.t -> env -> mind_key
val add_mind_key : MutInd.t -> mind_key -> env -> env
val add_mind : MutInd.t -> mutual_inductive_body -> env -> env

(** Looks up in the context of global inductive names
   raises an anomaly if the required path is not found *)
val lookup_mind : MutInd.t -> env -> mutual_inductive_body

val mem_mind : MutInd.t -> env -> bool

val ind_relevance : inductive -> env -> Sorts.relevance

(** The universe context associated to the inductive, empty if not
    polymorphic *)
val mind_context : env -> MutInd.t -> AbstractContext.t

(** New-style polymorphism *)
val polymorphic_ind  : inductive -> env -> bool
val polymorphic_pind : pinductive -> env -> bool
val type_in_type_ind : inductive -> env -> bool

(** Old-style polymorphism *)
val template_polymorphic_ind : inductive -> env -> bool
val template_polymorphic_pind : pinductive -> env -> bool

(** {6 Changes of representation of Case nodes} *)

(** Given an inductive type and its parameters, builds the context of the return
    clause, including the inductive being eliminated. The additional binder
    array is only used to set the names of the context variables, we use the
    less general type to make it easy to use this function on Case nodes. *)
val expand_arity : Declarations.mind_specif -> pinductive -> constr array ->
  Name.t binder_annot array -> rel_context

(** Given an inductive type and its parameters, builds the context of the return
    clause, including the inductive being eliminated. The additional binder
    array is only used to set the names of the context variables, we use the
    less general type to make it easy to use this function on Case nodes. *)
val expand_branch_contexts : Declarations.mind_specif -> UVars.Instance.t -> constr array ->
  (Name.t binder_annot array * 'a) array -> rel_context array

(** [instantiate_context u subst nas ctx] applies both [u] and [subst]
  to [ctx] while replacing names using [nas] (order reversed). In particular,
  assumes that [ctx] and [nas] have the same length. *)
val instantiate_context : UVars.Instance.t -> Vars.substl -> Name.t binder_annot array ->
  rel_context -> rel_context


(** {6 Name quotients} *)

module type QNameS =
sig
  type t
  val equal : env -> t -> t -> bool
  val compare : env -> t -> t -> int
  val hash : env -> t -> int
  val canonize : env -> t -> t
end

module QConstant : QNameS with type t = Constant.t

module QMutInd : QNameS with type t = MutInd.t

module QInd : QNameS with type t = Ind.t

module QConstruct : QNameS with type t = Construct.t

module QProjection :
sig
  include QNameS with type t = Projection.t
  module Repr : QNameS with type t = Projection.Repr.t
end

module QGlobRef : QNameS with type t = GlobRef.t

(** {5 Modules } *)

val add_modtype : ModPath.t -> module_type_body -> env -> env

(** [shallow_add_module] does not add module components *)
val shallow_add_module : ModPath.t -> module_body -> env -> env

val lookup_module : ModPath.t -> env -> module_body
val lookup_modtype : ModPath.t -> env -> module_type_body

(** {5 Universe constraints } *)

val add_constraints : Constraints.t -> env -> env
(** Add universe constraints to the environment.
    @raise UniverseInconsistency. *)

val check_constraints : Constraints.t -> env -> bool
(** Check constraints are satifiable in the environment. *)

val push_context : ?strict:bool -> UContext.t -> env -> env
(** [push_context ?(strict=false) ctx env] pushes the universe context to the environment.
    @raise UGraph.AlreadyDeclared if one of the universes is already declared. *)

val push_context_set : ?strict:bool -> ContextSet.t -> env -> env
(** [push_context_set ?(strict=false) ctx env] pushes the universe
    context set to the environment. It does not fail even if one of the
    universes is already declared. *)

val push_qualities : Sorts.QVar.Set.t -> env -> env
(** Add the qualities to the environment. Only used in higher layers. *)

val push_subgraph : ContextSet.t -> env -> env
(** [push_subgraph univs env] adds the universes and constraints in
   [univs] to [env] as [push_context_set ~strict:false univs env], and
   also checks that they do not imply new transitive constraints
   between pre-existing universes in [env]. *)

val set_typing_flags : typing_flags -> env -> env
val set_impredicative_set : bool -> env -> env
val set_type_in_type : bool -> env -> env
val set_allow_sprop : bool -> env -> env
val sprop_allowed : env -> bool
val allow_rewrite_rules : env -> env
val rewrite_rules_allowed : env -> bool

val same_flags : typing_flags -> typing_flags -> bool

(** [update_typing_flags ?typing_flags] may update env with optional typing flags *)
val update_typing_flags : ?typing_flags:typing_flags -> env -> env

val universes_of_global : env -> GlobRef.t -> AbstractContext.t

(** {6 Sets of referred section variables }
   [global_vars_set env c] returns the list of [id]'s occurring either
   directly as [Var id] in [c] or indirectly as a section variable
   dependent in a global reference occurring in [c] *)

val global_vars_set : env -> constr -> Id.Set.t

val vars_of_global : env -> GlobRef.t -> Id.Set.t

(** closure of the input id set w.r.t. dependency *)
val really_needed : env -> Id.Set.t -> Id.Set.t

(** like [really_needed] but computes a well ordered named context *)
val keep_hyps : env -> Id.Set.t -> Constr.named_context

(** {5 Unsafe judgments. }
    We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type ('constr, 'types) punsafe_judgment = {
  uj_val : 'constr;
  uj_type : 'types }

val on_judgment       : ('a -> 'b) -> ('a, 'a) punsafe_judgment -> ('b, 'b) punsafe_judgment
val on_judgment_value : ('c -> 'c) -> ('c, 't) punsafe_judgment -> ('c, 't) punsafe_judgment
val on_judgment_type  : ('t -> 't) -> ('c, 't) punsafe_judgment -> ('c, 't) punsafe_judgment

type unsafe_judgment = (constr, types) punsafe_judgment

val make_judge : 'constr -> 'types -> ('constr, 'types) punsafe_judgment
val j_val  : ('constr, 'types) punsafe_judgment -> 'constr
val j_type : ('constr, 'types) punsafe_judgment -> 'types

type ('types, 'sorts) punsafe_type_judgment = {
  utj_val : 'types;
  utj_type : 'sorts }

type unsafe_type_judgment = (types, Sorts.t) punsafe_type_judgment

exception Hyp_not_found

(** [apply_to_hyp sign id f] split [sign] into [tail::(id,_,_)::head] and
   return [tail::(f head (id,_,_) (rev tail))::head].
   the value associated to id should not change *)
val apply_to_hyp : named_context_val -> variable ->
  (Constr.named_context -> Constr.named_declaration -> Constr.named_context -> Constr.named_declaration) ->
    named_context_val

val remove_hyps : Id.Set.t -> (Constr.named_declaration -> Constr.named_declaration) -> named_context_val -> named_context_val

val is_polymorphic : env -> Names.GlobRef.t -> bool
val is_template_polymorphic : env -> GlobRef.t -> bool
val is_type_in_type : env -> GlobRef.t -> bool

(** {5 VM and native} *)

val vm_library : env -> Vmlibrary.t
val set_vm_library : Vmlibrary.t -> env -> env
val link_vm_library : Vmlibrary.on_disk -> env -> env
val lookup_vm_code : Vmlibrary.index -> env -> Vmemitcodes.to_patch

(** Native compiler *)
val no_link_info : link_info

(** Primitives *)
val set_retroknowledge : env -> Retroknowledge.retroknowledge -> env
val retroknowledge : env -> Retroknowledge.retroknowledge

module Internal : sig
  (** Makes the qvars treated as above prop.
      Do not use outside kernel inductive typechecking. *)
  val push_template_context : UContext.t -> env -> env

  val is_above_prop : env -> Sorts.QVar.t -> bool

  module View :
  sig
    type t = {
      env_constants : constant_key Cmap_env.t;
      env_inductives : mind_key Mindmap_env.t;
      env_modules : module_body MPmap.t;
      env_modtypes : module_type_body MPmap.t;
      env_named_context : named_context_val;
      env_rel_context   : rel_context_val;
      env_universes : UGraph.t;
      env_qualities : Sorts.QVar.Set.t;
      env_symb_pats : rewrite_rule list Cmap_env.t;
      env_typing_flags  : typing_flags;
    }

    val view : env -> t
  end
  (** View type only used by Serlib. Do not use otherwise. *)

end
