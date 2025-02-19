(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Loc
open Names
open Constr
open Environ

(** This file defines the pervasive unification state used everywhere
    in Rocq tactic engine. It is very low-level and most of the
    functions exported here are irrelevant to the standard API user.
    Consider using {!Evarutil} or {!Proofview} instead.

    A unification state (of type [evar_map]) is primarily a finite mapping
    from existential variables to records containing the type of the evar
    ([evar_concl]), the context under which it was introduced ([evar_hyps])
    and its definition ([evar_body]). [evar_extra] is used to add any other
    kind of information.

    It also contains conversion constraints, debugging information and
    information about meta variables. *)

type econstr
type etypes = econstr
type esorts
type erelevance

(** {5 Existential variables and unification states} *)

(** {6 Evar filters} *)

module Filter :
sig
  type t
  (** Evar filters, seen as bitmasks. *)

  val equal : t -> t -> bool
  (** Equality over filters *)

  val identity : t
  (** The identity filter. *)

  val filter_list : t -> 'a list -> 'a list
  (** Filter a list. Sizes must coincide. *)

  val filter_array : t -> 'a array -> 'a array
  (** Filter an array. Sizes must coincide. *)

  val filter_slist : t  -> 'a SList.t -> 'a SList.t
  (** Filter a sparse list. Sizes must coincide. *)

  val extend : int -> t -> t
  (** [extend n f] extends [f] on the left with [n]-th times [true]. *)

  val compose : t -> t -> t
  (** Horizontal composition : [compose f1 f2] only keeps parts of [f2] where
      [f1] is set. In particular, [f1] and [f2] must have the same length. *)

  val apply_subfilter : t -> bool list -> t
  (** [apply_subfilter f1 f2] applies filter [f2] where [f1] is [true]. In
      particular, the length of [f2] is the number of times [f1] is [true] *)

  val restrict_upon : t -> int -> (int -> bool) -> t option
  (** Ad-hoc primitive. *)

  val map_along : (bool -> 'a -> bool) -> t -> 'a list -> t
  (** Apply the function on the filter and the list. Sizes must coincide. *)

  val make : bool list -> t
  (** Create out of a list *)

  val repr :  t -> bool list option
  (** Observe as a bool list. *)

end

module Abstraction : sig
  type abstraction =
    | Abstract
    | Imitate

  type t = abstraction list

  val identity : t

  val abstract_last : t -> t
end

(** {6 Evar infos} *)

type defined = [ `defined ]
type undefined = [ `undefined ]

type _ evar_body =
  | Evar_empty : undefined evar_body
  | Evar_defined : econstr -> defined evar_body

type 'a evar_info

type any_evar_info = EvarInfo : 'a evar_info -> any_evar_info

(** {6 Projections from evar infos} *)

val evar_concl : undefined evar_info -> econstr
(** Type of the evar. *)

val evar_context : 'a evar_info -> (econstr, etypes, erelevance) Context.Named.pt
(** Context of the evar. *)

val evar_hyps : 'a evar_info -> named_context_val
(** Context of the evar. *)

val evar_body : 'a evar_info -> 'a evar_body
(** Optional content of the evar. *)

val evar_candidates : undefined evar_info -> econstr list option
(** List of possible solutions when known that it is a finite list *)

val evar_source : 'a evar_info -> Evar_kinds.t located

val evar_filter : 'a evar_info -> Filter.t
(** Boolean mask over {!evar_hyps}. Should have the same length.
    When filtered out, the corresponding variable is not allowed to occur
    in the solution *)

val evar_abstract_arguments : undefined evar_info -> Abstraction.t
(** Boolean information over {!evar_hyps}, telling if an hypothesis instance
    can be imitated or should stay abstract in HO unification problems
    and inversion (see [second_order_matching_with_args] for its use). *)

val evar_relevance : 'a evar_info -> erelevance
(** Relevance of the conclusion of the evar. *)

(** {6 Derived projections} *)

val evar_filtered_context : 'a evar_info -> (econstr, etypes, erelevance) Context.Named.pt
val evar_filtered_hyps : 'a evar_info -> named_context_val
val evar_env : env -> 'a evar_info -> env
val evar_filtered_env : env -> 'a evar_info -> env
val evar_identity_subst : 'a evar_info -> econstr SList.t

val map_evar_body : (econstr -> econstr) -> 'a evar_body -> 'a evar_body
val map_evar_info : (econstr -> econstr) -> 'a evar_info -> 'a evar_info

(** {6 Unification state} **)

type evar_map
(** Type of unification state. Essentially a bunch of state-passing data needed
    to handle incremental term construction. *)

val empty : evar_map
(** The empty evar map. *)

val from_env : ?binders:lident list -> env -> evar_map
(** The empty evar map with given universe context, taking its initial
    universes from env, possibly with initial universe binders. This
    is the main entry point at the beginning of the process of
    interpreting a declaration (e.g. before entering the
    interpretation of a Theorem statement). *)

val from_ctx : UState.t -> evar_map
(** The empty evar map with given universe context. This is the main
    entry point when resuming from a already interpreted declaration
    (e.g.  after having interpreted a Theorem statement and preparing
    to open a goal). *)

val is_empty : evar_map -> bool
(** Whether an evarmap is empty. *)

val has_undefined : evar_map -> bool
(** [has_undefined sigma] is [true] if and only if
    there are uninstantiated evars in [sigma]. *)

val has_given_up : evar_map -> bool
(** [has_given_up sigma] is [true] if and only if
    there are given up evars in [sigma]. *)

val has_shelved : evar_map -> bool
(** [has_shelved sigma] is [true] if and only if
    there are shelved evars in [sigma]. *)

val new_pure_evar :
  ?src:Evar_kinds.t Loc.located -> ?filter:Filter.t ->
  relevance:erelevance ->
  ?abstract_arguments:Abstraction.t -> ?candidates:econstr list ->
  ?name:Id.t ->
  ?typeclass_candidate:bool ->
  named_context_val -> evar_map -> etypes -> evar_map * Evar.t
(** Low-level interface to create an evar.
  @param src User-facing source for the evar
  @param filter See {!Evd.Filter}, must be the same length as [named_context_val]
  @param name A name for the evar
  @param named_context_val The context of the evar
  @param types The type of conclusion of the evar
*)

val add : evar_map -> Evar.t -> 'a evar_info -> evar_map
(** [add sigma ev info] adds [ev] with evar info [info] in sigma.
    Precondition: ev must not preexist in [sigma]. *)

val find_defined : evar_map -> Evar.t -> defined evar_info option

val find : evar_map -> Evar.t -> any_evar_info
(** Recover the data associated to an evar. *)

val find_undefined : evar_map -> Evar.t -> undefined evar_info
(** Same as {!find} but restricted to undefined evars. For efficiency
    reasons. *)

val remove : evar_map -> Evar.t -> evar_map
(** Remove an evar from an evar map. Use with caution. *)

val undefine : evar_map -> Evar.t -> etypes -> evar_map [@@ocaml.deprecated]
(** Remove the body of an evar. Only there for backward compat, do not use. *)

val mem : evar_map -> Evar.t -> bool
(** Whether an evar is present in an evarmap. *)

val fold : (Evar.t -> any_evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
(** Apply a function to all evars and their associated info in an evarmap. *)

val fold_undefined : (Evar.t -> undefined evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
(** Same as {!fold}, but restricted to undefined evars. For efficiency
    reasons. *)

type map = { map : 'r. Evar.t -> 'r evar_info -> 'r evar_info }

val raw_map : map -> evar_map -> evar_map
(** Apply the given function to all evars in the map. Beware: this function
    expects the argument function to preserve the kind of [evar_body], i.e. it
    must send [Evar_empty] to [Evar_empty] and [Evar_defined c] to some
    [Evar_defined c']. *)

val raw_map_undefined : (Evar.t -> undefined evar_info -> undefined evar_info) -> evar_map -> evar_map
(** Same as {!raw_map}, but restricted to undefined evars. For efficiency
    reasons. *)

val define : Evar.t -> econstr -> evar_map -> evar_map
(** Set the body of an evar to the given constr. It is expected that:
    {ul
      {- The evar is already present in the evarmap.}
      {- The evar is not defined in the evarmap yet.}
      {- All the evars present in the constr should be present in the evar map.}
    } *)

val define_with_evar : Evar.t -> econstr -> evar_map -> evar_map
(** Same as [define ev body evd], except the body must be an existential variable [ev'].
    This additionally makes [ev'] inherit the [obligation] and [typeclass] flags of [ev]. *)

val cmap : (econstr -> econstr) -> evar_map -> evar_map
(** Map the function on all terms in the evar map. *)

val is_evar : evar_map -> Evar.t-> bool
(** Alias for {!mem}. *)

val is_defined : evar_map -> Evar.t-> bool
(** Whether an evar is defined in an evarmap. *)

val is_undefined : evar_map -> Evar.t-> bool
(** Whether an evar is not defined in an evarmap. *)

val add_constraints : evar_map -> Univ.Constraints.t -> evar_map
(** Add universe constraints in an evar map. *)

val add_quconstraints : evar_map -> Sorts.QUConstraints.t -> evar_map

val undefined_map : evar_map -> undefined evar_info Evar.Map.t
(** Access the undefined evar mapping directly. *)

val defined_map : evar_map -> defined evar_info Evar.Map.t
(** Access the defined evar mapping directly. *)

val drop_all_defined : evar_map -> evar_map

val drop_new_defined : original:evar_map -> evar_map -> evar_map
(** Drop the defined evars in the second evar map which did not exist in the first. *)

val is_maybe_typeclass_hook : (evar_map -> econstr -> bool) Hook.t

(** {6 Instantiating partial terms} *)

exception NotInstantiatedEvar

val existential_value : evar_map -> econstr pexistential -> econstr
(** [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
    no body and [Not_found] if it does not exist in [sigma] *)

val existential_type_opt : evar_map -> econstr pexistential -> etypes option

val existential_type : evar_map -> econstr pexistential -> etypes

val existential_opt_value : evar_map -> econstr pexistential -> econstr option
(** Same as {!existential_value} but returns an option instead of raising an
    exception. *)

val existential_opt_value0 : evar_map -> existential -> constr option

val evar_handler : evar_map -> CClosure.evar_handler

val existential_expand_value0 : evar_map -> existential -> constr CClosure.evar_expansion

val expand_existential : evar_map -> econstr pexistential -> econstr list
(** Returns the full evar instance with implicit default variables turned into
    explicit [Var] nodes. *)

val expand_existential0 : evar_map -> constr pexistential -> constr list

val instantiate_evar_array : evar_map -> 'a evar_info -> econstr -> econstr SList.t -> econstr

(** {6 Misc} *)

val restrict : Evar.t-> Filter.t -> ?candidates:econstr list ->
  ?src:Evar_kinds.t located -> evar_map -> evar_map * Evar.t
(** Restrict an undefined evar into a new evar by filtering context and
    possibly limiting the instances to a set of candidates (candidates
    are filtered according to the filter) *)

val update_source : evar_map -> Evar.t -> Evar_kinds.t located -> evar_map
(** To update the source a posteriori, e.g. when an evar type of
    another evar has to refer to this other evar, with a mutual dependency *)

val get_aliased_evars : evar_map -> Evar.t Evar.Map.t
(** The map of aliased evars *)

val is_aliased_evar : evar_map -> Evar.t -> Evar.t option
(** Tell if an evar has been aliased to another evar, and if yes, which *)

val max_undefined_with_candidates : evar_map -> Evar.t option
(** If any, the evar with highest id with a non-empty list of candidates. *)

val set_typeclass_evars : evar_map -> Evar.Set.t -> evar_map
(** Mark the given set of evars as available for resolution.
    (The previous marked set is replaced, not added to.)

    Precondition: they should indeed refer to undefined typeclass evars.
 *)

val get_typeclass_evars : evar_map -> Evar.Set.t
(** The set of undefined typeclass evars *)

val is_typeclass_evar : evar_map -> Evar.t -> bool
(** Is the evar declared resolvable for typeclass resolution *)

val get_obligation_evars : evar_map -> Evar.Set.t
(** The set of obligation evars *)

val set_obligation_evar : evar_map -> Evar.t -> evar_map
(** Declare an evar as an obligation *)

val is_obligation_evar : evar_map -> Evar.t -> bool
(** Is the evar declared as an obligation *)

val get_impossible_case_evars : evar_map -> Evar.Set.t
(** Set of undefined evars with ImpossibleCase evar source. *)

val downcast : Evar.t-> etypes -> evar_map -> evar_map
(** Change the type of an undefined evar to a new type assumed to be a
    subtype of its current type; subtyping must be ensured by caller *)

val evar_ident : Evar.t -> evar_map -> Id.t option

val rename : Evar.t -> Id.t -> evar_map -> evar_map

val evar_key : Id.t -> evar_map -> Evar.t

val evar_names : evar_map -> Nameops.Fresh.t

val dependent_evar_ident : Evar.t -> evar_map -> Id.t

(** {5 Side-effects} *)

type side_effect_role =
| Schema of inductive * string

type side_effects = {
  seff_private : Safe_typing.private_constants;
  seff_roles : side_effect_role Cmap.t;
}

val empty_side_effects : side_effects

val concat_side_effects : side_effects -> side_effects -> side_effects

val emit_side_effects : side_effects -> evar_map -> evar_map
(** Push a side-effect into the evar map. *)

val eval_side_effects : evar_map -> side_effects
(** Return the effects contained in the evar map. *)

val drop_side_effects : evar_map -> evar_map
(** This should not be used. For hacking purposes. *)

(** {5 Future goals} *)

val declare_future_goal : Evar.t -> evar_map -> evar_map
(** Adds an existential variable to the list of future goals. For
    internal uses only. *)

module FutureGoals : sig

  type t

  val comb : t -> Evar.t list

  val map_filter : (Evar.t -> Evar.t option) -> t -> t
  (** Applies a function on the future goals *)

  val filter : (Evar.t -> bool) -> t -> t
  (** Applies a filter on the future goals *)

end

val push_future_goals : evar_map -> evar_map

val pop_future_goals : evar_map -> FutureGoals.t * evar_map

val fold_future_goals : (evar_map -> Evar.t -> evar_map) -> evar_map -> evar_map

val remove_future_goal : evar_map -> Evar.t -> evar_map

val pr_future_goals_stack : evar_map -> Pp.t

val push_shelf : evar_map -> evar_map

val pop_shelf : evar_map -> Evar.t list * evar_map

val filter_shelf : (Evar.t -> bool) -> evar_map -> evar_map

val give_up : Evar.t -> evar_map -> evar_map

val shelve : evar_map -> Evar.t list -> evar_map

val unshelve : evar_map -> Evar.t list -> evar_map

val given_up : evar_map -> Evar.Set.t

val shelf : evar_map -> Evar.t list

val pr_shelf : evar_map -> Pp.t

(** {5 Sort variables}

    Evar maps also keep track of the universe constraints defined at a given
    point. This section defines the relevant manipulation functions. *)

exception UniversesDiffer

val add_universe_constraints : evar_map -> UnivProblem.Set.t -> evar_map
(** Add the given universe unification constraints to the evar map.
    @raise UniversesDiffer in case a first-order unification fails.
    @raise UniverseInconsistency .
*)

(** {5 Extra data}

  Evar maps can contain arbitrary data, allowing to use an extensible state.
  As evar maps are theoretically used in a strict state-passing style, such
  additional data should be passed along transparently. Some old and bug-prone
  code tends to drop them nonetheless, so you should keep cautious.

*)

module Store : Store.S
(** Datatype used to store additional information in evar maps. *)

val get_extra_data : evar_map -> Store.t
val set_extra_data : Store.t -> evar_map -> evar_map

(** {5 The state monad with state an evar map} *)

module MonadR : Monad.S with type +'a t = evar_map -> evar_map * 'a
module Monad  : Monad.S with type +'a t = evar_map -> 'a * evar_map

(** Unification constraints *)
type conv_pb = Conversion.conv_pb
type evar_constraint = conv_pb * env * econstr * econstr

(** The following two functions are for internal use only,
    see [Evarutil.add_unification_pb] for a safe interface. *)
val add_conv_pb : ?tail:bool -> evar_constraint -> evar_map -> evar_map
val conv_pbs : evar_map -> evar_constraint list

val extract_conv_pbs : evar_map ->
      (evar_constraint -> bool) ->
      evar_map * evar_constraint list
val extract_changed_conv_pbs : evar_map ->
      evar_map * evar_constraint list
val extract_changed_conv_pbs_from : evar_map -> Evar.Set.t option ->
      evar_map * evar_constraint list
val extract_all_conv_pbs : evar_map -> evar_map * evar_constraint list
val loc_of_conv_pb : evar_map -> evar_constraint -> Loc.t option

(** The following functions return the set of undefined evars
    contained in the object. *)

val evars_of_term : evar_map -> econstr -> Evar.Set.t
  (** including evars in instances of evars *)

val evars_of_named_context : evar_map -> (econstr, etypes, erelevance) Context.Named.pt -> Evar.Set.t

val evars_of_filtered_evar_info : evar_map -> 'a evar_info -> Evar.Set.t

(** {5 FIXME: Nothing to do here} *)

(*********************************************************
   Sort/universe variables *)

(** Rigid or flexible universe variables.

   [UnivRigid] variables are user-provided or come from an explicit
   [Type] in the source, we do not minimize them or unify them eagerly.

   [UnivFlexible alg] variables are fresh universe variables of
   polymorphic constants or generated during refinement, sometimes in
   algebraic position (i.e. not appearing in the term at the moment of
   creation). They are the candidates for minimization (if alg, to an
   algebraic universe) and unified eagerly in the first-order
   unification heurstic.  *)

type rigid = UState.rigid =
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

val univ_rigid : rigid
val univ_flexible : rigid
val univ_flexible_alg : rigid

type 'a in_ustate = 'a * UState.t

val restrict_universe_context : evar_map -> Univ.Level.Set.t -> evar_map

(** Raises Not_found if not a name for a universe in this map. *)
val universe_of_name : evar_map -> Id.t -> Univ.Level.t
val quality_of_name : evar_map -> Id.t -> Sorts.QVar.t

val is_rigid_qvar : evar_map -> Sorts.QVar.t -> bool

val is_relevance_irrelevant : evar_map -> erelevance -> bool
(** Whether the relevance is irrelevant modulo qstate *)
(* XXX move to ERelevance *)

val universe_binders : evar_map -> UnivNames.universe_binders

val new_univ_level_variable : ?loc:Loc.t -> ?name:Id.t -> rigid -> evar_map -> evar_map * Univ.Level.t
val new_quality_variable : ?loc:Loc.t -> ?name:Id.t -> evar_map -> evar_map * Sorts.QVar.t
val new_sort_variable : ?loc:Loc.t -> rigid -> evar_map -> evar_map * esorts

val add_forgotten_univ : evar_map -> Univ.Level.t -> evar_map

val universe_rigidity : evar_map -> Univ.Level.t -> rigid

val make_nonalgebraic_variable : evar_map -> Univ.Level.t -> evar_map
(** See [UState.make_nonalgebraic_variable]. *)

val is_flexible_level : evar_map -> Univ.Level.t -> bool

val normalize_universe_instance : evar_map -> UVars.Instance.t -> UVars.Instance.t

val set_leq_sort : evar_map -> esorts -> esorts -> evar_map
val set_eq_sort : evar_map -> esorts -> esorts -> evar_map
val set_eq_level : evar_map -> Univ.Level.t -> Univ.Level.t -> evar_map
val set_leq_level : evar_map -> Univ.Level.t -> Univ.Level.t -> evar_map
val set_eq_instances : ?flex:bool ->
  evar_map -> UVars.Instance.t -> UVars.Instance.t -> evar_map

val set_eq_qualities : evar_map -> Sorts.Quality.t -> Sorts.Quality.t -> evar_map
val set_above_prop : evar_map -> Sorts.Quality.t -> evar_map

val check_eq : evar_map -> esorts -> esorts -> bool
val check_leq : evar_map -> esorts -> esorts -> bool

val check_constraints : evar_map -> Univ.Constraints.t -> bool
val check_qconstraints : evar_map -> Sorts.QConstraints.t -> bool
val check_quconstraints : evar_map -> Sorts.QUConstraints.t -> bool

val ustate : evar_map -> UState.t
val evar_universe_context : evar_map -> UState.t [@@deprecated "(9.0) Use [Evd.ustate]"]

val universe_context_set : evar_map -> Univ.ContextSet.t
val sort_context_set : evar_map -> UnivGen.sort_context_set
val universe_subst : evar_map -> UnivFlex.t
val universes : evar_map -> UGraph.t

(** [to_universe_context evm] extracts the local universes and
    constraints of [evm] and orders the universes the same as
    [Univ.ContextSet.to_context]. *)
val to_universe_context : evar_map -> UVars.UContext.t

val univ_entry : poly:bool -> evar_map -> UState.named_universes_entry

val check_univ_decl : poly:bool -> evar_map -> UState.universe_decl -> UState.named_universes_entry

(** An early check of compatibility of the universe declaration before
    starting to build a declaration interactively *)
val check_univ_decl_early : poly:bool -> with_obls:bool -> evar_map -> UState.universe_decl -> Constr.t list -> unit

val merge_universe_context : evar_map -> UState.t -> evar_map
val set_universe_context : evar_map -> UState.t -> evar_map

val merge_context_set : ?loc:Loc.t -> ?sideff:bool -> rigid -> evar_map -> Univ.ContextSet.t -> evar_map

val merge_sort_context_set : ?loc:Loc.t -> ?sideff:bool -> rigid -> evar_map -> UnivGen.sort_context_set -> evar_map

val merge_sort_variables : ?loc:Loc.t -> ?sideff:bool -> evar_map -> Sorts.QVar.Set.t -> evar_map

val with_context_set : ?loc:Loc.t -> rigid -> evar_map -> 'a Univ.in_universe_context_set -> evar_map * 'a

val with_sort_context_set : ?loc:Loc.t -> rigid -> evar_map -> 'a UnivGen.in_sort_context_set -> evar_map * 'a

val nf_univ_variables : evar_map -> evar_map

val collapse_sort_variables : ?except:Sorts.QVar.Set.t -> evar_map -> evar_map

val fix_undefined_variables : evar_map -> evar_map

(** Universe minimization (collapse_sort_variables is true by default) *)
val minimize_universes : ?collapse_sort_variables:bool -> evar_map -> evar_map

(** Lift [UState.update_sigma_univs] *)
val update_sigma_univs : UGraph.t -> evar_map -> evar_map

(** Polymorphic universes *)

val fresh_sort_in_family : ?loc:Loc.t -> ?rigid:rigid
  -> evar_map -> Sorts.family -> evar_map * esorts
val fresh_constant_instance : ?loc:Loc.t -> ?rigid:rigid
  -> env -> evar_map -> Constant.t -> evar_map * pconstant
val fresh_inductive_instance : ?loc:Loc.t -> ?rigid:rigid
  -> env -> evar_map -> inductive -> evar_map * pinductive
val fresh_constructor_instance : ?loc:Loc.t -> ?rigid:rigid
  -> env -> evar_map -> constructor -> evar_map * pconstructor
val fresh_array_instance : ?loc:Loc.t -> ?rigid:rigid
  -> env -> evar_map  -> evar_map * UVars.Instance.t

val fresh_global : ?loc:Loc.t -> ?rigid:rigid -> ?names:UVars.Instance.t -> env ->
  evar_map -> GlobRef.t -> evar_map * econstr

(********************************************************************)
(* constr with holes and pending resolution of classes, conversion  *)
(* problems, candidates, etc.                                       *)

type open_constr = evar_map * econstr (* Special case when before is empty *)

(** Partially constructed constrs. *)

type unsolvability_explanation = SeveralInstancesFound of int
(** Failure explanation. *)

(** {5 Summary names} *)

(* This stuff is internal and should not be used. Currently a hack in
   the STM relies on it. *)
val evar_counter_summary_tag : int Summary.Dyn.tag

(** {5 Deprecated functions} *)
val create_evar_defs : evar_map -> evar_map
(* XXX: This is supposed to be deprecated by used by ssrmatching, what
   should the replacement be? *)

(** Create an [evar_map] with empty meta map: *)

(** Use this module only to bootstrap EConstr *)
module MiniEConstr : sig
  module ERelevance : sig
    type t = erelevance
    val make : Sorts.relevance -> t
    val kind : evar_map -> t -> Sorts.relevance
    val unsafe_to_relevance : t -> Sorts.relevance
  end

  module ESorts : sig
    type t = esorts
    val make : Sorts.t -> t
    val kind : evar_map -> t -> Sorts.t
    val unsafe_to_sorts : t -> Sorts.t
  end

  module EInstance : sig
    type t
    val make : UVars.Instance.t -> t
    val kind : evar_map -> t -> UVars.Instance.t
    val empty : t
    val is_empty : t -> bool
    val unsafe_to_instance : t -> UVars.Instance.t
  end

  type t = econstr

  val kind : evar_map -> t -> (t, t, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term
  val kind_upto : evar_map -> constr -> (constr, types, Sorts.t, UVars.Instance.t, Sorts.relevance) Constr.kind_of_term

  val whd_evar : evar_map -> t -> t

  val mkLEvar : evar_map -> Evar.t * t list -> t

  val replace_vars : evar_map -> (Id.t * t) list -> t -> t

  val of_kind : (t, t, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term -> t

  val of_constr : Constr.t -> t
  val of_constr_array : Constr.t array -> t array

  val to_constr : ?abort_on_undefined_evars:bool -> evar_map -> t -> Constr.t
  val to_constr_opt : evar_map -> t -> Constr.t option
  val nf_evar : evar_map -> t -> t

  val unsafe_to_constr : t -> Constr.t
  val unsafe_to_constr_array : t array -> Constr.t array

  val unsafe_eq : (t, Constr.t) eq
  val unsafe_relevance_eq : (ERelevance.t, Sorts.relevance) eq

  val of_named_decl : (Constr.t, Constr.types, Sorts.relevance) Context.Named.Declaration.pt ->
    (t, t, ERelevance.t) Context.Named.Declaration.pt
  val unsafe_to_named_decl : (t, t, ERelevance.t) Context.Named.Declaration.pt ->
    (Constr.t, Constr.types, Sorts.relevance) Context.Named.Declaration.pt
  val unsafe_to_rel_decl : (t, t, ERelevance.t) Context.Rel.Declaration.pt ->
    (Constr.t, Constr.types, Sorts.relevance) Context.Rel.Declaration.pt
  val of_case_invert : constr pcase_invert -> econstr pcase_invert
  val unsafe_to_case_invert : econstr pcase_invert -> constr pcase_invert
  val of_rel_decl : (Constr.t, Constr.types, Sorts.relevance) Context.Rel.Declaration.pt ->
    (t, t, ERelevance.t) Context.Rel.Declaration.pt

  val of_named_context : (Constr.t, Constr.types, Sorts.relevance) Context.Named.pt ->
    (t, t, ERelevance.t) Context.Named.pt
  val of_rel_context : (Constr.t, Constr.types, Sorts.relevance) Context.Rel.pt ->
    (t, t, ERelevance.t) Context.Rel.pt
end

(** Only used as EConstr internals *)
module Expand : sig
  open MiniEConstr
  type handle
  val empty_handle : handle
  val liftn_handle : int -> handle -> handle
  val kind : evar_map -> handle -> econstr -> handle * (econstr, econstr, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term
  val expand : evar_map -> handle -> econstr -> econstr
  val expand_instance : skip:bool -> undefined evar_info -> handle -> econstr SList.t -> econstr SList.t
end
