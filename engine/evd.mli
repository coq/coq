(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

(** This file defines the pervasive unification state used everywhere in Coq
    tactic engine. It is very low-level and most of the functions exported here
    are irrelevant to the standard API user. Consider using {!Evarutil},
    {!Sigma} or {!Proofview} instead.

    A unification state (of type [evar_map]) is primarily a finite mapping
    from existential variables to records containing the type of the evar
    ([evar_concl]), the context under which it was introduced ([evar_hyps])
    and its definition ([evar_body]). [evar_extra] is used to add any other
    kind of information.

    It also contains conversion constraints, debugging information and
    information about meta variables. *)

type econstr
type etypes = econstr

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

(** {6 Evar infos} *)

type evar_body =
  | Evar_empty
  | Evar_defined of econstr


module Store : Store.S
(** Datatype used to store additional information in evar maps. *)

type evar_info = {
  evar_concl : econstr;
  (** Type of the evar. *)
  evar_hyps : named_context_val; (** TODO econstr? *)
  (** Context of the evar. *)
  evar_body : evar_body;
  (** Optional content of the evar. *)
  evar_filter : Filter.t;
  (** Boolean mask over {!evar_hyps}. Should have the same length.
      When filtered out, the corresponding variable is not allowed to occur
      in the solution *)
  evar_source : Evar_kinds.t located;
  (** Information about the evar. *)
  evar_candidates : econstr list option;
  (** List of possible solutions when known that it is a finite list *)
  evar_extra : Store.t
  (** Extra store, used for clever hacks. *)
}

val make_evar : named_context_val -> etypes -> evar_info
val evar_concl : evar_info -> econstr
val evar_context : evar_info -> (econstr, etypes) Context.Named.pt
val evar_filtered_context : evar_info -> (econstr, etypes) Context.Named.pt
val evar_hyps : evar_info -> named_context_val
val evar_filtered_hyps : evar_info -> named_context_val
val evar_body : evar_info -> evar_body
val evar_candidates : evar_info -> constr list option
val evar_filter : evar_info -> Filter.t
val evar_env :  evar_info -> env
val evar_filtered_env :  evar_info -> env

val map_evar_body : (econstr -> econstr) -> evar_body -> evar_body
val map_evar_info : (econstr -> econstr) -> evar_info -> evar_info

(** {6 Unification state} **)

type evar_map
(** Type of unification state. Essentially a bunch of state-passing data needed
    to handle incremental term construction. *)

val empty : evar_map
(** The empty evar map. *)

val from_env : env -> evar_map
(** The empty evar map with given universe context, taking its initial 
    universes from env. *)

val from_ctx : UState.t -> evar_map
(** The empty evar map with given universe context *)

val is_empty : evar_map -> bool
(** Whether an evarmap is empty. *)

val has_undefined : evar_map -> bool
(** [has_undefined sigma] is [true] if and only if
    there are uninstantiated evars in [sigma]. *)

val new_evar : evar_map ->
  ?name:Id.t -> evar_info -> evar_map * Evar.t
(** Creates a fresh evar mapping to the given information. *)

val add : evar_map -> Evar.t -> evar_info -> evar_map
(** [add sigma ev info] adds [ev] with evar info [info] in sigma.
    Precondition: ev must not preexist in [sigma]. *)

val find : evar_map -> Evar.t -> evar_info
(** Recover the data associated to an evar. *)

val find_undefined : evar_map -> Evar.t -> evar_info
(** Same as {!find} but restricted to undefined evars. For efficiency
    reasons. *)

val remove : evar_map -> Evar.t -> evar_map
(** Remove an evar from an evar map. Use with caution. *)

val mem : evar_map -> Evar.t -> bool
(** Whether an evar is present in an evarmap. *)

val fold : (Evar.t -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
(** Apply a function to all evars and their associated info in an evarmap. *)

val fold_undefined : (Evar.t -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
(** Same as {!fold}, but restricted to undefined evars. For efficiency
    reasons. *)

val raw_map : (Evar.t -> evar_info -> evar_info) -> evar_map -> evar_map
(** Apply the given function to all evars in the map. Beware: this function
    expects the argument function to preserve the kind of [evar_body], i.e. it
    must send [Evar_empty] to [Evar_empty] and [Evar_defined c] to some
    [Evar_defined c']. *)

val raw_map_undefined : (Evar.t -> evar_info -> evar_info) -> evar_map -> evar_map
(** Same as {!raw_map}, but restricted to undefined evars. For efficiency
    reasons. *)

val define : Evar.t-> econstr -> evar_map -> evar_map
(** Set the body of an evar to the given constr. It is expected that:
    {ul
      {- The evar is already present in the evarmap.}
      {- The evar is not defined in the evarmap yet.}
      {- All the evars present in the constr should be present in the evar map.}
    } *)

val cmap : (econstr -> econstr) -> evar_map -> evar_map
(** Map the function on all terms in the evar map. *)

val is_evar : evar_map -> Evar.t-> bool
(** Alias for {!mem}. *)

val is_defined : evar_map -> Evar.t-> bool
(** Whether an evar is defined in an evarmap. *)

val is_undefined : evar_map -> Evar.t-> bool
(** Whether an evar is not defined in an evarmap. *)

val add_constraints : evar_map -> Univ.Constraint.t -> evar_map
(** Add universe constraints in an evar map. *)

val undefined_map : evar_map -> evar_info Evar.Map.t
(** Access the undefined evar mapping directly. *)

val drop_all_defined : evar_map -> evar_map

(** {6 Instantiating partial terms} *)

exception NotInstantiatedEvar

val existential_value : evar_map -> econstr pexistential -> econstr
(** [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
    no body and [Not_found] if it does not exist in [sigma] *)

val existential_value0 : evar_map -> existential -> constr

val existential_type : evar_map -> econstr pexistential -> etypes

val existential_type0 : evar_map -> existential -> types

val existential_opt_value : evar_map -> econstr pexistential -> econstr option
(** Same as {!existential_value} but returns an option instead of raising an
    exception. *)

val existential_opt_value0 : evar_map -> existential -> constr option

val evar_instance_array : (Constr.named_declaration -> 'a -> bool) -> evar_info ->
  'a array -> (Id.t * 'a) list

val instantiate_evar_array : evar_info -> econstr -> econstr array -> econstr

val evars_reset_evd  : ?with_conv_pbs:bool -> ?with_univs:bool -> 
  evar_map ->  evar_map -> evar_map
(** spiwack: this function seems to somewhat break the abstraction. *)

(** {6 Misc} *)

val restrict : Evar.t-> Filter.t -> ?candidates:econstr list ->
  ?src:Evar_kinds.t located -> evar_map -> evar_map * Evar.t
(** Restrict an undefined evar into a new evar by filtering context and
    possibly limiting the instances to a set of candidates (candidates
    are filtered according to the filter) *)

val is_restricted_evar : evar_info -> Evar.t option
(** Tell if an evar comes from restriction of another evar, and if yes, which *)

val downcast : Evar.t-> etypes -> evar_map -> evar_map
(** Change the type of an undefined evar to a new type assumed to be a
    subtype of its current type; subtyping must be ensured by caller *)

val evar_source : Evar.t -> evar_map -> Evar_kinds.t located
(** Convenience function. Wrapper around {!find} to recover the source of an
    evar in a given evar map. *)

val evar_ident : Evar.t -> evar_map -> Id.t option

val rename : Evar.t -> Id.t -> evar_map -> evar_map

val evar_key : Id.t -> evar_map -> Evar.t

val evar_source_of_meta : metavariable -> evar_map -> Evar_kinds.t located

val dependent_evar_ident : Evar.t -> evar_map -> Id.t

(** {5 Side-effects} *)

val emit_side_effects : Safe_typing.private_constants -> evar_map -> evar_map
(** Push a side-effect into the evar map. *)

val eval_side_effects : evar_map -> Safe_typing.private_constants
(** Return the effects contained in the evar map. *)

val drop_side_effects : evar_map -> evar_map
(** This should not be used. For hacking purposes. *)

(** {5 Future goals} *)

type goal_kind = ToShelve | ToGiveUp

val declare_future_goal : ?tag:goal_kind -> Evar.t -> evar_map -> evar_map
(** Adds an existential variable to the list of future goals. For
    internal uses only. *)

val declare_principal_goal : ?tag:goal_kind -> Evar.t -> evar_map -> evar_map
(** Adds an existential variable to the list of future goals and make
    it principal. Only one existential variable can be made principal, an
    error is raised otherwise. For internal uses only. *)

val future_goals : evar_map -> Evar.t list
(** Retrieves the list of future goals. Used by the [refine] primitive
    of the tactic engine. *)

val principal_future_goal : evar_map -> Evar.t option
(** Retrieves the name of the principal existential variable if there
    is one. Used by the [refine] primitive of the tactic engine. *)

type future_goals

val save_future_goals : evar_map -> future_goals
(** Retrieves the list of future goals including the principal future
    goal. Used by the [refine] primitive of the tactic engine. *)

val reset_future_goals : evar_map -> evar_map
(** Clears the list of future goals (as well as the principal future
    goal). Used by the [refine] primitive of the tactic engine. *)

val restore_future_goals : evar_map -> future_goals -> evar_map
(** Sets the future goals (including the principal future goal) to a
    previous value. Intended to be used after a local list of future
    goals has been consumed. Used by the [refine] primitive of the
    tactic engine. *)

val fold_future_goals : (evar_map -> Evar.t -> evar_map) -> evar_map -> future_goals -> evar_map
(** Fold future goals *)

val map_filter_future_goals : (Evar.t -> Evar.t option) -> future_goals -> future_goals
(** Applies a function on the future goals *)

val filter_future_goals : (Evar.t -> bool) -> future_goals -> future_goals
(** Applies a filter on the future goals *)

val dispatch_future_goals : future_goals -> Evar.t list * Evar.t list * Evar.t list * Evar.t option
(** Returns the future_goals dispatched into regular, shelved, given_up
   goals; last argument is the goal tagged as principal if any *)

val extract_given_up_future_goals : future_goals -> Evar.t list * Evar.t list
(** An ad hoc variant for Proof.proof; not for general use *)

val shelve_on_future_goals : Evar.t list -> future_goals -> future_goals
(** Push goals on the shelve of future goals *)

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

val get_extra_data : evar_map -> Store.t
val set_extra_data : Store.t -> evar_map -> evar_map

(** {5 Enriching with evar maps} *)

type 'a sigma = {
  it : 'a ;
  (** The base object. *)
  sigma : evar_map
  (** The added unification state. *)
}
(** The type constructor ['a sigma] adds an evar map to an object of type
    ['a]. *)

val sig_it  : 'a sigma -> 'a
val sig_sig : 'a sigma -> evar_map
val on_sig : 'a sigma -> (evar_map -> evar_map * 'b) -> 'a sigma * 'b

(** {5 The state monad with state an evar map} *)

module MonadR : Monad.S with type +'a t = evar_map -> evar_map * 'a
module Monad  : Monad.S with type +'a t = evar_map -> 'a * evar_map

(** {5 Meta machinery}

    These functions are almost deprecated. They were used before the
    introduction of the full-fledged evar calculus. In an ideal world, they
    should be removed. Alas, some parts of the code still use them. Do not use
    in newly-written code. *)

module Metaset : Set.S with type elt = metavariable
module Metamap : Map.ExtS with type key = metavariable and module Set := Metaset

type 'a freelisted = {
  rebus : 'a;
  freemetas : Metaset.t }

val metavars_of : econstr -> Metaset.t
val mk_freelisted : econstr -> econstr freelisted
val map_fl : ('a -> 'b) -> 'a freelisted -> 'b freelisted

(** Status of an instance found by unification wrt to the meta it solves:
  - a supertype of the meta (e.g. the solution to ?X <= T is a supertype of ?X)
  - a subtype of the meta (e.g. the solution to T <= ?X is a supertype of ?X)
  - a term that can be eta-expanded n times while still being a solution
    (e.g. the solution [P] to [?X u v = P u v] can be eta-expanded twice)
*)

type instance_constraint = IsSuperType | IsSubType | Conv

val eq_instance_constraint :
  instance_constraint -> instance_constraint -> bool

(** Status of the unification of the type of an instance against the type of
     the meta it instantiates:
   - CoerceToType means that the unification of types has not been done
     and that a coercion can still be inserted: the meta should not be
     substituted freely (this happens for instance given via the
     "with" binding clause).
   - TypeProcessed means that the information obtainable from the
     unification of types has been extracted.
   - TypeNotProcessed means that the unification of types has not been
     done but it is known that no coercion may be inserted: the meta
     can be substituted freely.
*)

type instance_typing_status =
    CoerceToType | TypeNotProcessed | TypeProcessed

(** Status of an instance together with the status of its type unification *)

type instance_status = instance_constraint * instance_typing_status

(** Clausal environments *)

type clbinding =
  | Cltyp of Name.t * econstr freelisted
  | Clval of Name.t * (econstr freelisted * instance_status) * econstr freelisted

(** Unification constraints *)
type conv_pb = Reduction.conv_pb
type evar_constraint = conv_pb * env * econstr * econstr

(** The following two functions are for internal use only,
    see [Evarutil.add_unification_pb] for a safe interface. *)
val add_conv_pb : ?tail:bool -> evar_constraint -> evar_map -> evar_map
val conv_pbs : evar_map -> evar_constraint list

val extract_changed_conv_pbs : evar_map ->
      (Evar.Set.t -> evar_constraint -> bool) ->
      evar_map * evar_constraint list
val extract_all_conv_pbs : evar_map -> evar_map * evar_constraint list
val loc_of_conv_pb : evar_map -> evar_constraint -> Loc.t option

(** The following functions return the set of evars immediately
    contained in the object; need the term to be evar-normal otherwise
    defined evars are returned too. *)

val evars_of_term : constr -> Evar.Set.t
  (** including evars in instances of evars *)

val evars_of_named_context : (econstr, etypes) Context.Named.pt -> Evar.Set.t

val evars_of_filtered_evar_info : evar_info -> Evar.Set.t

(** Metas *)
val meta_list : evar_map -> (metavariable * clbinding) list
val meta_defined : evar_map -> metavariable -> bool

val meta_value     : evar_map -> metavariable -> econstr
(** [meta_fvalue] raises [Not_found] if meta not in map or [Anomaly] if
   meta has no value *)

val meta_fvalue    : evar_map -> metavariable -> econstr freelisted * instance_status
val meta_opt_fvalue : evar_map -> metavariable -> (econstr freelisted * instance_status) option
val meta_type      : evar_map -> metavariable -> etypes
val meta_type0 : evar_map -> metavariable -> types
val meta_ftype     : evar_map -> metavariable -> etypes freelisted
val meta_name      : evar_map -> metavariable -> Name.t
val meta_declare   :
  metavariable -> etypes -> ?name:Name.t -> evar_map -> evar_map
val meta_assign    : metavariable -> econstr * instance_status -> evar_map -> evar_map
val meta_reassign  : metavariable -> econstr * instance_status -> evar_map -> evar_map

val clear_metas : evar_map -> evar_map

(** [meta_merge evd1 evd2] returns [evd2] extended with the metas of [evd1] *)
val meta_merge : ?with_univs:bool -> evar_map -> evar_map -> evar_map

val undefined_metas : evar_map -> metavariable list
val map_metas_fvalue : (econstr -> econstr) -> evar_map -> evar_map
val map_metas : (econstr -> econstr) -> evar_map -> evar_map

type metabinding = metavariable * econstr * instance_status

val retract_coercible_metas : evar_map -> metabinding list * evar_map

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

type 'a in_evar_universe_context = 'a * UState.t

val restrict_universe_context : evar_map -> Univ.LSet.t -> evar_map
(** Raises Not_found if not a name for a universe in this map. *)
val universe_of_name : evar_map -> Id.t -> Univ.Level.t

val universe_binders : evar_map -> UnivNames.universe_binders

val new_univ_level_variable : ?loc:Loc.t -> ?name:Id.t -> rigid -> evar_map -> evar_map * Univ.Level.t
val new_univ_variable : ?loc:Loc.t -> ?name:Id.t -> rigid -> evar_map -> evar_map * Univ.Universe.t
val new_sort_variable : ?loc:Loc.t -> ?name:Id.t -> rigid -> evar_map -> evar_map * Sorts.t

val add_global_univ : evar_map -> Univ.Level.t -> evar_map

val universe_rigidity : evar_map -> Univ.Level.t -> rigid
val make_flexible_variable : evar_map -> algebraic:bool -> Univ.Level.t -> evar_map
(** See [UState.make_flexible_variable] *)

val is_sort_variable : evar_map -> Sorts.t -> Univ.Level.t option 
(** [is_sort_variable evm s] returns [Some u] or [None] if [s] is 
    not a local sort variable declared in [evm] *)
val is_flexible_level : evar_map -> Univ.Level.t -> bool

(* val normalize_universe_level : evar_map -> Univ.Level.t -> Univ.Level.t *)
val normalize_universe : evar_map -> Univ.Universe.t -> Univ.Universe.t
val normalize_universe_instance : evar_map -> Univ.Instance.t -> Univ.Instance.t

val set_leq_sort : env -> evar_map -> Sorts.t -> Sorts.t -> evar_map
val set_eq_sort : env -> evar_map -> Sorts.t -> Sorts.t -> evar_map
val set_eq_level : evar_map -> Univ.Level.t -> Univ.Level.t -> evar_map
val set_leq_level : evar_map -> Univ.Level.t -> Univ.Level.t -> evar_map
val set_eq_instances : ?flex:bool -> 
  evar_map -> Univ.Instance.t -> Univ.Instance.t -> evar_map

val check_eq : evar_map -> Univ.Universe.t -> Univ.Universe.t -> bool
val check_leq : evar_map -> Univ.Universe.t -> Univ.Universe.t -> bool

val check_constraints : evar_map -> Univ.Constraint.t -> bool

val evar_universe_context : evar_map -> UState.t
val universe_context_set : evar_map -> Univ.ContextSet.t
val universe_subst : evar_map -> UnivSubst.universe_opt_subst
val universes : evar_map -> UGraph.t

(** [to_universe_context evm] extracts the local universes and
    constraints of [evm] and orders the universes the same as
    [Univ.ContextSet.to_context]. *)
val to_universe_context : evar_map -> Univ.UContext.t

val const_univ_entry : poly:bool -> evar_map -> Entries.constant_universes_entry

(** NB: [ind_univ_entry] cannot create cumulative entries. *)
val ind_univ_entry : poly:bool -> evar_map -> Entries.inductive_universes

val check_univ_decl : poly:bool -> evar_map -> UState.universe_decl -> Entries.constant_universes_entry

val merge_universe_context : evar_map -> UState.t -> evar_map
val set_universe_context : evar_map -> UState.t -> evar_map

val merge_context_set : ?loc:Loc.t -> ?sideff:bool -> rigid -> evar_map -> Univ.ContextSet.t -> evar_map
val merge_universe_subst : evar_map -> UnivSubst.universe_opt_subst -> evar_map

val with_context_set : ?loc:Loc.t -> rigid -> evar_map -> 'a Univ.in_universe_context_set -> evar_map * 'a

val nf_univ_variables : evar_map -> evar_map * Univ.universe_subst

val fix_undefined_variables : evar_map -> evar_map

val refresh_undefined_universes : evar_map -> evar_map * Univ.universe_level_subst

(** Universe minimization *)
val minimize_universes : evar_map -> evar_map

val update_sigma_env : evar_map -> env -> evar_map

(** Polymorphic universes *)

val fresh_sort_in_family : ?loc:Loc.t -> ?rigid:rigid -> evar_map -> Sorts.family -> evar_map * Sorts.t
val fresh_constant_instance : ?loc:Loc.t -> env -> evar_map -> Constant.t -> evar_map * pconstant
val fresh_inductive_instance : ?loc:Loc.t -> env -> evar_map -> inductive -> evar_map * pinductive
val fresh_constructor_instance : ?loc:Loc.t -> env -> evar_map -> constructor -> evar_map * pconstructor

val fresh_global : ?loc:Loc.t -> ?rigid:rigid -> ?names:Univ.Instance.t -> env ->
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
  module ESorts : sig
    type t
    val make : Sorts.t -> t
    val kind : evar_map -> t -> Sorts.t
    val unsafe_to_sorts : t -> Sorts.t
  end

  module EInstance : sig
    type t
    val make : Univ.Instance.t -> t
    val kind : evar_map -> t -> Univ.Instance.t
    val empty : t
    val is_empty : t -> bool
    val unsafe_to_instance : t -> Univ.Instance.t
  end

  type t = econstr

  val kind : evar_map -> t -> (t, t, ESorts.t, EInstance.t) Constr.kind_of_term
  val kind_upto : evar_map -> constr -> (constr, types, Sorts.t, Univ.Instance.t) Constr.kind_of_term
  val kind_of_type : evar_map -> t -> (t, t) Term.kind_of_type

  val whd_evar : evar_map -> t -> t

  val of_kind : (t, t, ESorts.t, EInstance.t) Constr.kind_of_term -> t

  val of_constr : Constr.t -> t

  val to_constr : ?abort_on_undefined_evars:bool -> evar_map -> t -> Constr.t

  val unsafe_to_constr : t -> Constr.t

  val unsafe_eq : (t, Constr.t) eq

  val of_named_decl : (Constr.t, Constr.types) Context.Named.Declaration.pt ->
    (t, t) Context.Named.Declaration.pt
  val unsafe_to_named_decl : (t, t) Context.Named.Declaration.pt ->
    (Constr.t, Constr.types) Context.Named.Declaration.pt
  val unsafe_to_rel_decl : (t, t) Context.Rel.Declaration.pt ->
    (Constr.t, Constr.types) Context.Rel.Declaration.pt
  val of_rel_decl : (Constr.t, Constr.types) Context.Rel.Declaration.pt ->
    (t, t) Context.Rel.Declaration.pt
  val to_rel_decl : evar_map -> (t, t) Context.Rel.Declaration.pt ->
    (Constr.t, Constr.types) Context.Rel.Declaration.pt
end
