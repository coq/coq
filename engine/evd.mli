(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Loc
open Names
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

(** {5 Existential variables and unification states} *)

type evar = Evar.t
[@@ocaml.deprecated "use Evar.t"]
(** Existential variables. *)

(** {6 Evars} *)
val string_of_existential : Evar.t -> string
[@@ocaml.deprecated "use Evar.print"]

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

type 'a evar_body =
  | Evar_empty
  | Evar_defined of 'a

module Store : Store.S
(** Datatype used to store additional information in evar maps. *)

type 'a evar_ginfo = {
  evar_concl : 'a;
  (** Type of the evar. *)
  evar_hyps : named_context_val;
  (** Context of the evar. *)
  evar_body : 'a evar_body;
  (** Optional content of the evar. *)
  evar_filter : Filter.t;
  (** Boolean mask over {!evar_hyps}. Should have the same length.
      When filtered out, the corresponding variable is not allowed to occur
      in the solution *)
  evar_source : Evar_kinds.t located;
  (** Information about the evar. *)
  evar_candidates : 'a list option;
  (** List of possible solutions when known that it is a finite list *)
  evar_extra : Store.t
  (** Extra store, used for clever hacks. *)
}

val make_evar : named_context_val -> 'a -> 'a evar_ginfo
val evar_concl : 'a evar_ginfo -> 'a
val evar_context : 'a evar_ginfo -> Context.Named.t
val evar_filtered_context : 'a evar_ginfo -> Context.Named.t
val evar_hyps : 'a evar_ginfo -> named_context_val
val evar_filtered_hyps : 'a evar_ginfo -> named_context_val
val evar_body : 'a evar_ginfo -> 'a evar_body
val evar_filter : 'a evar_ginfo -> Filter.t
val evar_env :  'a evar_ginfo -> env
val evar_filtered_env :  'a evar_ginfo -> env

val map_evar_body : ('a -> 'a) -> 'a evar_body -> 'a evar_body
val map_evar_info : (Constr.t -> Constr.t) -> Constr.t evar_ginfo -> Constr.t evar_ginfo

(** {6 Unification state} **)

type evar_universe_context = UState.t
[@@ocaml.deprecated "Alias of UState.t"]
(** The universe context associated to an evar map *)

type 'a evar_gmap
(** Type of unification state. Essentially a bunch of state-passing data needed
    to handle incremental term construction. *)

val empty : 'a evar_gmap
(** The empty evar map. *)

val from_env : env -> 'a evar_gmap
(** The empty evar map with given universe context, taking its initial
    universes from env. *)

val from_ctx : UState.t -> 'a evar_gmap
(** The empty evar map with given universe context *)

val is_empty : 'a evar_gmap -> bool
(** Whether an evarmap is empty. *)

val has_undefined : 'a evar_gmap -> bool
(** [has_undefined sigma] is [true] if and only if
    there are uninstantiated evars in [sigma]. *)

val new_evar : 'a evar_gmap ->
  ?name:Id.t -> 'a evar_ginfo -> 'a evar_gmap * Evar.t
(** Creates a fresh evar mapping to the given information. *)

val add : 'a evar_gmap -> Evar.t -> 'a evar_ginfo -> 'a evar_gmap
(** [add sigma ev info] adds [ev] with evar info [info] in sigma.
    Precondition: ev must not preexist in [sigma]. *)

val find : 'a evar_gmap -> Evar.t -> 'a evar_ginfo
(** Recover the data associated to an evar. *)

val find_undefined : 'a evar_gmap -> Evar.t -> 'a evar_ginfo
(** Same as {!find} but restricted to undefined evars. For efficiency
    reasons. *)

val remove : 'a evar_gmap -> Evar.t -> 'a evar_gmap
(** Remove an evar from an evar map. Use with caution. *)

val mem : 'a evar_gmap -> Evar.t -> bool
(** Whether an evar is present in an evarmap. *)

val fold : (Evar.t -> 'a evar_ginfo -> 'b -> 'b) -> 'a evar_gmap -> 'b -> 'b
(** Apply a function to all evars and their associated info in an evarmap. *)

val fold_undefined : (Evar.t -> 'a evar_ginfo -> 'b -> 'b) -> 'a evar_gmap -> 'b -> 'b
(** Same as {!fold}, but restricted to undefined evars. For efficiency
    reasons. *)

val raw_map : (Evar.t -> 'a evar_ginfo -> 'a evar_ginfo) -> 'a evar_gmap -> 'a evar_gmap
(** Apply the given function to all evars in the map. Beware: this function
    expects the argument function to preserve the kind of [evar_body], i.e. it
    must send [Evar_empty] to [Evar_empty] and [Evar_defined c] to some
    [Evar_defined c']. *)

val raw_map_undefined : (Evar.t -> 'a evar_ginfo -> 'a evar_ginfo) -> 'a evar_gmap -> 'a evar_gmap
(** Same as {!raw_map}, but restricted to undefined evars. For efficiency
    reasons. *)

val define : Evar.t-> 'a -> 'a evar_gmap -> 'a evar_gmap
(** Set the body of an evar to the given constr. It is expected that:
    {ul
      {- The evar is already present in the evarmap.}
      {- The evar is not defined in the evarmap yet.}
      {- All the evars present in the constr should be present in the evar map.}
    } *)

val cmap : (Constr.t -> Constr.t) -> Constr.t evar_gmap -> Constr.t evar_gmap
(** Map the function on all terms in the evar map. *)

val is_evar : 'a evar_gmap -> Evar.t-> bool
(** Alias for {!mem}. *)

val is_defined : 'a evar_gmap -> Evar.t-> bool
(** Whether an evar is defined in an evarmap. *)

val is_undefined : 'a evar_gmap -> Evar.t-> bool
(** Whether an evar is not defined in an evarmap. *)

val add_constraints : 'a evar_gmap -> Univ.Constraint.t -> 'a evar_gmap
(** Add universe constraints in an evar map. *)

val undefined_map : 'a evar_gmap -> 'a evar_ginfo Evar.Map.t
(** Access the undefined evar mapping directly. *)

val drop_all_defined : 'a evar_gmap -> 'a evar_gmap

(** {6 Instantiating partial terms} *)

exception NotInstantiatedEvar

type 'a gexistential = Evar.t * 'a array
val existential_value : Constr.t evar_gmap -> Constr.t gexistential -> Constr.t
(** [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
    no body and [Not_found] if it does not exist in [sigma] *)

val existential_type : Constr.t evar_gmap -> Constr.t gexistential -> Constr.t

val existential_opt_value : Constr.t evar_gmap -> Constr.t gexistential -> Constr.t option
(** Same as {!existential_value} but returns an option instead of raising an
    exception. *)

val evar_instance_array : (Context.Named.Declaration.t -> 'a -> bool) -> 'b evar_ginfo ->
  'a array -> (Id.t * 'a) list

val instantiate_evar_array : Constr.t evar_ginfo -> Constr.t -> Constr.t array -> Constr.t

val evars_reset_evd  : ?with_conv_pbs:bool -> ?with_univs:bool ->
  'a evar_gmap -> 'a evar_gmap -> 'a evar_gmap
(** spiwack: this function seems to somewhat break the abstraction. *)

(** {6 Misc} *)

val restrict : Evar.t -> Filter.t -> ?candidates:Constr.t list ->
  ?src:Evar_kinds.t located -> Constr.t evar_gmap -> Constr.t evar_gmap * Evar.t
(** Restrict an undefined evar into a new evar by filtering context and
    possibly limiting the instances to a set of candidates *)

val is_restricted_evar : 'a evar_ginfo -> Evar.t option
(** Tell if an evar comes from restriction of another evar, and if yes, which *)

val downcast : Evar.t-> 'a -> 'a evar_gmap -> 'a evar_gmap
(** Change the type of an undefined evar to a new type assumed to be a
    subtype of its current type; subtyping must be ensured by caller *)

val evar_source : Evar.t -> 'a evar_gmap -> Evar_kinds.t located
(** Convenience function. Wrapper around {!find} to recover the source of an
    evar in a given evar map. *)

val evar_ident : Evar.t -> 'a evar_gmap -> Id.t option

val rename : Evar.t -> Id.t -> 'a evar_gmap -> 'a evar_gmap

val evar_key : Id.t -> 'a evar_gmap -> Evar.t

val evar_source_of_meta : Constr.metavariable -> 'a evar_gmap -> Evar_kinds.t located

val dependent_evar_ident : Evar.t -> 'a evar_gmap -> Id.t

(** {5 Side-effects} *)

val emit_side_effects : Safe_typing.private_constants -> 'a evar_gmap -> 'a evar_gmap
(** Push a side-effect into the evar map. *)

val eval_side_effects : 'a evar_gmap -> Safe_typing.private_constants
(** Return the effects contained in the evar map. *)

val drop_side_effects : 'a evar_gmap -> 'a evar_gmap
(** This should not be used. For hacking purposes. *)

(** {5 Future goals} *)

val declare_future_goal : Evar.t -> 'a evar_gmap -> 'a evar_gmap
(** Adds an existential variable to the list of future goals. For
    internal uses only. *)

val declare_principal_goal : Evar.t -> 'a evar_gmap -> 'a evar_gmap
(** Adds an existential variable to the list of future goals and make
    it principal. Only one existential variable can be made principal, an
    error is raised otherwise. For internal uses only. *)

val future_goals : 'a evar_gmap -> Evar.t list
(** Retrieves the list of future goals. Used by the [refine] primitive
    of the tactic engine. *)

val principal_future_goal : 'a evar_gmap -> Evar.t option
(** Retrieves the name of the principal existential variable if there
    is one. Used by the [refine] primitive of the tactic engine. *)

val reset_future_goals : 'a evar_gmap -> 'a evar_gmap
(** Clears the list of future goals (as well as the principal future
    goal). Used by the [refine] primitive of the tactic engine. *)

val restore_future_goals : 'a evar_gmap -> Evar.t list -> Evar.t option -> 'a evar_gmap
(** Sets the future goals (including the principal future goal) to a
    previous value. Intended to be used after a local list of future
    goals has been consumed. Used by the [refine] primitive of the
    tactic engine. *)

(** {5 Sort variables}

    Evar maps also keep track of the universe constraints defined at a given
    point. This section defines the relevant manipulation functions. *)

val whd_sort_variable : 'a evar_gmap -> 'a -> 'a

exception UniversesDiffer

val add_universe_constraints : 'a evar_gmap -> Universes.Constraints.t -> 'a evar_gmap
(** Add the given universe unification constraints to the evar map.
    @raises UniversesDiffer in case a first-order unification fails.
    @raises UniverseInconsistency
*)

(** {5 Extra data}

  Evar maps can contain arbitrary data, allowing to use an extensible state.
  As evar maps are theoretically used in a strict state-passing style, such
  additional data should be passed along transparently. Some old and bug-prone
  code tends to drop them nonetheless, so you should keep cautious.

*)

val get_extra_data : 'a evar_gmap -> Store.t
val set_extra_data : Store.t -> 'a evar_gmap -> 'a evar_gmap

(** {5 Enriching with evar maps} *)

type ('a,'b) gsigma = {
  it : 'a ;
  (** The base object. *)
  sigma : 'b evar_gmap
  (** The added unification state. *)
}
(** The type constructor ['a sigma] adds an evar map to an object of type
    ['a]. *)

val sig_it  : ('a,'b) gsigma -> 'a
val sig_sig : ('a,'b) gsigma -> 'b evar_gmap
val on_sig  : ('a,'b) gsigma -> ('b evar_gmap -> 'b evar_gmap * 'c) -> ('a,'b) gsigma * 'c

(** {5 The state monad with state an evar map} *)

module MonadR : Monad.S with type +'a t = Constr.t evar_gmap -> Constr.t evar_gmap * 'a
module Monad  : Monad.S with type +'a t = Constr.t evar_gmap -> 'a * Constr.t evar_gmap

(** {5 Meta machinery}

    These functions are almost deprecated. They were used before the
    introduction of the full-fledged evar calculus. In an ideal world, they
    should be removed. Alas, some parts of the code still use them. Do not use
    in newly-written code. *)

module Metaset : Set.S with type elt = Constr.metavariable
module Metamap : Map.ExtS with type key = Constr.metavariable and module Set := Metaset

type 'a freelisted = {
  rebus : 'a;
  freemetas : Metaset.t }

val metavars_of : Constr.t -> Metaset.t
val mk_freelisted : Constr.t -> Constr.t freelisted
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
  | Cltyp of Name.t * Constr.t freelisted
  | Clval of Name.t * (Constr.t freelisted * instance_status) * Constr.t freelisted

(** Unification constraints *)
type conv_pb = Reduction.conv_pb
type 'a evar_gconstraint = conv_pb * env * 'a * 'a
val add_conv_pb : ?tail:bool -> 'a evar_gconstraint -> 'a evar_gmap -> 'a evar_gmap

val extract_changed_conv_pbs : 'a evar_gmap ->
      (Evar.Set.t -> 'a evar_gconstraint -> bool) ->
      'a evar_gmap * 'a evar_gconstraint list
val extract_all_conv_pbs : 'a evar_gmap -> 'a evar_gmap * 'a evar_gconstraint list
val loc_of_conv_pb : Constr.t evar_gmap -> Constr.t evar_gconstraint -> Loc.t option

(** The following functions return the set of evars immediately
    contained in the object; need the term to be evar-normal otherwise
    defined evars are returned too. *)

val evars_of_term : Constr.t -> Evar.Set.t
  (** including evars in instances of evars *)

val evars_of_named_context : Context.Named.t -> Evar.Set.t

val evars_of_filtered_evar_info : Constr.t evar_ginfo -> Evar.Set.t

(** Metas *)
val meta_list : 'a evar_gmap -> (Constr.metavariable * clbinding) list
val meta_defined : 'a evar_gmap -> Constr.metavariable -> bool

val meta_value     : 'a evar_gmap -> Constr.metavariable -> Constr.t
(** [meta_fvalue] raises [Not_found] if meta not in map or [Anomaly] if
   meta has no value *)

val meta_fvalue    : Constr.t evar_gmap -> Constr.metavariable -> Constr.t freelisted * instance_status
val meta_opt_fvalue : Constr.t evar_gmap -> Constr.metavariable -> (Constr.t freelisted * instance_status) option
val meta_type      : Constr.t evar_gmap -> Constr.metavariable -> Constr.t
val meta_ftype     : Constr.t evar_gmap -> Constr.metavariable -> Constr.t freelisted
val meta_name      : Constr.t evar_gmap -> Constr.metavariable -> Name.t
val meta_declare   :
  Constr.metavariable -> Constr.t -> ?name:Name.t -> Constr.t evar_gmap -> Constr.t evar_gmap
val meta_assign    : Constr.metavariable -> Constr.t * instance_status -> Constr.t evar_gmap -> Constr.t evar_gmap
val meta_reassign  : Constr.metavariable -> Constr.t * instance_status -> Constr.t evar_gmap -> Constr.t evar_gmap

val clear_metas : 'a evar_gmap -> 'a evar_gmap

(** [meta_merge evd1 evd2] returns [evd2] extended with the metas of [evd1] *)
val meta_merge : ?with_univs:bool -> 'a evar_gmap -> 'a evar_gmap -> 'a evar_gmap

val undefined_metas : 'a evar_gmap -> Constr.metavariable list
val map_metas_fvalue : (Constr.t -> Constr.t) -> Constr.t evar_gmap -> Constr.t evar_gmap
val map_metas : (Constr.t -> Constr.t) -> Constr.t evar_gmap -> Constr.t evar_gmap

type 'a metabinding = Constr.metavariable * 'a * instance_status

val retract_coercible_metas : Constr.t evar_gmap -> Constr.t metabinding list * Constr.t evar_gmap

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

val evar_universe_context_set : UState.t -> Univ.ContextSet.t
val evar_universe_context_constraints : UState.t -> Univ.Constraint.t
val evar_context_universe_context : UState.t -> Univ.UContext.t
[@@ocaml.deprecated "alias of UState.context"]

val evar_universe_context_of : Univ.ContextSet.t -> UState.t
val empty_evar_universe_context : UState.t
val union_evar_universe_context : UState.t -> UState.t ->
  UState.t
val evar_universe_context_subst : UState.t -> Universes.universe_opt_subst
val constrain_variables : Univ.LSet.t -> UState.t -> UState.t


val evar_universe_context_of_binders :
  Universes.universe_binders -> UState.t

val make_evar_universe_context : env -> (Id.t located) list option -> UState.t
val restrict_universe_context : 'a evar_gmap -> Univ.LSet.t -> 'a evar_gmap
(** Raises Not_found if not a name for a universe in this map. *)
val universe_of_name : 'a evar_gmap -> Id.t -> Univ.Level.t

val universe_binders : 'a evar_gmap -> Universes.universe_binders
val add_constraints_context : UState.t ->
  Univ.Constraint.t -> UState.t


val normalize_evar_universe_context_variables : UState.t -> 
  Univ.universe_subst in_evar_universe_context

val normalize_evar_universe_context : UState.t -> 
  UState.t

val new_univ_level_variable : ?loc:Loc.t -> ?name:Id.t -> rigid -> 'a evar_gmap -> 'a evar_gmap * Univ.Level.t
val new_univ_variable : ?loc:Loc.t -> ?name:Id.t -> rigid -> 'a evar_gmap -> 'a evar_gmap * Univ.Universe.t
val new_sort_variable : ?loc:Loc.t -> ?name:Id.t -> rigid -> 'a evar_gmap -> 'a evar_gmap * Sorts.t

val add_global_univ : 'a evar_gmap -> Univ.Level.t -> 'a evar_gmap

val universe_rigidity : 'a evar_gmap -> Univ.Level.t -> rigid
val make_flexible_variable : 'a evar_gmap -> algebraic:bool -> Univ.Level.t -> 'a evar_gmap
(** See [UState.make_flexible_variable] *)

val is_sort_variable : 'a evar_gmap -> Sorts.t -> Univ.Level.t option
(** [is_sort_variable evm s] returns [Some u] or [None] if [s] is 
    not a local sort variable declared in [evm] *)
val is_flexible_level : 'a evar_gmap -> Univ.Level.t -> bool

(* val normalize_universe_level : 'a evar_gmap -> Univ.Level.t -> Univ.Level.t *)
val normalize_universe : 'a evar_gmap -> Univ.Universe.t -> Univ.Universe.t
val normalize_universe_instance : 'a evar_gmap -> Univ.Instance.t -> Univ.Instance.t

val set_leq_sort : env -> 'a evar_gmap -> Sorts.t -> Sorts.t -> 'a evar_gmap
val set_eq_sort : env -> 'a evar_gmap -> Sorts.t -> Sorts.t -> 'a evar_gmap
val has_lub : 'a evar_gmap -> Univ.Universe.t -> Univ.Universe.t -> 'a evar_gmap
val set_eq_level : 'a evar_gmap -> Univ.Level.t -> Univ.Level.t -> 'a evar_gmap
val set_leq_level : 'a evar_gmap -> Univ.Level.t -> Univ.Level.t -> 'a evar_gmap
val set_eq_instances : ?flex:bool -> 
  'a evar_gmap -> Univ.Instance.t -> Univ.Instance.t -> 'a evar_gmap

val check_eq : 'a evar_gmap -> Univ.Universe.t -> Univ.Universe.t -> bool
val check_leq : 'a evar_gmap -> Univ.Universe.t -> Univ.Universe.t -> bool

val evar_universe_context : 'a evar_gmap -> UState.t
val universe_context_set : 'a evar_gmap -> Univ.ContextSet.t
val universe_subst : 'a evar_gmap -> Universes.universe_opt_subst
val universes : 'a evar_gmap -> UGraph.t

(** [to_universe_context evm] extracts the local universes and
    constraints of [evm] and orders the universes the same as
    [Univ.ContextSet.to_context]. *)
val to_universe_context : 'a evar_gmap -> Univ.UContext.t

val const_univ_entry : poly:bool -> 'a evar_gmap -> Entries.constant_universes_entry

(** NB: [ind_univ_entry] cannot create cumulative entries. *)
val ind_univ_entry : poly:bool -> 'a evar_gmap -> Entries.inductive_universes

val check_univ_decl : poly:bool -> 'a evar_gmap -> UState.universe_decl -> Entries.constant_universes_entry

val merge_universe_context : 'a evar_gmap -> UState.t -> 'a evar_gmap
val set_universe_context : 'a evar_gmap -> UState.t -> 'a evar_gmap

val merge_context_set : ?loc:Loc.t -> ?sideff:bool -> rigid -> 'a evar_gmap -> Univ.ContextSet.t -> 'a evar_gmap
val merge_universe_subst : 'a evar_gmap -> Universes.universe_opt_subst -> 'a evar_gmap

val with_context_set : ?loc:Loc.t -> rigid -> 'a evar_gmap -> 'a Univ.in_universe_context_set -> 'a evar_gmap * 'a

val nf_univ_variables : 'a evar_gmap -> 'a evar_gmap * Univ.universe_subst
val abstract_undefined_variables : UState.t -> UState.t

val fix_undefined_variables : 'a evar_gmap -> 'a evar_gmap

val refresh_undefined_universes : Constr.t evar_gmap -> Constr.t evar_gmap * Univ.universe_level_subst

val nf_constraints : 'a evar_gmap -> 'a evar_gmap

val update_sigma_env : 'a evar_gmap -> env -> 'a evar_gmap

(** Polymorphic universes *)

val fresh_sort_in_family : ?loc:Loc.t -> ?rigid:rigid -> env -> 'a evar_gmap -> Sorts.family -> 'a evar_gmap * Sorts.t
val fresh_constant_instance : ?loc:Loc.t -> env -> 'a evar_gmap -> Constant.t -> 'a evar_gmap * Constr.pconstant
val fresh_inductive_instance : ?loc:Loc.t -> env -> 'a evar_gmap -> inductive -> 'a evar_gmap * Constr.pinductive
val fresh_constructor_instance : ?loc:Loc.t -> env -> 'a evar_gmap -> constructor -> 'a evar_gmap * Constr.pconstructor

val fresh_global : ?loc:Loc.t -> ?rigid:rigid -> ?names:Univ.Instance.t -> env ->
  Constr.t evar_gmap -> Globnames.global_reference -> Constr.t evar_gmap * Constr.t

(********************************************************************)
(* constr with holes and pending resolution of classes, conversion  *)
(* problems, candidates, etc.                                       *)

type 'a open_gconstr = 'a evar_gmap * 'a (* Special case when before is empty *)

(** Partially constructed constrs. *)

type unsolvability_explanation = SeveralInstancesFound of int
(** Failure explanation. *)

(** {5 Summary names} *)

(* This stuff is internal and should not be used. Currently a hack in
   the STM relies on it. *)
val evar_counter_summary_tag : int Summary.Dyn.tag

(** {5 Deprecated functions} *)
val create_evar_defs : 'a evar_gmap -> 'a evar_gmap
(* XXX: This is supposed to be deprecated by used by ssrmatching, what
   should the replacement be? *)

(** Create an [evar_gmap] with empty meta map: *)

(* Compat aliases *)
type evar_info = Constr.t evar_ginfo
type evar_map = Constr.t evar_gmap
type evar_constraint = Constr.t evar_gconstraint
type 'a sigma = ('a,Constr.t) gsigma
type open_constr = Constr.t open_gconstr
