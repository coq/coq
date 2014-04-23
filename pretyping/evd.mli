(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Loc
open Names
open Term
open Context
open Environ
open Mod_subst

(** {5 Existential variables and unification states}

    A unification state (of type [evar_map]) is primarily a finite mapping
    from existential variables to records containing the type of the evar
    ([evar_concl]), the context under which it was introduced ([evar_hyps])
    and its definition ([evar_body]). [evar_extra] is used to add any other
    kind of information.

    It also contains conversion constraints, debugging information and
    information about meta variables. *)

(** {6 Evars} *)

type evar = existential_key
(** Existential variables. TODO: Should be made opaque one day. *)

val string_of_existential : evar -> string

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
  | Evar_defined of constr

module Store : Store.S
(** Datatype used to store additional information in evar maps. *)

type evar_info = {
  evar_concl : constr;
  (** Type of the evar. *)
  evar_hyps : named_context_val;
  (** Context of the evar. *)
  evar_body : evar_body;
  (** Optional content of the evar. *)
  evar_filter : Filter.t;
  (** Boolean mask over {!evar_hyps}. Should have the same length.
      TODO: document me more. *)
  evar_source : Evar_kinds.t located;
  (** Information about the evar. *)
  evar_candidates : constr list option;
  (** TODO: document this *)
  evar_extra : Store.t
  (** Extra store, used for clever hacks. *)
}

val eq_evar_info : evar_info -> evar_info -> bool

val make_evar : named_context_val -> types -> evar_info
val evar_concl : evar_info -> constr
val evar_context : evar_info -> named_context
val evar_filtered_context : evar_info -> named_context
val evar_hyps : evar_info -> named_context_val
val evar_filtered_hyps : evar_info -> named_context_val
val evar_body : evar_info -> evar_body
val evar_filter : evar_info -> Filter.t
val evar_env :  evar_info -> env
val evar_filtered_env :  evar_info -> env

(** {6 Unification state} **)

type evar_map
(** Type of unification state. Essentially a bunch of state-passing data needed
    to handle incremental term construction. *)

val progress_evar_map : evar_map -> evar_map -> bool
(** Assuming that the second map extends the first one, this says if
   some existing evar has been refined *)

val empty : evar_map
(** The empty evar map. *)

val is_empty : evar_map -> bool
(** Whether an evarmap is empty. *)

val has_undefined : evar_map -> bool
(** [has_undefined sigma] is [true] if and only if
    there are uninstantiated evars in [sigma]. *)

val add : evar_map -> evar -> evar_info -> evar_map
(** [add sigma ev info] adds [ev] with evar info [info] in sigma.
    Precondition: ev must not preexist in [sigma]. *)

val find : evar_map -> evar -> evar_info
(** Recover the data associated to an evar. *)

val find_undefined : evar_map -> evar -> evar_info
(** Same as {!find} but restricted to undefined evars. For efficiency
    reasons. *)

val remove : evar_map -> evar -> evar_map
(** Remove an evar from an evar map. Use with caution. *)

val mem : evar_map -> evar -> bool
(** Whether an evar is present in an evarmap. *)

val fold : (evar -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
(** Apply a function to all evars and their associated info in an evarmap. *)

val fold_undefined : (evar -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
(** Same as {!fold}, but restricted to undefined evars. For efficiency
    reasons. *)

val raw_map : (evar -> evar_info -> evar_info) -> evar_map -> evar_map
(** Apply the given function to all evars in the map. Beware: this function
    expects the argument function to preserve the kind of [evar_body], i.e. it
    must send [Evar_empty] to [Evar_empty] and [Evar_defined c] to some
    [Evar_defined c']. *)

val raw_map_undefined : (evar -> evar_info -> evar_info) -> evar_map -> evar_map
(** Same as {!raw_map}, but restricted to undefined evars. For efficiency
    reasons. *)

val define : evar -> constr -> evar_map -> evar_map
(** Set the body of an evar to the given constr. It is expected that:
    {ul
      {- The evar is already present in the evarmap.}
      {- The evar is not defined in the evarmap yet.}
      {- All the evars present in the constr should be present in the evar map.}
    } *)

val is_evar : evar_map -> evar -> bool
(** Alias for {!mem}. *)

val is_defined : evar_map -> evar -> bool
(** Whether an evar is defined in an evarmap. *)

val is_undefined : evar_map -> evar -> bool
(** Whether an evar is not defined in an evarmap. *)

val add_constraints : evar_map -> Univ.constraints -> evar_map
(** Add universe constraints in an evar map. *)

val undefined_map : evar_map -> evar_info Evar.Map.t
(** Access the undefined evar mapping directly. *)

(** {6 Instantiating partial terms} *)

exception NotInstantiatedEvar

val existential_value : evar_map -> existential -> constr
(** [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
    no body and [Not_found] if it does not exist in [sigma] *)

val existential_type : evar_map -> existential -> types

val existential_opt_value : evar_map -> existential -> constr option
(** Same as {!existential_value} but returns an option instead of raising an
    exception. *)

val instantiate_evar_array : evar_info -> constr -> constr array -> constr

val subst_evar_defs_light : substitution -> evar_map -> evar_map
(** Assume empty universe constraints in [evar_map] and [conv_pbs] *)

val evars_reset_evd : ?with_conv_pbs:bool -> evar_map ->  evar_map -> evar_map
(** spiwack: this function seems to somewhat break the abstraction. *)

(** {6 Misc} *)

val evar_declare :
  named_context_val -> evar -> types -> ?src:Loc.t * Evar_kinds.t ->
      ?filter:Filter.t -> ?candidates:constr list -> evar_map -> evar_map
(** Convenience function. Just a wrapper around {!add}. *)

val evar_source : existential_key -> evar_map -> Evar_kinds.t located
(** Convenience function. Wrapper around {!find} to recover the source of an
    evar in a given evar map. *)

(** {5 Side-effects} *)

val emit_side_effects : Declareops.side_effects -> evar_map -> evar_map
(** Push a side-effect into the evar map. *)

val eval_side_effects : evar_map -> Declareops.side_effects
(** Return the effects contained in the evar map. *)

val drop_side_effects : evar_map -> evar_map
(** This should not be used. For hacking purposes. *)

(** {5 Sort variables}

    Evar maps also keep track of the universe constraints defined at a given
    point. This section defines the relevant manipulation functions. *)

val new_univ_variable : evar_map -> evar_map * Univ.universe
val new_sort_variable : evar_map -> evar_map * sorts
val is_sort_variable : evar_map -> sorts -> bool
val whd_sort_variable : evar_map -> constr -> constr
val set_leq_sort : evar_map -> sorts -> sorts -> evar_map
val set_eq_sort : evar_map -> sorts -> sorts -> evar_map

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

val metavars_of : constr -> Metaset.t
val mk_freelisted : constr -> constr freelisted
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
  | Cltyp of Name.t * constr freelisted
  | Clval of Name.t * (constr freelisted * instance_status) * constr freelisted

(** Unification constraints *)
type conv_pb = Reduction.conv_pb
type evar_constraint = conv_pb * env * constr * constr
val add_conv_pb :  evar_constraint -> evar_map -> evar_map

val extract_changed_conv_pbs : evar_map ->
      (Evar.Set.t -> evar_constraint -> bool) ->
      evar_map * evar_constraint list
val extract_all_conv_pbs : evar_map -> evar_map * evar_constraint list
val loc_of_conv_pb : evar_map -> evar_constraint -> Loc.t

val evar_list : evar_map -> constr -> existential list
val collect_evars : constr -> Evar.Set.t

(** Metas *)
val meta_list : evar_map -> (metavariable * clbinding) list
val meta_defined : evar_map -> metavariable -> bool

val meta_value     : evar_map -> metavariable -> constr
(** [meta_fvalue] raises [Not_found] if meta not in map or [Anomaly] if
   meta has no value *)

val meta_fvalue    : evar_map -> metavariable -> constr freelisted * instance_status
val meta_opt_fvalue : evar_map -> metavariable -> (constr freelisted * instance_status) option
val meta_type      : evar_map -> metavariable -> types
val meta_ftype     : evar_map -> metavariable -> types freelisted
val meta_name      : evar_map -> metavariable -> Name.t
val meta_with_name : evar_map -> Id.t -> metavariable
val meta_declare   :
  metavariable -> types -> ?name:Name.t -> evar_map -> evar_map
val meta_assign    : metavariable -> constr * instance_status -> evar_map -> evar_map
val meta_reassign  : metavariable -> constr * instance_status -> evar_map -> evar_map

(** [meta_merge evd1 evd2] returns [evd2] extended with the metas of [evd1] *)
val meta_merge : evar_map -> evar_map -> evar_map

val undefined_metas : evar_map -> metavariable list
val map_metas_fvalue : (constr -> constr) -> evar_map -> evar_map

type metabinding = metavariable * constr * instance_status

val retract_coercible_metas : evar_map -> metabinding list * evar_map
val subst_defined_metas : metabinding list -> constr -> constr option

(** {5 FIXME: Nothing to do here} *)

type open_constr = evar_map * constr
(** Partially constructed constrs. *)

type unsolvability_explanation = SeveralInstancesFound of int
(** Failure explanation. *)

(** {5 Debug pretty-printers} *)

val pr_evar_info : evar_info -> Pp.std_ppcmds
val pr_evar_constraints : evar_constraint list -> Pp.std_ppcmds
val pr_evar_map : int option -> evar_map -> Pp.std_ppcmds
val pr_evar_map_filter : (Evar.t -> evar_info -> bool) ->
  evar_map -> Pp.std_ppcmds
val pr_metaset : Metaset.t -> Pp.std_ppcmds

(** {5 Deprecated functions} *)

val create_evar_defs      : evar_map -> evar_map
(** Create an [evar_map] with empty meta map: *)

val create_goal_evar_defs : evar_map -> evar_map

val subst_evar_map : substitution -> evar_map -> evar_map
