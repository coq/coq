(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Evd
open Environ

type alias

val of_alias : alias -> EConstr.t

module AllowedEvars : sig

  type t
  (** Represents the set of evars that can be defined by the pretyper *)

  val all : t
  (** All evars can be defined *)

  val mem : t -> Evar.t -> bool
  (** [mem allowed evk] is true iff evk can be defined *)

  val from_pred : (Evar.t -> bool) -> t
  (** [from_pred p] means evars satisfying p can be defined *)

  val except : Evar.Set.t -> t
  (** [except evars] means all evars can be defined except the ones in [evars] *)

  val remove : Evar.t -> t -> t
  (** [remove evk allowed] removes [evk] from the set of evars allowed by [allowed] *)

end

type unify_flags = {
  modulo_betaiota : bool;
  (* Enable beta-iota reductions during unification *)
  open_ts : TransparentState.t;
  (* Enable delta reduction according to open_ts for open terms *)
  closed_ts : TransparentState.t;
  (* Enable delta reduction according to closed_ts for closed terms (when calling conversion) *)
  subterm_ts : TransparentState.t;
  (* Enable delta reduction according to subterm_ts for selection of subterms during higher-order
     unifications. *)
  allowed_evars : AllowedEvars.t;
  (* Disallowed evars are treated like rigid variables during unification: they can not be instantiated. *)
  allow_K_at_toplevel : bool;
  (* During higher-order unifications, allow to produce K-redexes: i.e. to produce
     an abstraction for an unused argument *)
  with_cs : bool
  (* Enable canonical structure resolution during unification *)
}

type unification_result =
  | Success of evar_map
  | UnifFailure of evar_map * Pretype_errors.unification_error

val is_success : unification_result -> bool

val is_evar_allowed : unify_flags -> Evar.t -> bool

(** Replace the vars and rels that are aliases to other vars and rels by
   their representative that is most ancient in the context *)
val expand_vars_in_term : env -> evar_map -> constr -> constr

(** One might want to use different conversion strategies for types and terms:
    e.g. preventing delta reductions when doing term unifications but allowing
    arbitrary delta conversion when checking the types of evar instances. *)

type unification_kind =
  | TypeUnification
  | TermUnification

(** A unification function parameterized by:
    - unification flags
    - the kind of unification
    - environment
    - sigma
    - conversion problem
    - the two terms to unify. *)
type unifier = unify_flags -> unification_kind ->
  env -> evar_map -> conv_pb -> constr -> constr -> unification_result

(** A conversion function: parameterized by the kind of unification,
    environment, sigma, conversion problem and the two terms to convert.
    Conversion is not allowed to instantiate evars contrary to unification. *)
type conversion_check = unify_flags -> unification_kind ->
  env -> evar_map -> conv_pb -> constr -> constr -> bool

(** [instantiate_evar unify flags env sigma ev c] defines the evar [ev] with [c],
    checking that the type of [c] is unifiable with [ev]'s declared type first.

    Preconditions:
    - [ev] does not occur in [c].
    - [c] does not contain any Meta(_)

    If [ev] and [c] have non inferably convertible types, an exception
    [IllTypedInstance] is raised *)

val instantiate_evar : unifier -> unify_flags -> env -> evar_map ->
  Evar.t -> constr -> evar_map

(** [evar_define choose env ev c] try to instantiate [ev] with [c] (typed in [env]),
   possibly solving related unification problems, possibly leaving open
   some problems that cannot be solved in a unique way (except if choose is
   true); fails if the instance is not valid for the given [ev];
   If [ev] and [c] have non inferably convertible types, an exception
   [IllTypedInstance] is raised *)

val evar_define : unifier -> unify_flags -> ?choose:bool -> ?imitate_defs:bool ->
  env -> evar_map -> bool option -> existential -> constr -> evar_map


val refresh_universes :
  ?status:Evd.rigid ->
  ?onlyalg:bool (* Only algebraic universes *) ->
  ?refreshset:bool ->
  (* Also refresh Prop and Set universes, so that the returned type can be any supertype
     of the original type *)
  bool option (* direction: true for levels lower than the existing levels *) ->
  env -> evar_map -> types -> evar_map * types

val solve_refl : ?can_drop:bool -> conversion_check -> unify_flags -> env ->  evar_map ->
  bool option -> Evar.t -> constr list -> constr list -> evar_map

val solve_evar_evar : ?force:bool ->
  (env -> evar_map -> bool option -> existential -> constr -> evar_map) ->
  unifier -> unify_flags ->
  env ->  evar_map -> bool option -> existential -> existential -> evar_map
  (** The two evars are expected to be in inferably convertible types;
      if not, an exception IllTypedInstance is raised *)

(* [solve_simple_eqn unifier flags env evd (direction,?ev[inst],t)]
   makes progresses on problems of the form [?ev[inst] := t] (or
   [?ev[inst] :<= t], or [?ev[inst] :>= t]). It uses imitation and a
   limited form of projection. At the time of writing this comment,
   only rels/vars (possibly indirectly via a chain of evars) and
   constructors are used for projection. For instance
   [?e[x,S 0] := x + S 0] will be solved by imitating [+] and
   projecting [x] and [S 0] (so that [?e[a,b]:=a+b]) but in
   [?e[0+0] := 0+0], the possible imitation will not be seen.

   [choose] tells to make an irreversible choice when two valid
   projections are competing. It is to be used when no more reversible
   progress can be done. It is [false] by default.

   [imitate_defs] tells to expand local definitions if they cannot be
   projected. It is [true] by default.
*)

val solve_simple_eqn : unifier -> unify_flags -> ?choose:bool -> ?imitate_defs:bool -> env ->  evar_map ->
  bool option * existential * constr -> unification_result

val reconsider_unif_constraints : unifier -> unify_flags -> evar_map -> unification_result

val is_unification_pattern_evar : env -> evar_map -> existential -> constr list ->
  constr -> alias list option

val is_unification_pattern : env * int -> evar_map -> constr -> constr list ->
  constr -> alias list option

val solve_pattern_eqn : env -> evar_map -> alias list -> constr -> constr

val noccur_evar : env -> evar_map -> Evar.t -> constr -> bool

exception IllTypedInstance of env * evar_map * types * types

val check_evar_instance : unifier -> unify_flags ->
  env -> evar_map -> Evar.t -> constr -> evar_map
  (** May raise IllTypedInstance if types are not convertible *)

val remove_instance_local_defs :
  evar_map -> Evar.t -> 'a list -> 'a list

val get_type_of_refresh :
  ?polyprop:bool -> ?lax:bool -> env -> evar_map -> constr
  -> evar_map * types
