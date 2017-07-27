(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines clausenv, which is a deprecated way to handle open terms
    in the proof engine. Most of the API here is legacy except for the
    evar-based clauses. *)

open Names
open Term
open Environ
open Evd
open EConstr
open Unification
open Misctypes

(** {6 The Type of Constructions clausale environments.} *)

type clausenv = {
  env      : env; (** the typing context *)
  evd      : evar_map; (** the mapping from metavar and evar numbers to their 
			   types and values *)
  templval : constr freelisted; (** the template which we are trying to fill 
				    out *)
  templtyp : constr freelisted (** its type *)}


(** subject of clenv (instantiated) *)
val clenv_value     : clausenv -> constr

(** type of clenv (instantiated) *)
val clenv_type      : clausenv -> types

(** substitute resolved metas *)
val clenv_nf_meta   : clausenv -> EConstr.constr -> EConstr.constr

(** type of a meta in clenv context *)
val clenv_meta_type : clausenv -> metavariable -> types

val mk_clenv_from : 'a Proofview.Goal.t -> EConstr.constr * EConstr.types -> clausenv
val mk_clenv_from_n :
  'a Proofview.Goal.t -> int option -> EConstr.constr * EConstr.types -> clausenv
val mk_clenv_type_of : 'a Proofview.Goal.t -> EConstr.constr -> clausenv
val mk_clenv_from_env : env -> evar_map -> int option -> EConstr.constr * EConstr.types -> clausenv

(** Refresh the universes in a clenv *)
val refresh_undefined_univs : clausenv -> clausenv * Univ.universe_level_subst

(** {6 linking of clenvs } *)

val clenv_fchain :
  ?with_univs:bool -> ?flags:unify_flags -> metavariable -> clausenv -> clausenv -> clausenv

(** {6 Unification with clenvs } *)

(** Unifies two terms in a clenv. *)
val clenv_unify :
  ?flags:unify_flags -> conv_pb -> constr -> constr -> clausenv -> clausenv

(** unifies the concl of the goal with the type of the clenv *)
val old_clenv_unique_resolver :
  ?flags:unify_flags -> clausenv -> Goal.goal sigma -> clausenv

val clenv_unique_resolver :
  ?flags:unify_flags -> clausenv -> 'a Proofview.Goal.t -> clausenv

val clenv_dependent : clausenv -> metavariable list

val clenv_pose_metas_as_evars : clausenv -> metavariable list -> clausenv

(** {6 Bindings } *)

type arg_bindings = constr explicit_bindings

(** bindings where the key is the position in the template of the
   clenv (dependent or not). Positions can be negative meaning to
   start from the rightmost argument of the template. *)
val clenv_independent : clausenv -> metavariable list
val clenv_missing : clausenv -> metavariable list

(** for the purpose of inversion tactics *)
exception NoSuchBinding
val clenv_constrain_last_binding : constr -> clausenv -> clausenv

val clenv_unify_meta_types : ?flags:unify_flags -> clausenv -> clausenv

(** start with a clenv to refine with a given term with bindings *)

(** the arity of the lemma is fixed 
   the optional int tells how many prods of the lemma have to be used 
   use all of them if None *)
val make_clenv_binding_env_apply :
  env -> evar_map -> int option -> EConstr.constr * EConstr.constr -> constr bindings ->
   clausenv

val make_clenv_binding_apply :
  env -> evar_map -> int option -> EConstr.constr * EConstr.constr -> constr bindings ->
   clausenv

val make_clenv_binding_env :
  env -> evar_map -> EConstr.constr * EConstr.constr -> constr bindings -> clausenv

val make_clenv_binding :
  env -> evar_map -> EConstr.constr * EConstr.constr -> constr bindings -> clausenv

(** if the clause is a product, add an extra meta for this product *)
exception NotExtensibleClause
val clenv_push_prod : clausenv -> clausenv

(** {6 Pretty-print (debug only) } *)
val pr_clenv : clausenv -> Pp.t

(** {6 Evar-based clauses} *)

(** The following code is an adaptation of the [make_clenv_*] functions above,
    except that it uses evars instead of metas, and naturally fits in the new
    refinement monad. It should eventually replace all uses of the
    aforementioned functions.

    A clause is constructed as follows: assume a type [t := forall (x1 : A1) ...
    (xn : An), T], we instantiate all the [xi] with a fresh evar [ei] and
    return [T(xi := ei)] together with the [ei] enriched with a bit of
    additional data. This is the simple part done by [make_evar_clause].

    The problem lies in the fact we want to solve such holes with some
    [constr bindings]. This entails some subtleties, because the provided terms
    may only be well-typed up to a coercion, which we can only infer if we have
    enough typing information. The meta machinery could insert coercions through
    tricky instantiation delays. The only solution we have now is to delay the
    tentative resolution of clauses by providing the [solve_evar_clause]
    function, to be called at a smart enough time.
*)

type hole = {
  hole_evar : EConstr.constr;
  (** The hole itself. Guaranteed to be an evar. *)
  hole_type : EConstr.types;
  (** Type of the hole in the current environment. *)
  hole_deps  : bool;
  (** Whether the remainder of the clause was dependent in the hole. Note that
      because let binders are substituted, it does not mean that it actually
      appears somewhere in the returned clause. *)
  hole_name : Name.t;
  (** Name of the hole coming from its binder. *)
}

type clause = {
  cl_holes : hole list;
  (** The holes of the clause. *)
  cl_concl : EConstr.types;
  (** The conclusion: an evar applied to some terms *)
  cl_concl_occs : Evarconv.occurrences_selection option;
  (** The occurrences of the terms to be abstracted when unifying *)
  cl_val   : EConstr.constr;
  (** The value the clause was built from, applied to holes *)
}

(** Accessors *)

val hole_type : evar_map -> hole -> types
(** [hole_type sigma h] returns the beta-iota-evar normalized type of [h] in [sigma].
    @pre The hole's evar is undefined in [sigma]. *)

val clenv_concl : clause -> types
(** The conclusion of the clause. *)

val clenv_val : clause -> constr
(** The value of the clause, of type the conclusion *)

val clenv_holes : clause -> hole list
(** The list of remaining holes of the clause.
    CAUTION: this API doesn't ensure that only undefined holes are returned here.
    In clenvtac, the clause-manipulating primitives ensure that property using
    [clenv_advance] below. This applies to the two functions below as well. *)

val clenv_dep_holes: clause -> hole list
(** Returns the dependent goals only. *)

val clenv_indep_holes : clause -> hole list
(** Returns the independent holes in the clause, according to the
    hyps_only flag that was used during its construction. *)

val clenv_map_concl : (types -> types) -> clause -> clause
(** Map a function on the clause's conclusion type. *)

(** Creation of clauses. *)

val make_evar_clause :
  env -> evar_map -> ?len:int -> ?occs:Evarconv.occurrences_selection ->
  EConstr.constr -> EConstr.types -> (evar_map * clause)
(** An evar version of {!make_clenv_binding}. Given a type [t],
    [evar_environments env sigma ~len t bl] tries to eliminate at most [len]
    products of the type [t] by filling it with evars. It returns the resulting
    type together with the list of holes generated. Assumes that [t] is
    well-typed in the environment. *)

val make_clenv_from_env :
  env -> evar_map -> ?len:int -> ?occs:Evarconv.occurrences_selection ->
  constr * types -> evar_map * clause
(** Wrapper for [make_evar_clause], simply removing casts in the value argument. *)

val solve_evar_clause : env -> evar_map -> hyps_only:bool -> clause -> EConstr.constr bindings ->
  evar_map * clause
(** [solve_evar_clause env sigma recompute_deps hyps_only cl bl] tries
    to solve the holes contained in [cl] according to the [bl]
    argument. Assumes that [bl] are well-typed in the environment. The
    boolean [recompute_deps] tells if the dependent holes of the clause
    have to be recomputed first, in which case [hyps_only] is a flag
    that allows to consider arguments to be dependent only when they
    appear in hypotheses and not in the conclusion. This boolean is
    especially used when [bl] is of the form [ImplicitBindings _] to
    determine which bindings to instantiate.
    Returns the new [sigma] and the advanced clause. *)

val make_clenv_bindings :
  env -> evar_map -> ?len:int -> ?occs:Evarconv.occurrences_selection ->
  constr * constr -> hyps_only:bool -> constr bindings ->
  evar_map * clause
(** Combination of [make_evar_clause] and [solve_evar_clause], creating a clause
    and immediately solving them with the given bindings. *)

val clenv_dest_prod : env -> evar_map -> clause -> evar_map * clause
(* [clenv_dest_prod env sigma cl]

   Add one more hole of type [ty] to the clause if its conclusion if of the form
   [ty -> _] after weak head reduction (whd_all).

   @raise NotExtensibleClause if no product is found. *)

val clenv_advance : evar_map -> clause -> clause
(** Advance the clause, removing holes that are defined in the evar_map and
    do not simply result from clearing an hypothesis in the original hole evar.
    It relies on [Proofview.Unsafe.advance] to compute this information. *)

val clenv_chain : ?holes_order:bool -> (* true = holes of the first clause first *)
                  ?flags:unify_flags -> ?occs:Evarconv.occurrences_selection ->
                  env -> evar_map -> hole ->
                  clause -> clause -> evar_map * clause
(** [clenv_chain env sigma hole first next] chains two clauses.  The
    first clause must contain the undefined hole which is filled by the
    next clauses body. Note that holes from the next clause which are
    unified with holes of the first clause always remain with their name
    in the resulting clause. This ensures that evar names are always
    preserved from the next clause to the resulting clause.
    Returns the new [sigma] and the advanced clause. *)

val clenv_chain_last : ?flags:unify_flags ->
                       env -> evar_map -> constr -> clause -> evar_map * clause
(** [clenv_chain_last env sigma c cl] defines the last hole of [cl] as [c].
    Returns the new [sigma] and the advanced clause. *)

val clenv_recompute_deps : evar_map -> hyps_only:bool -> clause -> clause
(** [clenv_recompute_deps sigma hyps_only cl]
    Updates the dependencies of the clause. A hole is dependent if:
    - if hyps_only is true: it appears in another hole's type of the clause and
      does _not_ appear in the conclusion.
    - if hyps_only is false: it appears either in another hole's type
      or the conclusion. *)

val clenv_unify_concl : env -> evar_map ->
                        Evarconv.unify_flags -> types -> clause ->
                        evar_map * clause
(** [clenv_unify_concl env sigma flags ty cl] unifies the conclusion of
    the clause with [ty] (with cumulativity), calling evar_conv with the given
    flags. Returns the new [sigma] and the advanced clause.

    Two situations can arise:
    - If the clause has an explicit occurrences selection set (see [make_evar_clause]),
    the conclusion is an evar applied to [n] arguments _and_ [ty] is not an explicit
    lambda abstraction applied to exactly [n] arguments, then second-order matching
    is called with the given occurrence selection, truncated to [n] arguments (i.e. the
    occurrence selection might be longer than the actual evar arguments).
    - Otherwise, evar_conv is called directly, favoring first-order unification solutions,
    and if that fails we backtrack on higher-order unification, ignoring the occurrence
    selection.

  @raises Evarconv.UnableToUnify if unification fails *)
