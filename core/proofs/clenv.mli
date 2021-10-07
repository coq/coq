(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file defines clausenv, which is a deprecated way to handle open terms
    in the proof engine. Most of the API here is legacy except for the
    evar-based clauses. *)

open Names
open Constr
open Environ
open Evd
open EConstr
open Unification
open Tactypes

(** {6 The Type of Constructions clausale environments.} *)

type clausenv = private {
  env      : env; (** the typing context *)
  evd      : evar_map; (** the mapping from metavar and evar numbers to their
                           types and values *)
  templval : constr freelisted; (** the template which we are trying to fill
                                    out *)
  templtyp : constr freelisted; (** its type *)
  cache : Reductionops.meta_instance_subst; (* Reductionops.create_meta_instance_subst evd) *)
}

val mk_clausenv : env -> evar_map -> constr freelisted -> types freelisted -> clausenv
val update_clenv_evd : clausenv -> evar_map -> clausenv

(** subject of clenv (instantiated) *)
val clenv_value     : clausenv -> constr

(** type of clenv (instantiated) *)
val clenv_type      : clausenv -> types

(** type of a meta in clenv context *)
val clenv_meta_type : clausenv -> metavariable -> types

val mk_clenv_from : env -> evar_map -> EConstr.constr * EConstr.types -> clausenv
val mk_clenv_from_n : env -> evar_map -> int -> EConstr.constr * EConstr.types -> clausenv

(** {6 linking of clenvs } *)

val clenv_instantiate : ?flags:unify_flags -> metavariable -> clausenv -> (constr * types) -> clausenv

val clenv_fchain :
  ?with_univs:bool -> ?flags:unify_flags -> metavariable -> clausenv -> clausenv -> clausenv

(** {6 Unification with clenvs } *)

(** Unifies two terms in a clenv. The boolean is [allow_K] (see [Unification]) *)
val clenv_unify :
  ?flags:unify_flags -> conv_pb -> constr -> constr -> clausenv -> clausenv

(** {6 Bindings } *)

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
val make_clenv_binding_apply :
  env -> evar_map -> int option -> EConstr.constr * EConstr.constr -> constr bindings ->
   clausenv

val make_clenv_binding :
  env -> evar_map -> EConstr.constr * EConstr.constr -> constr bindings -> clausenv

(** if the clause is a product, add an extra meta for this product *)
val clenv_push_prod : clausenv -> (metavariable * bool * clausenv) option

(** {6 Clenv tactics} *)

val unify : ?flags:unify_flags -> constr -> unit Proofview.tactic
val res_pf : ?with_evars:bool -> ?with_classes:bool -> ?flags:unify_flags -> clausenv -> unit Proofview.tactic

val clenv_pose_dependent_evars : ?with_evars:bool -> clausenv -> clausenv

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
  cl_concl : EConstr.types;
}

val make_evar_clause : env -> evar_map -> ?len:int -> EConstr.types ->
  (evar_map * clause)
(** An evar version of {!make_clenv_binding}. Given a type [t],
    [evar_environments env sigma ~len t bl] tries to eliminate at most [len]
    products of the type [t] by filling it with evars. It returns the resulting
    type together with the list of holes generated. Assumes that [t] is
    well-typed in the environment. *)

val solve_evar_clause : env -> evar_map -> bool -> clause -> EConstr.constr bindings ->
  evar_map
(** [solve_evar_clause env sigma hyps cl bl] tries to solve the holes contained
    in [cl] according to the [bl] argument. Assumes that [bl] are well-typed in
    the environment. The boolean [hyps] is a compatibility flag that allows to
    consider arguments to be dependent only when they appear in hypotheses and
    not in the conclusion. This boolean is only used when [bl] is of the form
    [ImplicitBindings _]. *)
