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
open Environ
open Evd
open Tactypes

(** {6 Evar-based clauses} *)

(** The following code is an adaptation of the [Clenv.make_clenv_*] functions,
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
  hole_evar_key : Evar.t;
  (** Internal evar key of the hole. *)
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

val check_bindings : 'a explicit_bindings -> unit

val explain_no_such_bound_variable : Id.t list -> Id.t CAst.t -> 'a

val error_not_right_number_missing_arguments : int -> 'a

val check_evar_clause :  Environ.env -> evar_map -> evar_map -> clause -> unit
