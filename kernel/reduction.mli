(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Environ
open CClosure

(***********************************************************************
  s Reduction functions *)

(** None of these functions do eta reduction *)

val whd_all : ?evars:evar_handler -> env -> constr -> constr

(************************************************************************)

(** Builds an application node, reducing beta redexes it may produce. *)
val beta_applist : constr -> constr list -> constr

(** Builds an application node, reducing beta redexes it may produce. *)
val beta_appvect : constr -> constr array -> constr

(** Builds an application node, reducing beta redexe it may produce. *)
val beta_app : constr -> constr -> constr

(** Pseudo-reduction rule  Prod(x,A,B) a --> B[x\a] *)
val hnf_prod_applist : ?evars:evar_handler -> env -> types -> constr list -> types

(** In [hnf_prod_applist_decls n c args], [c] is supposed to (whd-)reduce to
    the form [∀Γ.t] with [Γ] of length [n] and possibly with let-ins; it
    returns [t] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded. *)
val hnf_prod_applist_decls : ?evars:evar_handler -> env -> int -> types -> constr list -> types

(** Compatibility alias for Term.lambda_appvect_decls *)
val betazeta_appvect : int -> constr -> constr array -> constr

(***********************************************************************
  s Recognizing products and arities modulo reduction *)

val whd_decompose_prod : ?evars:evar_handler -> env -> types -> Constr.rel_context * types
val whd_decompose_prod_decls : ?evars:evar_handler -> env -> types -> Constr.rel_context * types
val whd_decompose_lambda : ?evars:evar_handler -> env -> constr -> Constr.rel_context * constr
val whd_decompose_lambda_decls : ?evars:evar_handler -> env -> constr -> Constr.rel_context * constr

(** This is typically the function to use to extract the context of a
    Fix not already in normal form up to and including the decreasing
    argument, counting as many lambda's as given by the decreasing
    index + 1 *)
val whd_decompose_lambda_n_assum : ?evars:evar_handler -> env -> int -> constr -> Constr.rel_context * constr

exception NotArity

val dest_arity : ?evars:evar_handler -> env -> types -> Term.arity (* raises NotArity if not an arity *)
val is_arity : ?evars:evar_handler -> env -> types -> bool

val eta_expand : ?evars:evar_handler -> env -> constr -> types -> constr
