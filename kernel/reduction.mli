(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Environ

(***********************************************************************
  s Reduction functions *)

(** None of these functions do eta reduction *)

val whd_all                 : env -> constr -> constr

(************************************************************************)

(** Builds an application node, reducing beta redexes it may produce. *)
val beta_applist : constr -> constr list -> constr

(** Builds an application node, reducing beta redexes it may produce. *)
val beta_appvect : constr -> constr array -> constr

(** Builds an application node, reducing beta redexe it may produce. *)
val beta_app : constr -> constr -> constr

(** Pseudo-reduction rule  Prod(x,A,B) a --> B[x\a] *)
val hnf_prod_applist : env -> types -> constr list -> types

(** In [hnf_prod_applist_decls n c args], [c] is supposed to (whd-)reduce to
    the form [∀Γ.t] with [Γ] of length [n] and possibly with let-ins; it
    returns [t] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded. *)
val hnf_prod_applist_decls : env -> int -> types -> constr list -> types

(** Compatibility alias for Term.lambda_appvect_decls *)
val betazeta_appvect : int -> constr -> constr array -> constr

(***********************************************************************
  s Recognizing products and arities modulo reduction *)

val whd_decompose_prod         : env -> types -> Constr.rel_context * types
val whd_decompose_prod_n       : env -> int -> types -> Constr.rel_context * types
val whd_decompose_prod_decls   : env -> types -> Constr.rel_context * types
val whd_decompose_lambda       : env -> constr -> Constr.rel_context * constr
val whd_decompose_lambda_decls : env -> constr -> Constr.rel_context * constr

(** This is typically the function to use to extract the context of a
    Fix not already in normal form up to and including the decreasing
    argument, counting as many lambda's as given by the decreasing
    index + 1 *)
val whd_decompose_lambda_n_assum : env -> int -> constr -> Constr.rel_context * constr

exception NotArity

val dest_arity : env -> types -> Term.arity (* raises NotArity if not an arity *)
val is_arity   : env -> types -> bool

val eta_expand : env -> constr -> types -> constr

(** Deprecated *)

val dest_prod       : env -> types -> Constr.rel_context * types
[@@ocaml.deprecated "Use [whd_decompose_prod] instead."]
val dest_prod_assum : env -> types -> Constr.rel_context * types
[@@ocaml.deprecated "Use [whd_decompose_prod_decls] instead."]
val dest_lam        : env -> constr -> Constr.rel_context * constr
[@@ocaml.deprecated "Use [whd_decompose_lambda] instead."]
val dest_lam_assum  : env -> constr -> Constr.rel_context * constr
[@@ocaml.deprecated "Use [whd_decompose_lambda_assum] instead."]

(** Re-deprecated in 8.19 *)

val hnf_decompose_prod           : env -> types -> Constr.rel_context * types
[@@ocaml.deprecated "Use [whd_decompose_prod] instead."]
val hnf_decompose_prod_decls     : env -> types -> Constr.rel_context * types
[@@ocaml.deprecated "Use [whd_decompose_prod_decls] instead."]
val hnf_decompose_lambda         : env -> constr -> Constr.rel_context * constr
[@@ocaml.deprecated "Use [whd_decompose_lambda] instead."]
val hnf_decompose_lambda_decls   : env -> constr -> Constr.rel_context * constr
[@@ocaml.deprecated "Use [whd_decompose_lambda_decls] instead."]
val hnf_decompose_lambda_n_decls : env -> int -> constr -> Constr.rel_context * constr
[@@ocaml.deprecated "Use [whd_decompose_lambda_n_assum] instead."]
