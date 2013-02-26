(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Mod_subst
open Lazyconstr

(** Operations concerning types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

(** {6 Constants} *)

val subst_const_def : substitution -> constant_def -> constant_def
val subst_const_body : substitution -> constant_body -> constant_body

(** Is there a actual body in const_body or const_body_opaque ? *)

val constant_has_body : constant_body -> bool

(** Accessing const_body_opaque or const_body *)

val body_of_constant : constant_body -> constr_substituted option

val is_opaque : constant_body -> bool


(** {6 Inductive types} *)

val eq_recarg : recarg -> recarg -> bool

val subst_recarg : substitution -> recarg -> recarg

val mk_norec : wf_paths
val mk_paths : recarg -> wf_paths list array -> wf_paths
val dest_recarg : wf_paths -> recarg
val dest_subterms : wf_paths -> wf_paths list array
val recarg_length : wf_paths -> int -> int

val subst_wf_paths : substitution -> wf_paths -> wf_paths

val subst_mind : substitution -> mutual_inductive_body -> mutual_inductive_body


(** {6 Hash-consing} *)

(** Here, strictly speaking, we don't perform true hash-consing
    of the structure, but simply hash-cons all inner constr
    and other known elements *)

val hcons_const_body : constant_body -> constant_body
val hcons_mind : mutual_inductive_body -> mutual_inductive_body
