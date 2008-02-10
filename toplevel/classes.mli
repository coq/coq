(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.mli 6748 2005-02-18 22:17:50Z herbelin $ i*)

(*i*)
open Names
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Topconstr
open Util
open Typeclasses
open Implicit_quantifiers
(*i*)

type binder_list = (identifier located * bool * constr_expr) list
type binder_def_list = (identifier located * identifier located list * constr_expr) list
 
val binders_of_lidents : identifier located list -> local_binder list

val declare_implicit_proj : typeclass -> constant -> Impargs.manual_explicitation list -> bool -> unit

val infer_super_instances : env -> constr list ->
  named_context -> named_context -> types list * identifier list * named_context

val new_class : identifier located ->
  local_binder list ->
  Vernacexpr.sort_expr located ->
  local_binder list ->
  binder_list -> unit

val new_instance : 
  local_binder list ->
  typeclass_constraint ->
  binder_def_list ->
  unit

val context : typeclass_context -> unit

val add_instance_hint : identifier -> unit

val declare_instance : identifier located -> unit

val mismatched_params : env -> constr_expr list -> named_context -> 'a

val mismatched_props : env -> constr_expr list -> named_context -> 'a

val solve_by_tac :     env ->
    Evd.evar_defs ->
    Evd.evar ->
  evar_info ->
  Proof_type.tactic ->
    Evd.evar_defs * bool

val solve_evars_by_tac :     env ->
    Evd.evar_defs ->
  Proof_type.tactic ->
  Evd.evar_defs

val refine_ref : (open_constr -> Proof_type.tactic) ref

val decompose_named_assum : types -> named_context * types

val push_named_context : named_context -> env -> env

val name_typeclass_binders : Idset.t ->
    Topconstr.local_binder list ->
    Topconstr.local_binder list * Idset.t
