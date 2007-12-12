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

type binder_list = (identifier located * constr_expr) list
type binder_def_list = (identifier located * identifier located list * constr_expr) list
 
val binders_of_lidents : identifier located list -> local_binder list

val declare_implicit_proj : typeclass -> constant -> unit

val infer_super_instances : env -> constr list ->
  named_context -> named_context -> types list * env * named_context


val new_class : identifier located ->
  binder_list ->
  Vernacexpr.sort_expr located ->
  typeclass_context ->
  binder_list -> unit

val new_instance : 
  typeclass_context ->
  identifier located option ->
  identifier located ->
  constr_expr list ->
  binder_def_list ->
  unit

val add_instance_hint : identifier -> unit

val declare_instance : identifier located -> unit

val set_instantiation_tactic : Tacexpr.raw_tactic_expr -> unit

val mismatched_params : env -> constr_expr list -> named_context -> 'a

val mismatched_props : env -> constr_expr list -> named_context -> 'a

val solve_by_tac :     env ->
    Evd.evar_defs ->
    Evd.evar ->
  evar_info ->
  Proof_type.tactic ->
    Evd.evar_defs * bool
