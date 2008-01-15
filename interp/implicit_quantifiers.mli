(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.ml 6748 2005-02-18 22:17:50Z herbelin $ i*)

(*i*)
open Names
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Rawterm
open Topconstr
open Util
open Typeclasses
(*i*)

val ids_of_list : identifier list -> Idset.t
val destClassApp : constr_expr -> identifier located * constr_expr list
val destClassAppExpl : constr_expr -> identifier located * (constr_expr * explicitation located option) list

val free_vars_of_constr_expr :     Topconstr.constr_expr ->
    ?bound:Idset.t ->
  Names.identifier list -> Names.identifier list

val binder_list_of_ids : identifier list -> local_binder list

val make_fresh : Names.Idset.t -> Environ.env -> identifier -> identifier

val free_vars_of_binders :
  ?bound:Idset.t -> Names.identifier list -> local_binder list -> Idset.t * Names.identifier list

val compute_constrs_freevars : Idset.t -> constr_expr list -> identifier list
val compute_constrs_freevars_binders : Idset.t -> constr_expr list -> (identifier located * constr_expr) list
val resolve_class_binders : Idset.t -> typeclass_context -> 
  (identifier located * constr_expr) list * typeclass_context

val full_class_binders : Idset.t -> typeclass_context -> typeclass_context
  
val generalize_class_binders_raw : Idset.t -> typeclass_context -> 
  (name located * binding_kind * constr_expr) list * (name located * binding_kind * constr_expr) list

val ctx_of_class_binders : Idset.t -> typeclass_context -> local_binder list

val implicits_of_binders : local_binder list -> (Topconstr.explicitation * (bool * bool)) list

val implicits_of_rawterm : Rawterm.rawconstr -> (Topconstr.explicitation * (bool * bool)) list

val nf_named_context : evar_map -> named_context -> named_context
val nf_rel_context : evar_map -> rel_context -> rel_context
val nf_env : evar_map -> env -> env

val combine_params : Names.Idset.t ->
  (Names.Idset.t -> (Names.identifier * bool) option * (Names.identifier * Term.constr option * Term.types) ->
    Topconstr.constr_expr * Names.Idset.t) ->
  (Topconstr.constr_expr * Topconstr.explicitation located option) list ->
  ((Names.identifier * bool) option * Term.named_declaration) list ->
  Topconstr.constr_expr list * Names.Idset.t


val ids_of_named_context_avoiding :     Names.Idset.t ->
    Sign.named_context -> Names.Idset.elt list * Names.Idset.t

