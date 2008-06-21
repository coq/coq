(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

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

(* Errors *)

val mismatched_params : env -> constr_expr list -> rel_context -> 'a

val mismatched_props : env -> constr_expr list -> rel_context -> 'a

type binder_list = (identifier located * bool * constr_expr) list
type binder_def_list = (identifier located * identifier located list * constr_expr) list
 
val binders_of_lidents : identifier located list -> local_binder list

val name_typeclass_binders : Idset.t ->
    Topconstr.local_binder list ->
    Topconstr.local_binder list * Idset.t

val declare_implicit_proj : typeclass -> (identifier * constant) -> 
  Impargs.manual_explicitation list -> bool -> unit

val new_class : identifier located ->
  local_binder list ->
  Vernacexpr.sort_expr located option ->
  local_binder list ->
  binder_list -> unit

(* By default, print the free variables that are implicitely generalized. *)

val default_on_free_vars : identifier list -> unit

val fail_on_free_vars : identifier list -> unit

(* Instance declaration *)

val declare_instance : bool -> identifier located -> unit

val declare_instance_constant :
  typeclass ->
  int option -> (* priority *)
  bool -> (* globality *)
  Impargs.manual_explicitation list -> (* implicits *)
  ?hook:(Names.constant -> unit) ->
  identifier -> (* name *)
  Term.constr -> (* body *)
  Term.types -> (* type *)
  Names.identifier
    
val new_instance : 
  ?global:bool -> (* Not global by default. *)
  local_binder list ->
  typeclass_constraint ->
  binder_def_list ->
  ?on_free_vars:(identifier list -> unit) ->
  ?tac:Proof_type.tactic  ->
  ?hook:(constant -> unit) ->
  int option ->
  identifier

(* For generation on names based on classes only *)

val id_of_class : typeclass -> identifier

(* Context command *)    

val context : ?hook:(Libnames.global_reference -> unit) -> typeclass_context -> unit

(* Forward ref for refine *)

val refine_ref : (open_constr -> Proof_type.tactic) ref

