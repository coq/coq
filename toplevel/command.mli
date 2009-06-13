(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Nametab
open Declare
open Library
open Libnames
open Nametab
open Tacexpr
open Vernacexpr
open Rawterm
open Topconstr
open Decl_kinds
open Redexpr
(*i*)

(*s Declaration functions. The following functions take ASTs,
   transform them into [constr] and then call the corresponding
   functions of [Declare]; they return an absolute reference to the
   defined object *)

val get_declare_definition_hook : unit -> (Entries.definition_entry -> unit)
val set_declare_definition_hook : (Entries.definition_entry -> unit) -> unit

val definition_message : identifier -> unit
val assumption_message : identifier -> unit

val declare_definition : identifier -> definition_kind ->
  local_binder list -> red_expr option -> constr_expr ->
  constr_expr option -> declaration_hook -> unit

val syntax_definition : identifier -> identifier list * constr_expr -> 
  bool -> bool -> unit

val declare_one_assumption : coercion_flag -> assumption_kind -> Term.types ->
  Impargs.manual_explicitation list ->
  bool (* implicit *) -> identifier list (* keep *) -> bool (* inline *) -> Names.variable located  -> unit
  
val set_declare_assumption_hook : (types -> unit) -> unit

val declare_assumption : identifier located list ->
  coercion_flag -> assumption_kind -> local_binder list -> constr_expr -> 
  bool -> identifier list -> bool -> unit

val declare_interning_data : 'a * Constrintern.implicits_env ->
    string * Topconstr.constr_expr * Topconstr.scope_name option -> unit

val compute_interning_datas : Environ.env -> Constrintern.var_internalisation_type -> 
  'a list -> 'b list ->
  Term.types list ->Impargs.manual_explicitation list list ->
  'a list *
    ('b * (Constrintern.var_internalisation_type * Names.identifier list * Impargs.implicits_list *
	      Topconstr.scope_name option list))
    list

val check_mutuality : Environ.env -> definition_object_kind ->
  (identifier * types) list -> unit

val build_mutual : ((lident * local_binder list * constr_expr option * constructor_expr list) * 
		                decl_notation) list -> bool -> unit

val declare_mutual_with_eliminations :
  bool -> Entries.mutual_inductive_entry -> 
  (Impargs.manual_explicitation list *
      Impargs.manual_explicitation list list) list ->
  mutual_inductive

type fixpoint_kind =
  | IsFixpoint of (identifier located option * recursion_order_expr) list
  | IsCoFixpoint

type fixpoint_expr = {
  fix_name : identifier;
  fix_binders : local_binder list;
  fix_body : constr_expr;
  fix_type : constr_expr
}

val recursive_message : definition_object_kind ->
  int array option -> identifier list -> Pp.std_ppcmds
  
val declare_fix : bool -> definition_object_kind -> identifier ->
  constr -> types -> Impargs.manual_explicitation list -> global_reference

val build_recursive : (Topconstr.fixpoint_expr * decl_notation) list -> bool -> unit

val build_corecursive : (Topconstr.cofixpoint_expr * decl_notation) list -> bool -> unit

val build_scheme : (identifier located option * scheme ) list -> unit

val build_combined_scheme : identifier located -> identifier located list -> unit

val generalize_constr_expr : constr_expr -> local_binder list -> constr_expr

val abstract_constr_expr : constr_expr -> local_binder list -> constr_expr

(* A hook start_proof calls on the type of the definition being started *)
val set_start_hook : (types -> unit) -> unit

val start_proof : identifier -> goal_kind -> types ->
  ?init_tac:Proof_type.tactic -> ?compute_guard:bool -> declaration_hook -> unit

val start_proof_com : goal_kind -> 
  (lident option * (local_binder list * constr_expr)) list ->
  declaration_hook -> unit

(* A hook the next three functions pass to cook_proof *)
val set_save_hook : (Refiner.pftreestate -> unit) -> unit

(*s [save_named b] saves the current completed proof under the name it
was started; boolean [b] tells if the theorem is declared opaque; it
fails if the proof is not completed *)

val save_named : bool -> unit

(* [save_anonymous b name] behaves as [save_named] but declares the theorem
under the name [name] and respects the strength of the declaration *)

val save_anonymous : bool -> identifier -> unit

(* [save_anonymous_with_strength s b name] behaves as [save_anonymous] but
   declares the theorem under the name [name] and gives it the
   strength [strength] *)

val save_anonymous_with_strength : theorem_kind -> bool -> identifier -> unit

(* [admit ()] aborts the current goal and save it as an assmumption *)

val admit : unit -> unit

(* [get_current_context ()] returns the evar context and env of the
   current open proof if any, otherwise returns the empty evar context
   and the current global env *)

val get_current_context : unit -> Evd.evar_map * Environ.env


