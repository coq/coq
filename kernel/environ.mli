(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Declarations
open Univ
open Sign
(*i*)

(*s Unsafe environments. We define here a datatype for environments. 
   Since typing is not yet defined, it is not possible to check the
   informations added in environments, and that is why we speak here
   of ``unsafe'' environments. *)

type env

val empty_env : env

val universes : env -> universes
val rel_context : env -> rel_context
val named_context : env -> named_context

(* This forgets named and rel contexts *)
val reset_context : env -> env
(* This forgets rel context and sets a new named context *)
val reset_with_named_context : named_context -> env -> env

(*s This concerns only local vars referred by names [named_context] *)
val push_named_decl : named_declaration -> env -> env
val pop_named_decl : identifier -> env -> env

(*s This concerns only local vars referred by indice [rel_context] *)
val push_rel : rel_declaration -> env -> env
val push_rel_context : rel_context -> env -> env

(*s Push the types of a (co-)fixpoint to [rel_context] *)
val push_rec_types : rec_declaration -> env -> env

(*s Recurrence on [named_context]: older declarations processed first *)
val fold_named_context :
  (env -> named_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

(* Recurrence on [named_context] starting from younger decl *)
val fold_named_context_reverse :
  ('a -> named_declaration -> 'a) -> init:'a -> env -> 'a

(*s Recurrence on [rel_context] *)
val fold_rel_context :
  (env -> rel_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

(*s add entries to environment *)
val set_universes : universes -> env -> env
val add_constraints : constraints -> env -> env
val add_constant : 
  constant -> constant_body -> env -> env
val add_mind : 
  section_path -> mutual_inductive_body -> env -> env

(*s Lookups in environment *)

(* Looks up in the context of local vars referred by indice ([rel_context]) *)
(* raises [Not_found] if the index points out of the context *)
val lookup_rel : int -> env -> rel_declaration

(* Looks up in the context of local vars referred by names ([named_context]) *)
(* raises [Not_found] if the identifier is not found *)
val lookup_named : variable -> env -> named_declaration

(* Looks up in the context of global constant names *)
(* raises [Not_found] if the required path is not found *)
val lookup_constant : constant -> env -> constant_body

(*s [constant_value env c] raises [NotEvaluableConst Opaque] if
   [c] is opaque and [NotEvaluableConst NoBody] if it has no
   body and [Not_found] if it does not exist in [env] *)
type const_evaluation_result = NoBody | Opaque
exception NotEvaluableConst of const_evaluation_result

val constant_value : env -> constant -> constr
val constant_type : env -> constant -> types
val constant_opt_value : env -> constant -> constr option

(* Looks up in the context of global inductive names *)
(* raises [Not_found] if the required path is not found *)
val lookup_mind : section_path -> env -> mutual_inductive_body


(* [global_vars_set c] returns the list of [id]'s occurring as [VAR
    id] in [c] *)
val global_vars_set : env -> constr -> Idset.t
(* the constr must be an atomic construction *)
val vars_of_global : env -> constr -> identifier list

val keep_hyps : env -> Idset.t -> section_context

(* A constant is defined when it has a body (theorems do) *)
val defined_constant : env -> constant -> bool
(* A constant is evaluable when delta reduction applies (theorems don't) *)
val evaluable_constant : env -> constant -> bool

val evaluable_named_decl : env -> variable -> bool
val evaluable_rel_decl : env -> int -> bool

(*s Modules. *)

type compiled_env

val export : env -> dir_path -> compiled_env
val import : compiled_env -> env -> env

(*s Unsafe judgments. We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type unsafe_judgment = { 
  uj_val : constr;
  uj_type : types }

val make_judge : constr -> types -> unsafe_judgment
val j_val  : unsafe_judgment -> constr
val j_type : unsafe_judgment -> types

type unsafe_type_judgment = { 
  utj_val : constr;
  utj_type : sorts }
