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
open Term
open Declarations
open Sign
(*i*)

(*s Unsafe environments. We define here a datatype for environments. 
   Since typing is not yet defined, it is not possible to check the
   informations added in environments, and that is why we speak here
   of ``unsafe'' environments. *)

(* Environments have the following components:
   - a context for de Bruijn variables
   - a context for section variables and goal assumptions
   - a context for global constants and axioms
   - a context for inductive definitions
   - a set of universe constraints
   - a flag telling if Set is, can be, or cannot be set impredicative *)

type env

val empty_env : env

val universes     : env -> Univ.universes
val rel_context   : env -> rel_context
val named_context : env -> named_context

type engagement = ImpredicativeSet

val engagement    : env -> engagement option

(* is the local context empty *)
val empty_context : env -> bool

(************************************************************************)
(*s Context of de Bruijn variables (rel_context) *)
val push_rel         : rel_declaration -> env -> env
val push_rel_context :     rel_context -> env -> env
val push_rec_types   : rec_declaration -> env -> env

(* Looks up in the context of local vars referred by indice ([rel_context]) *)
(* raises [Not_found] if the index points out of the context *)
val lookup_rel    : int -> env -> rel_declaration
val evaluable_rel : int -> env -> bool

(*s Recurrence on [rel_context] *)
val fold_rel_context :
  (env -> rel_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

(************************************************************************)
(* Context of variables (section variables and goal assumptions) *)
val push_named : named_declaration -> env -> env

(* Looks up in the context of local vars referred by names ([named_context]) *)
(* raises [Not_found] if the identifier is not found *)
val lookup_named    : variable -> env -> named_declaration
val evaluable_named : variable -> env -> bool

(*s Recurrence on [named_context]: older declarations processed first *)
val fold_named_context :
  (env -> named_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

(* Recurrence on [named_context] starting from younger decl *)
val fold_named_context_reverse :
  ('a -> named_declaration -> 'a) -> init:'a -> env -> 'a

(* This forgets named and rel contexts *)
val reset_context : env -> env
(* This forgets rel context and sets a new named context *)
val reset_with_named_context : named_context -> env -> env

(************************************************************************)
(*s Global constants *)
(*s Add entries to global environment *)
val add_constant : constant -> constant_body -> env -> env

(* Looks up in the context of global constant names *)
(* raises [Not_found] if the required path is not found *)
val lookup_constant    : constant -> env -> constant_body
val evaluable_constant : constant -> env -> bool

(*s [constant_value env c] raises [NotEvaluableConst Opaque] if
   [c] is opaque and [NotEvaluableConst NoBody] if it has no
   body and [Not_found] if it does not exist in [env] *)
type const_evaluation_result = NoBody | Opaque
exception NotEvaluableConst of const_evaluation_result

val constant_value     : env -> constant -> constr
val constant_type      : env -> constant -> types
val constant_opt_value : env -> constant -> constr option

(************************************************************************)
(*s Inductive types *)
val add_mind : mutual_inductive -> mutual_inductive_body -> env -> env

(* Looks up in the context of global inductive names *)
(* raises [Not_found] if the required path is not found *)
val lookup_mind : mutual_inductive -> env -> mutual_inductive_body

(************************************************************************)
(*s Modules *)
val add_modtype : kernel_name -> module_type_body -> env -> env

(* [shallow_add_module] does not add module components *)
val shallow_add_module : module_path -> module_body -> env -> env

val lookup_module : module_path -> env -> module_body
val lookup_modtype : kernel_name -> env -> module_type_body

(************************************************************************)
(*s Universe constraints *)
val set_universes   :   Univ.universes -> env -> env
val add_constraints : Univ.constraints -> env -> env

val set_engagement : engagement -> env -> env

(************************************************************************)
(* Sets of referred section variables *)
(* [global_vars_set env c] returns the list of [id]'s occurring as
   [VAR id] in [c] *)
val global_vars_set : env -> constr -> Idset.t
(* the constr must be an atomic construction *)
val vars_of_global : env -> constr -> identifier list

val keep_hyps : env -> Idset.t -> section_context

(************************************************************************)
(*s Unsafe judgments. We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type unsafe_judgment = { 
  uj_val  : constr;
  uj_type : types }

val make_judge : constr -> types -> unsafe_judgment
val j_val  : unsafe_judgment -> constr
val j_type : unsafe_judgment -> types

type unsafe_type_judgment = { 
  utj_val  : constr;
  utj_type : sorts }






