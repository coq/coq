(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
open Symbol
(*i*)

(*s Declaration functions. The following functions take ASTs,
   transform them into [constr] and then call the corresponding
   functions of [Declare]; they return an absolute reference to the
   defined object *)

val declare_definition : identifier -> definition_kind ->
  local_binder list -> Tacred.red_expr option -> constr_expr ->
    constr_expr option -> global_reference

val syntax_definition : identifier -> constr_expr -> unit

val declare_assumption : identifier -> assumption_kind -> 
  local_binder list -> constr_expr -> global_reference

val build_mutual : inductive_expr list -> bool -> unit

val declare_mutual_with_eliminations :
  Entries.mutual_inductive_entry -> mutual_inductive

val build_recursive : fixpoint_expr list -> unit

val build_corecursive : cofixpoint_expr list -> unit

val build_scheme : (identifier * bool * reference * rawsort) list -> unit

val declare_symbol : identifier -> constr_expr -> int -> eqth -> status ->
  int list -> int list -> unit

val declare_rules : (identifier * constr_expr) list ->
  (identifier * constr_expr) list -> (constr_expr * constr_expr) list -> unit

val generalize_rawconstr : constr_expr -> local_binder list -> constr_expr

val start_proof : identifier -> goal_kind -> constr ->
  declaration_hook -> unit

val start_proof_com : identifier option -> goal_kind -> 
  (local_binder list * constr_expr) -> declaration_hook -> unit

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

(* [get_current_context ()] returns the evar context and env of the
   current open proof if any, otherwise returns the empty evar context
   and the current global env *)

val get_current_context : unit -> Evd.evar_map * Environ.env
