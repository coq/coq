(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Term
open Sign
open Environ

(* Universes *)
val set_module : Names.dir_path -> unit
val new_univ : unit -> Univ.universe
val new_sort_in_family : sorts_family -> sorts

(* iterators on terms *)
val print_sort : sorts -> std_ppcmds
val print_sort_family : sorts_family -> std_ppcmds
val prod_it : init:types -> (name * types) list -> types
val lam_it : init:constr -> (name * types) list -> constr
val rel_vect : int -> int -> constr array
val rel_list : int -> int -> constr list
val extended_rel_list : int -> rel_context -> constr list
val extended_rel_vect : int -> rel_context -> constr array
val push_rel_assum : name * types -> env -> env
val push_rels_assum : (name * types) list -> env -> env
val push_named_rec_types : name array * types array * 'a -> env -> env
val lookup_rel_id : identifier -> rel_context -> int * types
val mkProd_or_LetIn : rel_declaration -> types -> types
val mkProd_wo_LetIn : rel_declaration -> types -> types
val it_mkProd_wo_LetIn : init:types -> rel_context -> types
val it_mkProd_or_LetIn   : init:types -> rel_context -> types
val it_mkLambda_or_LetIn : init:constr -> rel_context -> constr
val it_named_context_quantifier :
  (named_declaration -> 'a -> 'a) -> init:'a -> named_context -> 'a
val it_mkNamedProd_or_LetIn   : init:types -> named_context -> types
val it_mkNamedLambda_or_LetIn : init:constr -> named_context -> constr

val map_constr_with_named_binders :
  (name -> 'a -> 'a) ->
  ('a -> constr -> constr) -> 'a -> constr -> constr
val map_constr_with_binders_left_to_right :
  (rel_declaration -> 'a -> 'a) -> 
  ('a -> constr -> constr) ->
    'a -> constr -> constr
val map_constr_with_full_binders :
  (rel_declaration -> 'a -> 'a) ->
  ('a -> constr -> constr) -> 'a -> constr -> constr

val strip_head_cast : constr -> constr

(* occur checks *)
exception Occur
val occur_meta : types -> bool
val occur_existential : types -> bool
val occur_const : constant -> types -> bool
val occur_evar : existential_key -> types -> bool
val occur_in_global : env -> identifier -> constr -> unit
val occur_var : env -> identifier -> types -> bool
val occur_var_in_decl :
  env ->
  identifier -> 'a * types option * types -> bool
val occur_term : constr -> constr -> bool
val free_rels : constr -> Intset.t

(* Substitution of metavariables *)
val subst_meta : (int * constr) list -> constr -> constr

(* Expansion of local definitions *)
val whd_locals : env -> constr -> constr
val nf_locals  : env -> constr -> constr

(* [pop c] lifts by -1 the positive indexes in [c] *)
val pop : constr -> constr

(* substitution of an arbitrary large term. Uses equality modulo
   reduction of let *)
val dependent : constr -> constr -> bool
val subst_term_gen :
  (env -> constr -> constr -> bool) -> env -> constr -> constr -> constr
val replace_term_gen :
  (env -> constr -> constr -> bool) ->
    env -> constr -> constr -> constr -> constr
val subst_term : constr -> constr -> constr
val replace_term : constr -> constr -> constr -> constr
val subst_term_occ_gen :
  env -> int list -> int -> constr -> types -> int * types
val subst_term_occ : env -> int list -> constr -> types -> types
val subst_term_occ_decl :
  env -> int list -> constr -> named_declaration -> named_declaration

(* Alternative term equalities *)
val zeta_eq_constr : constr -> constr -> bool
val eta_reduce_head : constr -> constr
val eta_eq_constr : constr -> constr -> bool

(* finding "intuitive" names to hypotheses *)
val first_char : identifier -> string
val lowercase_first_char : identifier -> string
(*val id_of_global : env -> Libnames.global_reference -> identifier*)
val sort_hdchar : sorts -> string
val hdchar : env -> types -> string
val id_of_name_using_hdchar :
  env -> types -> name -> identifier
val named_hd : env -> types -> name -> name
val named_hd_type : env -> types -> name -> name
val prod_name : env -> name * types * types -> constr
val lambda_name : env -> name * types * constr -> constr
val prod_create : env -> types * types -> constr
val lambda_create : env -> types * constr -> constr
val name_assumption : env -> rel_declaration -> rel_declaration
val name_context : env -> rel_context -> rel_context

val mkProd_or_LetIn_name : env -> types -> rel_declaration -> types
val mkLambda_or_LetIn_name : env -> constr -> rel_declaration -> constr
val it_mkProd_or_LetIn_name   : env -> types -> rel_context -> types
val it_mkLambda_or_LetIn_name : env -> constr -> rel_context -> constr

(* name contexts *)
type names_context = name list
val add_name : name -> names_context -> names_context
val lookup_name_of_rel : int -> names_context -> name
val lookup_rel_of_name : identifier -> names_context -> int
val empty_names_context : names_context
val ids_of_rel_context : rel_context -> identifier list
val ids_of_named_context : named_context -> identifier list
val ids_of_context : env -> identifier list
val names_of_rel_context : env -> names_context

(* sets of free identifiers *)
type used_idents = identifier list
val occur_rel : int -> name list -> identifier -> bool
val occur_id : env -> name list -> identifier -> constr -> bool

val next_name_not_occuring :
  env -> name -> identifier list -> name list -> constr -> identifier
val concrete_name :
  env -> identifier list -> name list -> name ->
  constr -> identifier option * identifier list
val concrete_let_name :
  env -> identifier list -> name list ->
  name -> constr -> name * identifier list
val rename_bound_var : env -> identifier list -> types -> types

(* other signature iterators *)
val process_rel_context : (rel_declaration -> env -> env) -> env -> env
val assums_of_rel_context : rel_context -> (name * constr) list
val lift_rel_context : int -> rel_context -> rel_context
val fold_named_context_both_sides :
  ('a -> named_declaration -> named_declaration list -> 'a) ->
    named_context -> init:'a -> 'a
val mem_named_context : identifier -> named_context -> bool
val make_all_name_different : env -> env

val global_vars : env -> constr -> identifier list
val global_vars_set_of_decl : env -> named_declaration -> Idset.t
