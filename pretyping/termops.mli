(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Util
open Pp
open Names
open Term
open Sign
open Environ

(* Universes *)
val new_univ : unit -> Univ.universe
val new_sort_in_family : sorts_family -> sorts
val new_Type : unit -> types
val new_Type_sort : unit -> sorts
val refresh_universes : types -> types
val refresh_universes_strict : types -> types

(* printers *)
val print_sort : sorts -> std_ppcmds
val pr_sort_family : sorts_family -> std_ppcmds
(* debug printer: do not use to display terms to the casual user... *)
val set_print_constr : (env -> constr -> std_ppcmds) -> unit
val print_constr     : constr -> std_ppcmds
val print_constr_env : env -> constr -> std_ppcmds
val print_named_context : env -> std_ppcmds
val pr_rel_decl : env -> rel_declaration -> std_ppcmds
val print_rel_context : env -> std_ppcmds
val print_env : env -> std_ppcmds

(* iterators on terms *)
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
val it_mkNamedProd_wo_LetIn   : init:types -> named_context -> types

(**********************************************************************)
(* Generic iterators on constr                                        *)

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

(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

val fold_constr_with_binders :
  ('a -> 'a) -> ('a -> 'b -> constr -> 'b) -> 'a -> 'b -> constr -> 'b

val iter_constr_with_full_binders :
  (rel_declaration -> 'a -> 'a) -> ('a -> constr -> unit) -> 'a -> 
    constr -> unit

(**********************************************************************)

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
val dependent : constr -> constr -> bool
val collect_metas : constr -> int list
(* Substitution of metavariables *)
type metamap = (metavariable * constr) list 
val subst_meta : metamap -> constr -> constr

(* [pop c] lifts by -1 the positive indexes in [c] *)
val pop : constr -> constr

(*s Substitution of an arbitrary large term. Uses equality modulo
   reduction of let *)

(* [subst_term_gen eq d c] replaces [Rel 1] by [d] in [c] using [eq]
   as equality *)
val subst_term_gen :
  (constr -> constr -> bool) -> constr -> constr -> constr

(* [replace_term_gen eq d e c] replaces [d] by [e] in [c] using [eq]
   as equality *)
val replace_term_gen :
  (constr -> constr -> bool) ->
    constr -> constr -> constr -> constr

(* [subst_term d c] replaces [Rel 1] by [d] in [c] *)
val subst_term : constr -> constr -> constr

(* [replace_term d e c] replaces [d] by [e] in [c] *)
val replace_term : constr -> constr -> constr -> constr

(* [subst_term_occ occl c d] replaces occurrences of [Rel 1] at
   positions [occl] by [c] in [d] *)
val subst_term_occ_gen : int list -> int -> constr -> types -> int * types

(* [subst_term_occ occl c d] replaces occurrences of [Rel 1] at
   positions [occl] by [c] in [d] (see also Note OCC) *)
val subst_term_occ : int list -> constr -> constr -> constr

(* [subst_term_occ_decl occl c decl] replaces occurrences of [Rel 1] at
   positions [occl] by [c] in [decl] *)
val subst_term_occ_decl :
  int list -> constr -> named_declaration -> named_declaration

val error_invalid_occurrence : int list -> 'a

(* Alternative term equalities *)
val base_sort_cmp : Reduction.conv_pb -> sorts -> sorts -> bool
val constr_cmp : Reduction.conv_pb -> constr -> constr -> bool
val eq_constr : constr -> constr -> bool

val eta_reduce_head : constr -> constr
val eta_eq_constr : constr -> constr -> bool

(* finding "intuitive" names to hypotheses *)
val lowercase_first_char : identifier -> string
val sort_hdchar : sorts -> string
val hdchar : env -> types -> string
val id_of_name_using_hdchar :
  env -> types -> name -> identifier
val named_hd : env -> types -> name -> name

val mkProd_name : env -> name * types * types -> types
val mkLambda_name : env -> name * types * constr -> constr

(* Deprecated synonyms of [mkProd_name] and [mkLambda_name] *)
val prod_name : env -> name * types * types -> types
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

val context_chop : int -> rel_context -> (rel_context*rel_context)

(* Set of local names *)
val vars_of_env: env -> Idset.t
val add_vname : Idset.t -> name -> Idset.t

(* sets of free identifiers *)
type used_idents = identifier list
val occur_rel : int -> name list -> identifier -> bool
val occur_id : name list -> identifier -> constr -> bool

type avoid_flags = bool option
 (* Some true = avoid all globals (as in intro); 
    Some false = avoid only global constructors; None = don't avoid globals *)

val next_name_away_in_cases_pattern : 
  name -> identifier list -> identifier
val next_global_ident_away : 
  (*allow section vars:*) bool -> identifier -> identifier list -> identifier
val next_name_not_occuring :
  avoid_flags -> name -> identifier list -> name list -> constr -> identifier
val concrete_name :
  avoid_flags -> identifier list -> name list -> name -> constr -> 
    name * identifier list
val concrete_let_name :
  avoid_flags -> identifier list -> name list -> name -> constr -> 
    name * identifier list
val rename_bound_var : env -> identifier list -> types -> types

(* other signature iterators *)
val process_rel_context : (rel_declaration -> env -> env) -> env -> env
val assums_of_rel_context : rel_context -> (name * constr) list
val lift_rel_context : int -> rel_context -> rel_context
val substl_rel_context : constr list -> rel_context -> rel_context
val map_rel_context_with_binders : 
  (int -> constr -> constr) -> rel_context -> rel_context
val fold_named_context_both_sides :
  ('a -> named_declaration -> named_declaration list -> 'a) ->
    named_context -> init:'a -> 'a
val mem_named_context : identifier -> named_context -> bool
val make_all_name_different : env -> env

val global_vars : env -> constr -> identifier list
val global_vars_set_of_decl : env -> named_declaration -> Idset.t

(* Test if an identifier is the basename of a global reference *)
val is_section_variable : identifier -> bool

val isGlobalRef : constr -> bool

val has_polymorphic_type : constant -> bool

(* Combinators on judgments *)

val on_judgment       : (types -> types) -> unsafe_judgment -> unsafe_judgment
val on_judgment_value : (types -> types) -> unsafe_judgment -> unsafe_judgment
val on_judgment_type  : (types -> types) -> unsafe_judgment -> unsafe_judgment
