(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context
open Termops
open Environ
open Libnames
open Globnames
open Glob_term
open Pattern
open Constrexpr
open Notation_term
open Notation
open Misctypes

(** Translation of pattern, cases pattern, glob_constr and term into syntax
   trees for printing *)

val extern_cases_pattern : Id.Set.t -> cases_pattern -> cases_pattern_expr
val extern_glob_constr : Id.Set.t -> glob_constr -> constr_expr
val extern_glob_type : Id.Set.t -> glob_constr -> constr_expr
val extern_constr_pattern : names_context -> Evd.evar_map ->
  constr_pattern -> constr_expr
val extern_closed_glob : ?lax:bool -> bool -> env -> Evd.evar_map -> closed_glob_constr -> constr_expr

(** If [b=true] in [extern_constr b env c] then the variables in the first
   level of quantification clashing with the variables in [env] are renamed.
    ~lax is for debug printing, when the constr might not be well typed in 
    env, sigma
*)

val extern_constr : ?lax:bool -> bool -> env -> Evd.evar_map -> constr -> constr_expr
val extern_constr_in_scope : bool -> scope_name -> env -> Evd.evar_map -> constr -> constr_expr
val extern_reference : Loc.t -> Id.Set.t -> global_reference -> reference
val extern_type : bool -> env -> Evd.evar_map -> types -> constr_expr
val extern_sort : Evd.evar_map -> sorts -> glob_sort
val extern_rel_context : constr option -> env -> Evd.evar_map ->
  rel_context -> local_binder list

(** Printing options *)
val print_implicits : bool ref
val print_implicits_defensive : bool ref
val print_arguments : bool ref
val print_evar_arguments : bool ref
val print_coercions : bool ref
val print_universes : bool ref
val print_no_symbol : bool ref
val print_projections : bool ref

(** Customization of the global_reference printer *)
val set_extern_reference :
  (Loc.t -> Id.Set.t -> global_reference -> reference) -> unit
val get_extern_reference :
  unit -> (Loc.t -> Id.Set.t -> global_reference -> reference)

(** This governs printing of implicit arguments. If [with_implicits] is
   on and not [with_arguments] then implicit args are printed prefixed
   by "!"; if [with_implicits] and [with_arguments] are both on the
   function and not the arguments is prefixed by "!" *)
val with_implicits : ('a -> 'b) -> 'a -> 'b
val with_arguments : ('a -> 'b) -> 'a -> 'b

(** This forces printing of coercions *)
val with_coercions : ('a -> 'b) -> 'a -> 'b

(** This forces printing universe names of Type\{.\} *)
val with_universes : ('a -> 'b) -> 'a -> 'b

(** This suppresses printing of primitive tokens and notations *)
val without_symbols : ('a -> 'b) -> 'a -> 'b

(** This suppresses printing of specific notations only *)
val without_specific_symbols : interp_rule list -> ('a -> 'b) -> 'a -> 'b

(** This prints metas as anonymous holes *)
val with_meta_as_hole : ('a -> 'b) -> 'a -> 'b
