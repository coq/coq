(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Sign
open Term
open Libnames
open Nametab
open Decl_kinds
open Misctypes
open Locus
open Glob_term

(** Operations on [glob_constr] *)

val cases_pattern_loc : cases_pattern -> loc

val cases_predicate_names : tomatch_tuples -> name list

(** Apply one argument to a glob_constr *)
val mkGApp : loc -> glob_constr -> glob_constr -> glob_constr

val map_glob_constr :
  (glob_constr -> glob_constr) -> glob_constr -> glob_constr

(** Ensure traversal from left to right *)
val map_glob_constr_left_to_right :
  (glob_constr -> glob_constr) -> glob_constr -> glob_constr

val fold_glob_constr : ('a -> glob_constr -> 'a) -> 'a -> glob_constr -> 'a
val iter_glob_constr : (glob_constr -> unit) -> glob_constr -> unit
val occur_glob_constr : identifier -> glob_constr -> bool
val free_glob_vars : glob_constr -> identifier list
val loc_of_glob_constr : glob_constr -> loc

(** Conversion from glob_constr to cases pattern, if possible

    Take the current alias as parameter,
    @raise Not_found if translation is impossible *)
val cases_pattern_of_glob_constr : name -> glob_constr -> cases_pattern

val glob_constr_of_closed_cases_pattern : cases_pattern -> name * glob_constr
