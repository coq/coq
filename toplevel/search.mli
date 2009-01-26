(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Names
open Term
open Environ
open Pattern
open Libnames
open Nametab

(*s Search facilities. *)

type glob_search_about_item =
  | GlobSearchSubPattern of constr_pattern
  | GlobSearchString of string

val search_by_head : constr -> dir_path list * bool -> unit
val search_rewrite : constr -> dir_path list * bool -> unit
val search_pattern : constr -> dir_path list * bool -> unit
val search_about  : 
  (bool * glob_search_about_item) list -> dir_path list * bool -> unit

(* The filtering function that is by standard search facilities.
   It can be passed as argument to the raw search functions.
   It is used in pcoq. *)

val filter_by_module_from_list :
  dir_path list * bool -> global_reference -> env -> 'a -> bool

(* raw search functions can be used for various extensions.
   They are also used for pcoq. *)
val gen_filtered_search : (global_reference -> env -> constr -> bool) ->
      (global_reference -> env -> constr -> unit) -> unit
val filtered_search : (global_reference -> env -> constr -> bool) -> 
  (global_reference -> env -> constr -> unit) -> global_reference -> unit
val raw_pattern_search : (global_reference -> env -> constr -> bool) ->
  (global_reference -> env -> constr -> unit) -> constr_pattern -> unit
val raw_search_rewrite : (global_reference -> env -> constr -> bool) ->
  (global_reference -> env -> constr -> unit) -> constr_pattern -> unit
val raw_search_about : (global_reference -> env -> constr -> bool) ->
  (global_reference -> env -> constr -> unit) -> 
      (bool * glob_search_about_item) list -> unit
val raw_search_by_head : (global_reference -> env -> constr -> bool) ->
  (global_reference -> env -> constr -> unit) -> constr_pattern -> unit
