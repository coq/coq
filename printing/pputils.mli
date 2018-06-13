(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genarg
open Locus
open Genredexpr

val pr_located : ('a -> Pp.t) -> 'a Loc.located -> Pp.t
val pr_ast : ('a -> Pp.t) -> 'a CAst.t -> Pp.t
(** Prints an object surrounded by its commented location *)

val pr_or_var : ('a -> Pp.t) -> 'a or_var -> Pp.t
val pr_or_by_notation : ('a -> Pp.t) -> 'a Constrexpr.or_by_notation -> Pp.t
val pr_with_occurrences :
  ('a -> Pp.t) -> (string -> Pp.t) -> 'a with_occurrences -> Pp.t

val pr_short_red_flag : ('a -> Pp.t) -> 'a glob_red_flag -> Pp.t
val pr_red_flag : ('a -> Pp.t) -> 'a glob_red_flag -> Pp.t

val pr_red_expr :
  ('a -> Pp.t) * ('a -> Pp.t) * ('b -> Pp.t) * ('c -> Pp.t) ->
  (string -> Pp.t) -> ('a,'b,'c) red_expr_gen -> Pp.t

val pr_red_expr_env : Environ.env -> Evd.evar_map ->
  (Environ.env -> Evd.evar_map -> 'a -> Pp.t) *
  (Environ.env -> Evd.evar_map -> 'a -> Pp.t) *
  ('b -> Pp.t) *
  (Environ.env -> Evd.evar_map -> 'c -> Pp.t) ->
  (string -> Pp.t) ->
  ('a,'b,'c) red_expr_gen -> Pp.t

val pr_raw_generic : Environ.env -> rlevel generic_argument -> Pp.t
val pr_glb_generic : Environ.env -> glevel generic_argument -> Pp.t

(* The comments interface is imperative due to the printer not
   threading it, this could be solved using a better data
   structure. *)
val beautify_comments : ((int * int) * string) list ref
val extract_comments : int -> string list
