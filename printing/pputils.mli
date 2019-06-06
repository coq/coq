(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genarg

val pr_located : ('a -> Pp.t) -> 'a Loc.located -> Pp.t
val pr_ast : ('a -> Pp.t) -> 'a CAst.t -> Pp.t
(** Prints an object surrounded by its commented location *)

val pr_lident : lident -> Pp.t
val pr_lname : lname -> Pp.t
val pr_or_var : ('a -> Pp.t) -> 'a Locus.or_var -> Pp.t
val pr_or_by_notation : ('a -> Pp.t) -> 'a Constrexpr.or_by_notation -> Pp.t

val pr_raw_generic : Environ.env -> Evd.evar_map -> rlevel generic_argument -> Pp.t
val pr_glb_generic : Environ.env -> Evd.evar_map -> glevel generic_argument -> Pp.t

(* The comments interface is imperative due to the printer not
   threading it, this could be solved using a better data
   structure. *)
val beautify_comments : ((int * int) * string) list ref
val extract_comments : int -> string list
