(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** false iff the module is an element of an open module type *)
val printable_body : DirPath.t -> bool

val pr_mutual_inductive_body : Environ.env ->
  MutInd.t -> Declarations.mutual_inductive_body ->
  UnivNames.univ_name_list option -> Pp.t
val print_module : bool -> ModPath.t -> Pp.t
val print_modtype : ModPath.t -> Pp.t
