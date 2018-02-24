(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** false iff the module is an element of an open module type *)
val printable_body : DirPath.t -> bool

val pr_mutual_inductive_body : Environ.env ->
  MutInd.t -> Declarations.mutual_inductive_body ->
  Universes.univ_name_list option -> Pp.t
val print_module : bool -> ModPath.t -> Pp.t
val print_modtype : ModPath.t -> Pp.t
