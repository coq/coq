(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genarg

(** {5 Substitution functions} *)

type 'glb subst_fun = Mod_subst.substitution -> 'glb -> 'glb
(** The type of functions used for substituting generic arguments. *)

val substitute : ('raw, 'glb, 'top) genarg_type -> 'glb subst_fun

val generic_substitute : glob_generic_argument subst_fun

val register_subst0 : ('raw, 'glb, 'top) genarg_type ->
  'glb subst_fun -> unit
