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
open Constr
open Globnames
open Printer

(** Collects all the objects on which a term directly relies, bypassing kernel
    opacity, together with the recursive dependence DAG of objects.

    WARNING: some terms may not make sense in the environment, because they are
    sealed inside opaque modules. Do not try to do anything fancy with those
    terms apart from printing them, otherwise demons may fly out of your nose.
*)
val traverse :
  Label.t -> constr ->
    (Refset_env.t * Refset_env.t Refmap_env.t *
     (Label.t * Constr.rel_context * types) list Refmap_env.t)

(** Collects all the assumptions (optionally including opaque definitions)
   on which a term relies (together with their type). The above warning of
   {!traverse} also applies. *)
val assumptions :
  ?add_opaque:bool -> ?add_transparent:bool -> transparent_state ->
     GlobRef.t -> constr -> types ContextObjectMap.t
