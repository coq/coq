(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Printer

(** Collects all the objects on which a term directly relies, bypassing kernel
    opacity, together with the recursive dependence DAG of objects.

    WARNING: some terms may not make sense in the environment, because they are
    sealed inside opaque modules. Do not try to do anything fancy with those
    terms apart from printing them, otherwise demons may fly out of your nose.

    NOTE: this function is used in the plugin paramcoq.
*)
val traverse :
  Global.indirect_accessor -> Label.t -> constr ->
    (GlobRef.Set_env.t * GlobRef.Set_env.t option GlobRef.Map_env.t *
     (Label.t * Constr.rel_context * types) list GlobRef.Map_env.t)

(** Collects all the assumptions (optionally including opaque definitions)
   on which a term relies (together with their type). The above warning of
   {!traverse} also applies. *)
val assumptions :
  ?add_opaque:bool -> ?add_transparent:bool -> Global.indirect_accessor ->
  TransparentState.t -> GlobRef.t -> constr -> types ContextObjectMap.t
