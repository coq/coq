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

(** Collects all the objects on which terms directly rely, bypassing kernel
    opacity, together with the recursive dependence DAG of objects.

    WARNING: some terms may not make sense in the environment, because they are
    sealed inside opaque modules. Do not try to do anything fancy with those
    terms apart from printing them, otherwise demons may fly out of your nose.

    NOTE: this function is used in the plugins paramcoq and metarocq.
*)
val traverse :
  Global.indirect_accessor -> GlobRef.t list ->
    (GlobRef.Set.t * GlobRef.Set.t option GlobRef.Map.t *
     (GlobRef.t * Constr.rel_context * types) list GlobRef.Map.t)

(** Collects all the assumptions (optionally including opaque definitions)
   on which terms rely (together with their type). The above warning of
   {!traverse} also applies. *)
val assumptions :
  ?add_opaque:bool -> ?add_transparent:bool -> Global.indirect_accessor ->
  TransparentState.t -> GlobRef.t list ->
  theory_assumptions * types ContextObjectMap.t

(** Reports each reference separately, sharing loaded constant bodies only
    within this call. The warning on {!traverse} also applies. *)
val assumptions_per_reference :
  ?add_opaque:bool -> ?add_transparent:bool -> Global.indirect_accessor ->
  TransparentState.t -> GlobRef.t list ->
  (GlobRef.t * (theory_assumptions * types ContextObjectMap.t)) list
