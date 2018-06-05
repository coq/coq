(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Univ

(** The universes of monomorphic constants appear. *)
val universes_of_constr : Environ.env -> constr -> LSet.t

(** [restrict_universe_context (univs,csts) keep] restricts [univs] to
   the universes in [keep]. The constraints [csts] are adjusted so
   that transitive constraints between remaining universes (those in
   [keep] and those not in [univs]) are preserved. *)
val restrict_universe_context : ContextSet.t -> LSet.t -> ContextSet.t
