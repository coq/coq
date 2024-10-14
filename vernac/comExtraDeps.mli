(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val declare_extra_dep :
  ?loc:Loc.t -> from:Names.DirPath.t -> file:string -> Names.Id.t option -> unit

val query_extra_dep : Names.Id.t -> string
(* @raise Not_found *)
