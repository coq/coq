(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This API is loosely inspired by [Stdune.Path], for now we keep it
   minimal, but at some point we may extend it, see developer notes in
   the implementation file. *)

(* To be made opaque one day, for now we force users to go thru the
   constructor *)
type t = private string

(** [make path_components] build a path from its components *)
val make : string list -> t

(** [relative path string] build a path relative to an existing one *)
val relative : t -> string -> t

(** [choose_existing paths] will return [Some f] for the first file
   [f] in [paths] that exists, [None] otherwise. *)
val choose_existing : t list -> t option

(* We should gradually add some more functions to handle common dirs
   here such the theories directories or share files. Abstracting it
   here does allow to use system-specific functionalities *)
