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

(** * Load paths.

  A load path is a physical path in the file system; to each load path is
  associated a Coq [DirPath.t] (the "logical" path of the physical path).

*)

type t
(** Type of loadpath bindings. *)

val physical : t -> CUnix.physical_path
(** Get the physical path (filesystem location) of a loadpath. *)

val logical : t -> DirPath.t
(** Get the logical path (Coq module hierarchy) of a loadpath. *)

val get_load_paths : unit -> t list
(** Get the current loadpath association. *)

val add_load_path : CUnix.physical_path -> DirPath.t -> implicit:bool -> unit
(** [add_load_path phys log type] adds the binding [phys := log] to the current
    loadpaths. *)

val remove_load_path : CUnix.physical_path -> unit
(** Remove the current logical path binding associated to a given physical path,
    if any. *)

val find_load_path : CUnix.physical_path -> t
(** Get the binding associated to a physical path. Raises [Not_found] if there
    is none. *)

val is_in_load_paths : CUnix.physical_path -> bool
(** Whether a physical path is currently bound. *)

val expand_path : ?root:DirPath.t -> DirPath.t -> (CUnix.physical_path * DirPath.t) list
(** Given a relative logical path, associate the list of absolute physical and
    logical paths which are possible matches of it. *)

val filter_path : (DirPath.t -> bool) -> (CUnix.physical_path * DirPath.t) list
(** As {!expand_path} but uses a filter function instead, and ignores the
    implicit status of loadpaths. *)

val locate_file : string -> string
(** Locate a file among the registered paths. Do not use this function, as
    it does not respect the visibility of paths. *)
