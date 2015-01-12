(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** * Load paths.

  A load path is a physical path in the file system; to each load path is
  associated a Coq [DirPath.t] (the "logical" path of the physical path).

*)

type path_type =
  | ImplicitPath     (** Can be implicitly appended to a logical path. *)
  | ImplicitRootPath (** Can be implicitly appended to the suffix of a logical path. *)
  | RootPath         (** Can only be a prefix of a logical path. *)

type t
(** Type of loadpath bindings. *)

val physical : t -> CUnix.physical_path
(** Get the physical path (filesystem location) of a loadpath. *)

val logical : t -> DirPath.t
(** Get the logical path (Coq module hierarchy) of a loadpath. *)

val get_load_paths : unit -> t list
(** Get the current loadpath association. *)

val get_paths : unit -> CUnix.physical_path list
(** Same as [get_load_paths] but only get the physical part. *)

val add_load_path : CUnix.physical_path -> path_type -> DirPath.t -> unit
(** [add_load_path phys type log] adds the binding [phys := log] to the current
    loadpaths. *)

val remove_load_path : CUnix.physical_path -> unit
(** Remove the current logical path binding associated to a given physical path,
    if any. *)

val find_load_path : CUnix.physical_path -> t
(** Get the binding associated to a physical path. Raises [Not_found] if there
    is none. *)

val is_in_load_paths : CUnix.physical_path -> bool
(** Whether a physical path is currently bound. *)

val expand_path : DirPath.t -> (CUnix.physical_path * DirPath.t) list
(** Given a relative logical path, associate the list of absolute physical and
    logical paths which are possible expansions of it. *)

val expand_root_path : DirPath.t -> CUnix.physical_path list
(** As [expand_path] but restricts to root loadpaths. *)
