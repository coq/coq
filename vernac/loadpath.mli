(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

val logical : t -> DirPath.t
(** Get the logical path (Coq module hierarchy) of a loadpath. *)

val pp : t -> Pp.t
(** Print a load path *)

val get_load_paths : unit -> t list
(** Get the current loadpath association. *)

val remove_load_path : CUnix.physical_path -> unit
(** Remove the current logical path binding associated to a given physical path,
    if any. *)

val find_load_path : CUnix.physical_path -> t
(** Get the binding associated to a physical path. Raises [Not_found] if there
    is none. *)

val locate_file : string -> string
(** Locate a file among the registered paths. Do not use this function, as
    it does not respect the visibility of paths. *)

(** {6 Locate a library in the load path } *)
type library_location = LibLoaded | LibInPath
type locate_error = LibUnmappedDir | LibNotFound
type 'a locate_result = ('a, locate_error) result

val locate_qualified_library
  :  ?root:DirPath.t
  -> ?warn:bool
  -> Libnames.qualid
  -> (library_location * DirPath.t * CUnix.physical_path) locate_result

(** Locates a library by implicit name.

  @raise LibUnmappedDir if the library is not in the path
  @raise LibNotFound if there is no corresponding file in the path

*)

val try_locate_absolute_library : DirPath.t -> string

(** {6 Extending the Load Path } *)

(** Adds a path to the Coq and ML paths *)
type add_ml = AddNoML | AddTopML | AddRecML

type vo_path_spec = {
  unix_path : string;
  (** Filesystem path containing vo/ml files *)
  coq_path  : Names.DirPath.t;
  (** Coq prefix for the path *)
  implicit  : bool;
  (** [implicit = true] avoids having to qualify with [coq_path] *)
  has_ml    : add_ml;
  (** If [has_ml] is true, the directory will also be search for plugins *)
}

type coq_path_spec =
  | VoPath of vo_path_spec
  | MlPath of string

type coq_path = {
  path_spec: coq_path_spec;
  recursive: bool;
}

val add_coq_path : coq_path -> unit
