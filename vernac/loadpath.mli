(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

val physical : t -> CUnix.physical_path
(** Get the physical path of a loadpath *)

val pp : t -> Pp.t
(** Print a load path *)

val get_load_paths : unit -> t list
(** Get the current loadpath association. *)

val remove_load_path : CUnix.physical_path -> unit
(** Remove the current logical path binding associated to a given physical path,
    if any. *)

val find_load_path : CUnix.physical_path -> t
(** Get the binding associated with a physical path. Raises [Not_found] if there
    is none. *)

val find_with_logical_path : Names.DirPath.t -> t list
(** get the list of load paths that correspond to a given logical path *)

val find_extra_dep_with_logical_path :
  ?loc:Loc.t -> from:Names.DirPath.t -> file:string -> unit -> CUnix.physical_path
(** finds a file rooted in from. @raise UserError if the file is not found *)

val locate_file : string -> string
(** Locate a file among the registered paths. Do not use this function, as
    it does not respect the visibility of paths. *)

(** {6 Locate a library in the load path } *)
type library_location = LibLoaded | LibInPath
type locate_error = LibUnmappedDir | LibNotFound
type 'a locate_result = ('a, locate_error) result

val locate_qualified_library
  :  ?root:DirPath.t
  -> Libnames.qualid
  -> (library_location * DirPath.t * CUnix.physical_path) locate_result

(** Locates a library by implicit name.

  @raise LibUnmappedDir if the library is not in the path
  @raise LibNotFound if there is no corresponding file in the path

*)

val try_locate_absolute_library : DirPath.t -> string

(** {6 Extending the Load Path } *)

(** Adds a path to the Coq and ML paths *)
type vo_path =
  { unix_path : string
  (** Filesystem path containing vo/ml files *)
  ; coq_path  : DirPath.t
  (** Coq prefix for the path *)
  ; implicit  : bool
  (** [implicit = true] avoids having to qualify with [coq_path] *)
  ; has_ml    : bool
  (** If [has_ml] is true, the directory will also be added to the ml include path *)
  ; recursive : bool
  (** [recursive] will determine whether we explore sub-directories  *)
  }

val add_vo_path : vo_path -> unit
