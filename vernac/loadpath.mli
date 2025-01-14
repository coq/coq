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

(** * Load paths.

  A load path is a physical path in the file system; to each load path is
  associated a Rocq [DirPath.t] (the "logical" path of the physical path).

*)

type t
(** Type of loadpath bindings. *)

val logical : t -> DirPath.t
(** Get the logical path (Rocq module hierarchy) of a loadpath. *)

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
module Error : sig
  type t = LibUnmappedDir | LibNotFound

  (** Raise regular Rocq errors with default informative message;
      usually document managers that have more information about the
      workspace than rocq compile will override this with a better
      mechanism / message. *)
  val raise : DirPath.t -> t -> 'a
end

val locate_qualified_library
  :  ?root:DirPath.t
  -> Libnames.qualid
  -> (DirPath.t * CUnix.physical_path, Error.t) Result.t

(** Locates a library by implicit name.

  @return LibUnmappedDir if the library is not in the path
  @return LibNotFound if there is no corresponding file in the path

*)
val locate_absolute_library : DirPath.t -> (CUnix.physical_path, Error.t) Result.t

(** {6 Extending the Load Path } *)

(** Adds a path to the Rocq and ML paths *)
type vo_path =
  { unix_path : string
  (** Filesystem path containing vo/ml files *)
  ; coq_path  : DirPath.t
  (** Rocq prefix for the path *)
  ; implicit  : bool
  (** [implicit = true] avoids having to qualify with [coq_path]
      true for -R, false for -Q in command line *)
  ; recursive : bool
  (** [recursive] will determine whether we explore sub-directories  *)
  }

val add_vo_path : vo_path -> unit
