(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CUnix
open Names

type section_path = {
  dirpath : string list;
  basename : string;
}

type object_file =
| PhysicalFile of physical_path
| LogicalFile of section_path

type logical_path = DirPath.t

val default_root_prefix : DirPath.t

val add_load_path : physical_path * logical_path -> unit

val recheck_library :
  norec:object_file list ->
  admit:object_file list ->
  check:object_file list -> unit
