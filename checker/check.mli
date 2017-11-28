(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CUnix
open Names

type section_path = {
  dirpath : string list;
  basename : string;
}

type logical_path = DirPath.t

val default_root_prefix : DirPath.t

val add_load_path : physical_path * logical_path -> unit

val recheck_library :
  norec:section_path list ->
  admit:section_path list ->
  check:section_path list -> unit
