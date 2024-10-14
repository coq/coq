(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [to_relative_path path] takes as input a file path [path], and constructs
    an equivalent relative path from the current working directory. If [path]
    is already relative, then it is returned immediately. *)
val to_relative_path : string -> string

(** [normalize_path path] takes as input a file path [path], and returns an
    equivalent path that: (1) does not contain the current directory member
    ["."] unless the path is to the current directory (in which case ["."]
    is returned, or ["./"] if [path] has a trailing ["/"]), (2) only uses
    parent directory members [".."] for a prefix of the path, and (3), has
    a trailing ["/"] only if and only if [path] does.

    For example, paths ["dir1/dir2/file.v"], ["."], ["dir1/dir2/dir3/"] and
    ["../../dir/file.v"] are possible return values, but ["./file.v"] and
    ["dir1/../dir2"] are not. *)
val normalize_path : string -> string
