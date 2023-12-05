(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This handles attributes associated to a library file *)

(*i*)
open Names
(*i*)

type t = Deprecation of Deprecation.t

let warn_library_deprecated =
  Deprecation.create_warning ~object_name:"Library File"
    ~warning_name_if_no_since:"deprecated-library-file"
    (fun dp -> DirPath.print dp)

let warn_library_deprecated_transitive =
  Deprecation.create_warning ~object_name:"Library File (transitively required)"
    ~warning_name_if_no_since:"deprecated-transitive-library-file"
    ~default:CWarnings.Disabled
    (fun dp -> DirPath.print dp)

let warn_library_info ?loc ?(transitive=false) (dp,infos) =
  match infos with
  | Deprecation t ->
     if transitive then warn_library_deprecated_transitive ?loc (dp, t)
     else warn_library_deprecated ?loc (dp, t)
