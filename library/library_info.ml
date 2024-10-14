(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

type t = UserWarn.t

let warn_library =
  UserWarn.create_depr_and_user_warnings
    ~object_name:"Library File"
    ~warning_name_base:"library-file"
    (fun dp -> DirPath.print dp)
    ()

let warn_library_transitive =
  UserWarn.create_depr_and_user_warnings ~object_name:"Library File (transitively required)"
    ~warning_name_base:"transitive-library-file"
    ~default:CWarnings.Disabled
    (fun dp -> DirPath.print dp)
    ()

let warn_library_info ?loc ?(transitive=false) dp infos =
  if transitive then warn_library_transitive ?loc dp infos
  else warn_library ?loc dp infos
