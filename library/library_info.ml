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

type t = UserWarn.t

let warn_library_deprecated =
  Deprecation.create_warning ~object_name:"Library File"
    ~warning_name_if_no_since:"deprecated-library-file"
    (fun dp -> DirPath.print dp)

let warn_library_warn =
  UserWarn.create_warning ~warning_name_if_no_cats:"warn-library-file" ()

let warn_library_deprecated_transitive =
  Deprecation.create_warning ~object_name:"Library File (transitively required)"
    ~warning_name_if_no_since:"deprecated-transitive-library-file"
    ~default:CWarnings.Disabled
    (fun dp -> DirPath.print dp)

let warn_library_warn_transitive =
  UserWarn.create_warning
    ~warning_name_if_no_cats:"warn-transitive-library-file"
    ~default:CWarnings.Disabled ()

let warn_library_info ?loc ?(transitive=false) dp infos =
  let open UserWarn in
  if transitive then begin
    Option.iter (fun depr ->
        warn_library_deprecated_transitive ?loc (dp, depr)) infos.depr;
    List.iter (fun warn -> warn_library_warn_transitive ?loc warn) infos.warn
  end else begin
    Option.iter (fun depr ->
        warn_library_deprecated ?loc (dp, depr)) infos.depr;
    List.iter (fun warn -> warn_library_warn ?loc warn) infos.warn
  end
