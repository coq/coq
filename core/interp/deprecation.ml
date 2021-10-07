(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = { since : string option ; note : string option }

let make ?since ?note () = { since ; note }

let create_warning ~object_name ~warning_name name_printer =
  let open Pp in
  CWarnings.create ~name:warning_name ~category:"deprecated"
    (fun (qid,depr) -> str object_name ++ spc () ++ name_printer qid ++
      strbrk " is deprecated" ++
      pr_opt (fun since -> str "since " ++ str since) depr.since ++
      str "." ++ pr_opt (fun note -> str note) depr.note)
