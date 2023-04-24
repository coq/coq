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

let warn_deprecated ~object_name ~warning_name_if_no_since since name_printer =
  let open Pp in
  let name =
    let space_dash s = String.map (function ' ' -> '-' | c -> c) s in
    Option.cata (fun s -> "deprecated-since-" ^ space_dash s)
      warning_name_if_no_since since in
  CWarnings.create ~name ~category:"deprecated"
    (fun (qid, note) -> str object_name ++ spc () ++ name_printer qid ++
      strbrk " is deprecated" ++
      pr_opt (fun since -> str "since " ++ str since) since ++
      str "." ++ pr_opt (fun note -> str note) note)

let create_warning ~object_name ~warning_name_if_no_since name_printer =
  let h = Hashtbl.create 19 in
  fun ?loc (qid, { since; note }) ->
    let w =
      try Hashtbl.find h since
      with Not_found ->
        let w = warn_deprecated ~object_name ~warning_name_if_no_since since
                  name_printer in
        Hashtbl.add h since w;
        w in
    w ?loc (qid, note)
