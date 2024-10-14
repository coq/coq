(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Printf
open Index

let type_of_string = function
  | "def" | "coe" | "subclass" | "canonstruc" | "fix" | "cofix" | "ex"
   |"scheme" ->
    Definition
  | "prf" | "thm" -> Lemma
  | "ind" | "variant" | "coind" -> Inductive
  | "constr" -> Constructor
  | "indrec" | "rec" | "corec" -> Record
  | "proj" -> Projection
  | "class" -> Class
  | "meth" -> Method
  | "inst" -> Instance
  | "var" -> Variable
  | "defax" | "prfax" | "ax" -> Axiom
  | "abbrev" | "syndef" -> Abbreviation
  | "not" -> Notation
  | "lib" -> Library
  | "mod" | "modtype" -> Module
  | "tac" -> TacticDefinition
  | "sec" -> Section
  | "binder" -> Binder
  | s -> invalid_arg ("type_of_string:" ^ s)

let ill_formed_glob_file f =
  eprintf "Warning: ill-formed file %s (links will not be available)\n" f

let outdated_glob_file f =
  eprintf
    "Warning: %s not consistent with corresponding .v file (links will not be \
     available)\n"
    f

let correct_file vfile f c =
  let s = input_line c in
  if String.length s < 7 || String.sub s 0 7 <> "DIGEST " then (
    ill_formed_glob_file f; false )
  else
    let s = String.sub s 7 (String.length s - 7) in
    match (vfile, s) with
    | None, "NO" -> true
    | Some _, "NO" -> ill_formed_glob_file f; false
    | None, _ -> ill_formed_glob_file f; false
    | Some vfile, s ->
      s = Digest.to_hex (Digest.file vfile) || (outdated_glob_file f; false)

let read_glob vfile f =
  let c = open_in f in
  if correct_file vfile f c then
    let cur_mod = ref "" in
    try
      while true do
        let s = input_line c in
        let n = String.length s in
        if n > 0 then
          match s.[0] with
          | 'F' ->
            cur_mod := String.sub s 1 (n - 1);
            current_library := !cur_mod
          | 'R' -> (
            try
              Scanf.sscanf s "R%d:%d %s %s %s %s"
                (fun loc1 loc2 lib_dp sp id ty ->
                  for loc = loc1 to loc2 do
                    add_ref !cur_mod loc lib_dp sp id (type_of_string ty);
                    (* Also add an entry for each module mentioned in [lib_dp],
                     * to use in interpolation. *)
                    ignore
                      (List.fold_right
                         (fun thisPiece priorPieces ->
                           let newPieces =
                             match priorPieces with
                             | "" -> thisPiece
                             | _ -> thisPiece ^ "." ^ priorPieces
                           in
                           add_ref !cur_mod loc "" "" newPieces Library;
                           newPieces)
                         (Str.split (Str.regexp_string ".") lib_dp)
                         "")
                  done)
            with _ -> () )
          | _ -> (
            try
              Scanf.sscanf s "%s %d:%d %s %s" (fun ty loc1 loc2 sp id ->
                  add_def loc1 loc2 (type_of_string ty) sp id)
            with Scanf.Scan_failure _ -> () )
      done;
      assert false
    with End_of_file -> close_in c
