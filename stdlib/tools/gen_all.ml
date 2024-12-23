(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let from = "Stdlib"

let () = Printf.printf "Set Warnings \"-deprecated-library-file,-warn-library-file,-notation-incompatible-prefix,-notation-overridden,-overwriting-delimiting-key\".\n\n"

let logical_concat prefix f =
  let f = Filename.remove_extension f in
  match prefix with
  | "" -> f
  | _ -> String.concat "." [prefix; f]

let rec traverse todo todo' = match todo, todo' with
  | [], [] -> ()
  |  [], todo :: todo' -> traverse todo todo'
  | (path,logical) :: todo, todo' ->
    let todo' = match (Unix.stat path).st_kind with
      | exception Unix.Unix_error _ -> todo'
      | S_DIR ->
        let contents = try Sys.readdir path with Sys_error _ -> [||] in
        (* sort to get a reproducible ordering *)
        let () = Array.sort String.compare contents in
        let contents = Array.to_list contents in
        let contents = List.map (fun fname ->
            Filename.concat path fname, logical_concat logical fname)
            contents
        in
        (contents :: todo')
      | S_REG ->
        let () =
          if Filename.extension path = ".v" &&
             logical <> "All"
          then Printf.printf "From %s Require Export %s.\n" from logical
        in
        todo'
      | _ -> todo'
    in
    traverse todo todo'

let () = traverse [".", ""] []

let () = Printf.printf "%!"
