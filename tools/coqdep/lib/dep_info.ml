(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Dep = struct
  type t =
  | Require of string (* one basename, to which we later append .vo or .vos *)
  | Ml of string * string
  | Other of string (* filenames of dependencies, separated by spaces *)
end

type t =
  { name : string  (* This should become [module : Coq_module.t] eventually *)
  ; deps : Dep.t list
  }

let make ~name ~deps = { name; deps }
