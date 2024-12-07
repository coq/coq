(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
  | Ml of string
  | Other of string (* filenames of dependencies, separated by spaces *)

  let compare a b = match a, b with
    | Require a, Require b | Ml a, Ml b | Other a, Other b -> CString.compare a b
    | Require _, _ -> -1
    | _, Require _ -> 1
    | Ml _, _ -> -1
    | _, Ml _ -> 1

  module Set = CSet.Make(struct
      type nonrec t = t
      let compare = compare
    end)
end

type t =
  { name : string  (* This should become [module : Coq_module.t] eventually *)
  ; deps : Dep.t list
  }

let make ~name ~deps = { name; deps }
