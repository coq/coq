(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(***************************)
(* Specific coqtop options *)

type run_mode = Interactive | Batch

type t = {
  run_mode : run_mode;
}

let default = {
  run_mode = Interactive;
}

let parse arglist =
  let args = ref arglist in
  let extras = ref [] in
  let rec parse (oval : t) = match !args with
    | [] ->
      (oval, List.rev !extras)
    | opt :: rem ->
      args := rem;
      let noval : t = begin match opt with
        | "-batch" -> { run_mode = Batch }
        | s ->
          extras := s :: !extras;
          oval
      end in
      parse noval
  in
  try
    parse default
  with any -> Coqargs.fatal_error any
