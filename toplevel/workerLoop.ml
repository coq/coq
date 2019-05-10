(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let rec parse = function
  | "--xml_format=Ppcmds" :: rest -> parse rest
  | x :: rest -> x :: parse rest
  | [] -> []

let worker_parse_extra ~opts extra_args =
  (), parse extra_args

let worker_init init () ~opts =
  Flags.quiet := true;
  init ();
  Coqtop.init_toploop opts

let worker_specific_usage name = Usage.{
  executable_name = name;
  extra_args = "";
  extra_options = ("\n" ^ name ^ " specific options:\
\n  --xml_format=Ppcmds    serialize pretty printing messages using the std_ppcmds format\n");
}

let start ~init ~loop name =
  let open Coqtop in
  let custom = {
    parse_extra = worker_parse_extra;
    help = worker_specific_usage name;
    opts = Coqargs.default;
    init = worker_init init;
    run = (fun () ~opts:_ _state (* why is state not used *) -> loop ());
  } in
  start_coq custom
