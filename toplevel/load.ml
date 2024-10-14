(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Coqargs

(******************************************************************************)
(* Interactive Load File Simulation                                           *)
(******************************************************************************)

let load_init_file opts ~state =
  if opts.pre.load_rcfile then
    Topfmt.(in_phase ~phase:LoadingRcFile) (fun () ->
        Coqrc.load_rcfile ~rcfile:opts.config.rcfile ~state) ()
  else begin
    Flags.if_verbose Feedback.msg_info (str"Skipping rcfile loading.");
    state
  end

let load_vernacular opts ~state =
  List.fold_left
    (fun state (f_in, echo) ->
      let s = Loadpath.locate_file f_in in
      (* Should make the beautify logic clearer *)
      let load_vernac f = Vernac.load_vernac ~echo ~check:true ~state f in
      if !Flags.beautify
      then Flags.with_option Flags.beautify_file load_vernac f_in
      else load_vernac s
    ) state opts.pre.load_vernacular_list

let load_init_vernaculars opts ~state =
  let state = load_init_file opts ~state in
  let state = load_vernacular opts ~state in
  state
