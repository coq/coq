(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2expr
open Proofview.Notations

let backtrace_evd : backtrace Evd.Store.field = Evd.Store.field "ltac2_trace"

let backtrace : backtrace Exninfo.t = Exninfo.make "ltac2_trace"

let print_ltac2_backtrace = ref false

let () = Goptions.declare_bool_option {
  optstage = Summary.Stage.Interp;
  optdepr = None;
  optkey = ["Ltac2"; "Backtrace"];
  optread = (fun () -> !print_ltac2_backtrace);
  optwrite = (fun b -> print_ltac2_backtrace := b);
}

let ltac2_in_ltac1_profiling = ref false

let () = Goptions.declare_bool_option {
  optstage = Summary.Stage.Interp;
  optdepr = None;
  optkey = ["Ltac2"; "In"; "Ltac1"; "Profiling"];
  optread = (fun () -> !ltac2_in_ltac1_profiling);
  optwrite = (fun b -> ltac2_in_ltac1_profiling := b);
}

let get_backtrace =
  Proofview.tclEVARMAP >>= fun sigma ->
  match Evd.Store.get (Evd.get_extra_data sigma) backtrace_evd with
  | None -> Proofview.tclUNIT []
  | Some bt -> Proofview.tclUNIT bt

let set_backtrace bt =
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = Evd.get_extra_data sigma in
  let store = Evd.Store.set store backtrace_evd bt in
  let sigma = Evd.set_extra_data store sigma in
  Proofview.Unsafe.tclEVARS sigma

let pr_frame, pr_frame_hook = Hook.make ()

let with_frame frame tac =
  let tac =
    if !print_ltac2_backtrace then
      get_backtrace >>= fun bt ->
      set_backtrace (frame :: bt) >>= fun () ->
      Proofview.tclOR tac (fun (e,info) ->
          (* If it's already present assume it's more precise *)
          let info = if Option.has_some (Exninfo.get info backtrace) then info
            else Exninfo.add info backtrace (frame::bt)
          in
          Proofview.tclZERO ~info e)
          >>= fun ans ->
      set_backtrace bt >>= fun () ->
      Proofview.tclUNIT ans
    else tac
  in
  if !ltac2_in_ltac1_profiling then
    let pr_frame f = Some (Hook.get pr_frame f) in
    Profile_tactic.do_profile_gen pr_frame frame ~count_call:true tac
  else tac
