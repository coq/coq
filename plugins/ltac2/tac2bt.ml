(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2expr
open Proofview.Notations

let backtrace : backtrace Evd.Store.field = Evd.Store.field ()

let print_ltac2_backtrace = ref false

let get_backtrace =
  Proofview.tclEVARMAP >>= fun sigma ->
  match Evd.Store.get (Evd.get_extra_data sigma) backtrace with
  | None -> Proofview.tclUNIT []
  | Some bt -> Proofview.tclUNIT bt

let set_backtrace bt =
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = Evd.get_extra_data sigma in
  let store = Evd.Store.set store backtrace bt in
  let sigma = Evd.set_extra_data store sigma in
  Proofview.Unsafe.tclEVARS sigma

let pr_frame = let open Pp in function
  | FrAnon e -> str "<fun " ++ Tac2print.pr_glbexpr e ++ str ">"
  | FrLtac kn -> Tac2print.pr_tacref kn
  | FrPrim ml -> str "<" ++ str ml.mltac_plugin ++ str ":" ++ str ml.mltac_tactic ++ str ">"
  | FrExtn (tag,_) -> str "<extn:" ++ str (Tac2dyn.Arg.repr tag) ++ str ">"

let with_frame frame tac =
  let tac =
    if !print_ltac2_backtrace then
      get_backtrace >>= fun bt ->
      set_backtrace (frame :: bt) >>= fun () ->
      tac >>= fun ans ->
      set_backtrace bt >>= fun () ->
      Proofview.tclUNIT ans
    else tac
  in
  let pr_frame f = Some (pr_frame f) in
  Ltac_plugin.Profile_ltac.do_profile_gen pr_frame frame ~count_call:true tac
