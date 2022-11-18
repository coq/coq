(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ltac_plugin
open Tacentries

let setoid_plugin = "coq-core.plugins.setoid"
let () = Mltop.add_known_module setoid_plugin

let head_of_constr id c =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= fun sigma ->
  let id = Taccoerce.coerce_to_ident_not_fresh sigma id in
  let c = Option.get @@ Tacinterp.Value.to_constr c in
  Class_tactics.head_of_constr id c

let () = ml_tactic_extend ~plugin:setoid_plugin ~name:"head_of_constr"
  ~local:true (MLTyArg (MLTyArg MLTyNil)) head_of_constr
