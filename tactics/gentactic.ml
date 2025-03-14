(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

type raw_generic_tactic = Genarg.raw_generic_argument

type glob_generic_tactic = Genarg.glob_generic_argument

let of_raw_genarg x = x

let to_raw_genarg x = x

let of_glob_genarg x = x

let print_raw = Pputils.pr_raw_generic

let print_glob = Pputils.pr_glb_generic

let subst = Gensubst.generic_substitute

let intern ?(strict=true) env ?(ltacvars=Id.Set.empty) v =
  let ist = { (Genintern.empty_glob_sign ~strict env) with ltacvars } in
  let _, v = Genintern.generic_intern ist v in
  v

let interp ?(lfun=Id.Map.empty) v =
  let open Geninterp in
  let open Proofview.Notations in
  Proofview.tclProofInfo[@ocaml.warning"-3"] >>= fun (_name, poly) ->
  let ist = { lfun; poly; extra = TacStore.empty } in
  let Genarg.GenArg (Glbwit tag, v) = v in
  let v = Geninterp.interp tag ist v in
  Ftactic.run v (fun _ -> Proofview.tclUNIT ())

let wit_generic_tactic = Genarg.make0 "generic_tactic"

let () =
  let mkprint f v = Genprint.PrinterBasic (fun env sigma -> f env sigma v) in
  Genprint.register_vernac_print0 wit_generic_tactic (mkprint (print_raw ?level:None));
