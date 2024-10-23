(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util

let papp env sigma r args =
  let open EConstr in
  let gr = delayed_force r in
  let evd, hd = Evd.fresh_global env sigma gr in
  sigma, mkApp (hd, args)

let sig_typ   () = Rocqlib.lib_ref "core.sig.type"
let sig_intro () = Rocqlib.lib_ref "core.sig.intro"
let sig_proj1 () = Rocqlib.lib_ref "core.sig.proj1"
(* let sig_proj2 () = Rocqlib.lib_ref "core.sig.proj2" *)

let sigT_typ   () = Rocqlib.lib_ref "core.sigT.type"
let sigT_intro () = Rocqlib.lib_ref "core.sigT.intro"
let sigT_proj1 () = Rocqlib.lib_ref "core.sigT.proj1"
let sigT_proj2 () = Rocqlib.lib_ref "core.sigT.proj2"

let prod_typ   () = Rocqlib.lib_ref "core.prod.type"
let prod_intro () = Rocqlib.lib_ref "core.prod.intro"
let prod_proj1 () = Rocqlib.lib_ref "core.prod.proj1"
let prod_proj2 () = Rocqlib.lib_ref "core.prod.proj2"

let coq_eq_ind      () = Rocqlib.lib_ref "core.eq.type"
let coq_eq_refl     () = Rocqlib.lib_ref "core.eq.refl"
let coq_eq_refl_ref () = Rocqlib.lib_ref "core.eq.refl"
let coq_eq_rect     () = Rocqlib.lib_ref "core.eq.rect"

let mk_coq_not env sigma x =
  let sigma, notc = Evd.fresh_global env sigma Rocqlib.(lib_ref "core.not.type") in
  sigma, EConstr.mkApp (notc, [| x |])

let coq_JMeq_ind  () =
  try Rocqlib.lib_ref "core.JMeq.type"
  with Not_found ->
    user_err (Pp.str "cannot find Stdlib.Logic.JMeq.JMeq; maybe library Stdlib.Logic.JMeq has to be required first.")
let coq_JMeq_refl () = Rocqlib.lib_ref "core.JMeq.refl"

let unsafe_fold_right f = function
    hd :: tl -> List.fold_right f tl hd
  | [] -> invalid_arg "unsafe_fold_right"

let mk_coq_and env sigma l =
  let sigma, and_typ = Evd.fresh_global env sigma Rocqlib.(lib_ref "core.and.type") in
  sigma, unsafe_fold_right
      (fun c conj ->
         EConstr.(mkApp (and_typ, [| c ; conj |])))
      l

(* true = transparent by default, false = opaque if possible *)
let proofs_transparency = ref true
let program_cases = ref true
let program_generalized_coercion = ref true

let set_proofs_transparency = (:=) proofs_transparency
let get_proofs_transparency () = !proofs_transparency

let is_program_generalized_coercion () = !program_generalized_coercion
let is_program_cases () = !program_cases

open Goptions

let () =
  declare_bool_option
  { optstage = Summary.Stage.Interp;
    optdepr  = None;
    optkey   = ["Transparent";"Obligations"];
    optread  = get_proofs_transparency;
    optwrite = set_proofs_transparency; }

let () =
  declare_bool_option
  { optstage = Summary.Stage.Interp;
    optdepr  = None;
    optkey   = ["Program";"Cases"];
    optread  = (fun () -> !program_cases);
    optwrite = (:=) program_cases }

let () =
  declare_bool_option
  { optstage = Summary.Stage.Interp;
    optdepr  = None;
    optkey   = ["Program";"Generalized";"Coercion"];
    optread  = (fun () -> !program_generalized_coercion);
    optwrite = (:=) program_generalized_coercion }
