(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util

let papp evdref r args = 
  let open EConstr in
  let gr = delayed_force r in
  let evd, hd = Evarutil.new_global !evdref gr in
  evdref := evd;
  mkApp (hd, args)

let sig_typ   () = Coqlib.lib_ref "core.sig.type"
let sig_intro () = Coqlib.lib_ref "core.sig.intro"
let sig_proj1 () = Coqlib.lib_ref "core.sig.proj1"
(* let sig_proj2 () = Coqlib.lib_ref "core.sig.proj2" *)

let sigT_typ   () = Coqlib.lib_ref "core.sigT.type"
let sigT_intro () = Coqlib.lib_ref "core.sigT.intro"
let sigT_proj1 () = Coqlib.lib_ref "core.sigT.proj1"
let sigT_proj2 () = Coqlib.lib_ref "core.sigT.proj2"

let prod_typ   () = Coqlib.lib_ref "core.prod.type"
let prod_intro () = Coqlib.lib_ref "core.prod.intro"
let prod_proj1 () = Coqlib.lib_ref "core.prod.proj1"
let prod_proj2 () = Coqlib.lib_ref "core.prod.proj2"

let coq_eq_ind      () = Coqlib.lib_ref "core.eq.type"
let coq_eq_refl     () = Coqlib.lib_ref "core.eq.refl"
let coq_eq_refl_ref () = Coqlib.lib_ref "core.eq.refl"
let coq_eq_rect     () = Coqlib.lib_ref "core.eq.rect"

let mk_coq_not sigma x =
  let sigma, notc = Evarutil.new_global sigma Coqlib.(lib_ref "core.not.type") in
  sigma, EConstr.mkApp (notc, [| x |])

let coq_JMeq_ind  () =
  try Coqlib.lib_ref "core.JMeq.type"
  with Not_found ->
    user_err (Pp.str "cannot find Coq.Logic.JMeq.JMeq; maybe library Coq.Logic.JMeq has to be required first.")
let coq_JMeq_refl () = Coqlib.lib_ref "core.JMeq.refl"

(* let coq_not () = Universes.constr_of_global @@ Coqlib.lib_ref "core.not.type" *)
(* let coq_and () = Universes.constr_of_global @@ Coqlib.lib_ref "core.and.type" *)

let unsafe_fold_right f = function
    hd :: tl -> List.fold_right f tl hd
  | [] -> invalid_arg "unsafe_fold_right"

let mk_coq_and sigma l =
  let sigma, and_typ = Evarutil.new_global sigma Coqlib.(lib_ref "core.and.type") in
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
  { optdepr  = false;
    optname  = "preferred transparency of Program obligations";
    optkey   = ["Transparent";"Obligations"];
    optread  = get_proofs_transparency;
    optwrite = set_proofs_transparency; }

let () =
  declare_bool_option
  { optdepr  = false;
    optname  = "program cases";
    optkey   = ["Program";"Cases"];
    optread  = (fun () -> !program_cases);
    optwrite = (:=) program_cases }

let () =
  declare_bool_option
  { optdepr  = false;
    optname  = "program generalized coercion";
    optkey   = ["Program";"Generalized";"Coercion"];
    optread  = (fun () -> !program_generalized_coercion);
    optwrite = (:=) program_generalized_coercion }
