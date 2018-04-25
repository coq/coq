(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util

let init_reference dir s () = Coqlib.coq_reference  "Program" dir s

let papp evdref r args = 
  let open EConstr in
  let gr = delayed_force r in
  let evd, hd = Evarutil.new_global !evdref gr in
  evdref := evd;
  mkApp (hd, args)

let sig_typ = init_reference ["Init"; "Specif"] "sig"
let sig_intro = init_reference ["Init"; "Specif"] "exist"
let sig_proj1 = init_reference ["Init"; "Specif"] "proj1_sig"

let sigT_typ = init_reference ["Init"; "Specif"] "sigT"
let sigT_intro = init_reference ["Init"; "Specif"] "existT"
let sigT_proj1 = init_reference ["Init"; "Specif"] "projT1"
let sigT_proj2 = init_reference ["Init"; "Specif"] "projT2"

let prod_typ = init_reference ["Init"; "Datatypes"] "prod"
let prod_intro = init_reference ["Init"; "Datatypes"] "pair"
let prod_proj1 = init_reference ["Init"; "Datatypes"] "fst"
let prod_proj2 = init_reference ["Init"; "Datatypes"] "snd"

let coq_eq_ind = init_reference ["Init"; "Logic"] "eq"
let coq_eq_refl = init_reference ["Init"; "Logic"] "eq_refl"
let coq_eq_refl_ref = init_reference ["Init"; "Logic"] "eq_refl"
let coq_eq_rect = init_reference ["Init"; "Logic"] "eq_rect"

let coq_JMeq_ind = init_reference ["Logic";"JMeq"] "JMeq"
let coq_JMeq_refl = init_reference ["Logic";"JMeq"] "JMeq_refl"

let coq_not = init_reference ["Init";"Logic"] "not"
let coq_and = init_reference ["Init";"Logic"] "and"

let mk_coq_not sigma x =
  let sigma, notc = Evarutil.new_global sigma (coq_not ()) in
  sigma, EConstr.mkApp (notc, [| x |])

let unsafe_fold_right f = function
    hd :: tl -> List.fold_right f tl hd
  | [] -> invalid_arg "unsafe_fold_right"

let mk_coq_and sigma l =
  let sigma, and_typ = Evarutil.new_global sigma (coq_and ()) in
  sigma, unsafe_fold_right
      (fun c conj ->
	 EConstr.mkApp (and_typ, [| c ; conj |]))
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

let _ =
  declare_bool_option
  { optdepr  = false;
    optname  = "preferred transparency of Program obligations";
    optkey   = ["Transparent";"Obligations"];
    optread  = get_proofs_transparency;
    optwrite = set_proofs_transparency; }

let _ =
  declare_bool_option
  { optdepr  = false;
    optname  = "program cases";
    optkey   = ["Program";"Cases"];
    optread  = (fun () -> !program_cases);
    optwrite = (:=) program_cases }

let _ =
  declare_bool_option
  { optdepr  = false;
    optname  = "program generalized coercion";
    optkey   = ["Program";"Generalized";"Coercion"];
    optread  = (fun () -> !program_generalized_coercion);
    optwrite = (:=) program_generalized_coercion }
