(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Term

let sig_typ   () = Coqlib.get_ref "core.sig.type"
let sig_intro () = Coqlib.get_ref "core.sig.intro"
let sig_proj1 () = Coqlib.get_ref "core.sig.proj1"
let sig_proj2 () = Coqlib.get_ref "core.sig.proj2"

let sigT_typ   () = Coqlib.get_ref "core.sigT.type"
let sigT_intro () = Coqlib.get_ref "core.sigT.intro"
let sigT_proj1 () = Coqlib.get_ref "core.sigT.proj2"
let sigT_proj2 () = Coqlib.get_ref "core.sigT.proj2"

let prod_typ   () = Coqlib.get_ref "core.prod.type"
let prod_intro () = Coqlib.get_ref "core.prod.intro"
let prod_proj1 () = Coqlib.get_ref "core.prod.proj1"
let prod_proj2 () = Coqlib.get_ref "core.prod.proj2"

let coq_eq_ind      () = Coqlib.get_ref "core.eq.type"
let coq_eq_refl     () = Coqlib.get_ref "core.eq.refl"
let coq_eq_refl_ref () = Coqlib.get_ref "core.eq.refl"
let coq_eq_rect     () = Coqlib.get_ref "core.eq.rect"

let coq_JMeq_ind  () = Coqlib.get_ref "core.jmeq.type"
let coq_JMeq_refl () = Coqlib.get_ref "core.jmeq.refl"

let coq_not () = Coqlib.get_constr "core.not.type"
let coq_and () = Coqlib.get_constr "core.and.type"

let unsafe_fold_right f = function
    hd :: tl -> List.fold_right f tl hd
  | [] -> invalid_arg "unsafe_fold_right"

let mk_coq_not x = mkApp (delayed_force coq_not, [| x |])

let papp evdref r args =
  let gr = delayed_force r in
    mkApp (Evarutil.e_new_global evdref gr, args)

let mk_coq_and l =
  let and_typ = delayed_force coq_and in
    unsafe_fold_right
      (fun c conj ->
	 mkApp (and_typ, [| c ; conj |]))
      l
