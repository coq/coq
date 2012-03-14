(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Term
open Reductionops
open Environ
open Typeops
open Pretype_errors
open Classops
open Recordops
open Evarutil
open Evarconv
open Retyping
open Evd
open Termops

type message = string

let make_dir l = make_dirpath (List.map id_of_string (List.rev l))

let find_reference locstr dir s =
  let sp = Libnames.make_path (make_dir dir) (id_of_string s) in
  try Nametab.global_of_path sp
  with Not_found -> anomaly (locstr^": cannot find "^(Libnames.string_of_path sp))

let coq_reference locstr dir s = find_reference locstr ("Coq"::dir) s
let coq_constant locstr dir s = Libnames.constr_of_global (coq_reference locstr dir s)

let init_constant dir s () = coq_constant "Program" dir s
let init_reference dir s () = coq_reference "Program" dir s

let sig_typ = init_constant ["Init"; "Specif"] "sig"
let sig_intro = init_constant ["Init"; "Specif"] "exist"
let sig_proj1 = init_constant ["Init"; "Specif"] "proj1_sig"

let sigT_typ = init_constant ["Init"; "Specif"] "sigT"
let sigT_intro = init_constant ["Init"; "Specif"] "existT"
let sigT_proj1 = init_constant ["Init"; "Specif"] "projT1"
let sigT_proj2 = init_constant ["Init"; "Specif"] "projT2"

let prod_typ = init_constant ["Init"; "Datatypes"] "prod"
let prod_intro = init_constant ["Init"; "Datatypes"] "pair"
let prod_proj1 = init_constant ["Init"; "Datatypes"] "fst"
let prod_proj2 = init_constant ["Init"; "Datatypes"] "snd"

let coq_eq_ind = init_constant ["Init"; "Logic"] "eq"
let coq_eq_refl = init_constant ["Init"; "Logic"] "eq_refl"
let coq_eq_refl_ref = init_reference ["Init"; "Logic"] "eq_refl"
let coq_eq_rect = init_constant ["Init"; "Logic"] "eq_rect"

let coq_JMeq_ind = init_constant ["Logic";"JMeq"] "JMeq"
let coq_JMeq_refl = init_constant ["Logic";"JMeq"] "JMeq_refl"

let coq_not = init_constant ["Init";"Logic"] "not"
let coq_and = init_constant ["Init";"Logic"] "and"

let mk_coq_not x = mkApp (delayed_force coq_not, [| x |])

let unsafe_fold_right f = function
    hd :: tl -> List.fold_right f tl hd
  | [] -> raise (Invalid_argument "unsafe_fold_right")

let mk_coq_and l =
  let and_typ = delayed_force coq_and in
    unsafe_fold_right
      (fun c conj ->
	 mkApp (and_typ, [| c ; conj |]))
      l

let with_program f c = 
  let mode = !Flags.program_mode in
    Flags.program_mode := true;
    let res = f c in
      Flags.program_mode := mode;
      res
