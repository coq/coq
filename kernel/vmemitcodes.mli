(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Names
open Vmvalues
open Vmbytecodes

type reloc_info =
  | Reloc_annot of annot_switch
  | Reloc_const of structured_constant
  | Reloc_getglobal of Constant.t
  | Reloc_caml_prim of caml_prim

type to_patch
type patches

val patch : (to_patch * patches) -> (reloc_info -> int) -> Vmvalues.tcode * fv

type 'a pbody_code =
  | BCdefined of bool array * 'a * patches
  | BCalias of Constant.t
  | BCconstant

type body_code = to_patch pbody_code

val subst_body_code : Mod_subst.substitution -> 'a pbody_code -> 'a pbody_code

val to_memory : fv -> bytecodes -> to_patch * patches
