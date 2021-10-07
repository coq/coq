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
open Vmvalues
open Vmbytecodes

type reloc_info =
  | Reloc_annot of annot_switch
  | Reloc_const of structured_constant
  | Reloc_getglobal of Constant.t
  | Reloc_proj_name of Projection.Repr.t
  | Reloc_caml_prim of CPrimitives.t

type patches
type emitcodes

val patch : emitcodes -> patches -> (reloc_info -> int) -> Vmvalues.tcode

type to_patch = emitcodes * patches * fv

type body_code =
  | BCdefined of to_patch
  | BCalias of Constant.t
  | BCconstant


val subst_body_code : Mod_subst.substitution -> body_code -> body_code

val to_memory : bytecodes * bytecodes * fv -> to_patch
               (** init code, fun code, fv *)
