(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Closure

(* Opaque constants *)
let cst_transp = ref Sppred.full

let set_opaque_const sp = cst_transp := Sppred.remove sp !cst_transp
let set_transparent_const sp = cst_transp := Sppred.add sp !cst_transp

let is_opaque_cst sp = not (Sppred.mem sp !cst_transp)

(* Unfold the first only if it is not opaque and the second is
   opaque *)
let const_order sp1 sp2 = is_opaque_cst sp2 & not (is_opaque_cst sp1)

(* Opaque variables *)
let var_transp = ref Idpred.full

let set_opaque_var sp = var_transp := Idpred.remove sp !var_transp
let set_transparent_var sp = var_transp := Idpred.add sp !var_transp

let is_opaque_var sp = not (Idpred.mem sp !var_transp)

let var_order id1 id2 = is_opaque_var id2 & not (is_opaque_var id1)

(* *)
let oracle_order k1 k2 =
  match (k1,k2) with
      (ConstKey sp1, ConstKey sp2) -> const_order sp1 sp2
    | (VarKey id1, VarKey id2) -> var_order id1 id2
    | _ -> false

(* summary operations *)

let init() = (cst_transp := Sppred.full; var_transp := Idpred.full)
let freeze () = (!var_transp, !cst_transp)
let unfreeze (vo,co) = (cst_transp := co; var_transp := vo)
