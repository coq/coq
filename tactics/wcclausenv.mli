(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
open Environ
open Evd
open Proof_type
open Tacmach
open Evar_refiner
open Clenv
(*i*)

(* A somewhat cryptic module. *)

val pf_get_new_id  : identifier      -> goal sigma -> identifier
val pf_get_new_ids : identifier list -> goal sigma -> identifier list

(*i**
val add_prod_sign : 
  'a evar_map -> constr * types signature -> constr * types signature

val add_prods_sign : 
  'a evar_map -> constr * types signature -> constr * types signature
**i*)

val applyUsing : constr -> tactic
