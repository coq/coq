(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Term

open Ptype
open Past
open Penv

(* Main part of the translation of imperative programs into functional ones
 * (with mlise.ml) *)

(* Here we translate the specification into a CIC specification *)

val trad_ml_type_v : Prename.t -> local_env -> type_v -> constr
val trad_ml_type_c : Prename.t -> local_env -> type_c -> constr
val trad_imp_type  : Prename.t -> local_env -> type_v -> constr
val trad_type_in_env : Prename.t -> local_env -> identifier -> constr

val binding_of_alist : Prename.t -> local_env
                    -> (identifier * identifier) list
		    -> cc_binder list
val make_abs : cc_binder list -> cc_term -> cc_term
val abs_pre : Prename.t -> local_env -> cc_term * constr -> 
  constr precondition list -> cc_term

(* The following functions translate the main constructions *)

val make_tuple : (cc_term * cc_type) list -> predicate option
          -> Prename.t -> local_env -> string
          -> cc_term

val result_tuple : Prename.t -> string -> local_env
          -> (cc_term * constr) -> (Peffect.t * predicate option)
          -> cc_term * constr

val let_in_pre : constr -> constr precondition -> cc_term -> cc_term

val make_let_in : Prename.t -> local_env -> cc_term 
          -> constr precondition list
          -> ((identifier * identifier) list * predicate option) 
	  -> identifier * constr
	  -> cc_term * constr -> cc_term

val make_block : Prename.t -> local_env
          -> (Prename.t -> (identifier * constr) option -> cc_term * constr)
	  -> (cc_term * type_c, constr) block
	  -> cc_term

val make_app : local_env
          -> Prename.t -> (cc_term * type_c) list
	  -> Prename.t -> cc_term * type_c
	  -> ((type_v binder list) * type_c)
	    * ((identifier*identifier) list)
	    * type_c
	  -> type_c
          -> cc_term

val make_if : Prename.t -> local_env 
         -> cc_term * type_c
	 -> Prename.t
         -> cc_term * type_c
         -> cc_term * type_c
         -> type_c
         -> cc_term

val make_while : Prename.t -> local_env
         -> (constr * constr * constr) (* typed variant *)
         -> cc_term * type_c
         -> (cc_term * type_c, constr) block
         -> constr assertion option * type_c
         -> cc_term

val make_letrec : Prename.t -> local_env
         -> (identifier * (constr * constr * constr)) (* typed variant *)
	 -> identifier (* the name of the function *)
         -> (cc_binder list)
	 -> (cc_term * type_c)
	 -> type_c
         -> cc_term

(* Functions to translate array operations *)

val array_info :
  Prename.t -> local_env -> identifier -> constr * constr * constr

val make_raw_access :
  Prename.t -> local_env -> identifier * identifier -> constr -> constr

val make_raw_store :
  Prename.t -> local_env -> identifier * identifier 
    -> constr -> constr -> constr

val make_pre_access :
  Prename.t -> local_env -> identifier -> constr -> constr

