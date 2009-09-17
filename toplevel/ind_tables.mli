(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Names
open Libnames
open Mod_subst
open Sign


val cache_scheme :(object_name*(Indmap.key*constr)) -> unit
val export_scheme : (Indmap.key*constr) -> (Indmap.key*constr) option 

val find_eq_scheme : Indmap.key -> constr
val check_eq_scheme : Indmap.key -> bool

val cache_bl: (object_name*(Indmap.key*constr)) -> unit
val cache_lb: (object_name*(Indmap.key*constr)) -> unit
val cache_dec : (object_name*(Indmap.key*constr)) -> unit

val export_bool_leib : (Indmap.key*constr) -> (Indmap.key*constr) option 
val export_leib_bool : (Indmap.key*constr) -> (Indmap.key*constr) option 
val export_dec_proof : (Indmap.key*constr) -> (Indmap.key*constr) option 

val find_bl_proof : Indmap.key -> constr
val find_lb_proof : Indmap.key -> constr
val find_eq_dec_proof : Indmap.key -> constr

val check_bl_proof: Indmap.key -> bool
val check_lb_proof: Indmap.key -> bool
val check_dec_proof: Indmap.key -> bool




