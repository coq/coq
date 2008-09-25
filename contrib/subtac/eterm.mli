(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)
open Environ
open Tacmach
open Term
open Evd
open Names
open Util

val mkMetas : int -> constr list

val evar_dependencies : evar_map -> int -> Intset.t
val sort_dependencies : (int * evar_info * Intset.t) list -> (int * evar_info * Intset.t) list

(* env, id, evars, number of function prototypes to try to clear from
   evars contexts, object and type *)
val eterm_obligations : env -> identifier -> evar_defs -> evar_map -> int -> 
  ?status:obligation_definition_status -> constr -> types -> 
  (identifier * types * loc * obligation_definition_status * Intset.t) array * constr * types
    (* Obl. name, type as product, location of the original evar, 
       status and dependencies as indexes into the array *)

val etermtac : open_constr -> tactic
