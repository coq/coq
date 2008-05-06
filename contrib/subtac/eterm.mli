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

(* val eterm_term : evar_map -> constr -> types option -> constr * types option * (identifier * types) list *)

(* env, id, evars, number of
   function prototypes to try to clear from evars contexts, object and type *)
val eterm_obligations : env -> identifier -> evar_defs -> evar_map -> int -> constr -> types -> 
  (identifier * types * loc * bool * Intset.t) array * constr * types
    (* Obl. name, type as product, location of the original evar, 
       opacity (true = opaque) and dependencies as indexes into the array *)

val etermtac : open_constr -> tactic
