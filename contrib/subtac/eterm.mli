(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)
open Environ
open Term
open Evd
open Names
open Util

(* arnaud: trucs factices *)
type tactic = Tacticals.tactic
(* arnaud:/trucs factices *)

val mkMetas : int -> constr list

(* val eterm_term : evar_map -> constr -> types option -> constr * types option * (identifier * types) list *)

(* env, id, evars, number of
   function prototypes to try to clear from evars contexts, object and optional type *)
val eterm_obligations : env -> identifier -> evar_defs -> evar_map -> int -> constr -> types option -> 
  (identifier * types * bool * Intset.t) array * constr
    (* Obl. name, type as product, opacity (true = opaque) and dependencies as indexes into the array *)

val etermtac : open_constr -> tactic
