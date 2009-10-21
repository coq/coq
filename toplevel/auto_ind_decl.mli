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


val subst_in_constr : (substitution*(inductive*constr))
                     -> (inductive*constr)

val compute_bl_goal : inductive -> rel_context -> int -> types
val compute_bl_tact : inductive -> rel_context -> int -> unit
val compute_lb_goal : inductive -> rel_context -> int -> types
val compute_lb_tact : inductive -> rel_context -> int -> unit
val compute_dec_goal : inductive -> rel_context -> int -> types
val compute_dec_tact : inductive -> rel_context -> int -> unit


val make_eq_scheme :mutual_inductive -> types array
