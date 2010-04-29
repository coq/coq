(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Names
open Tacmach
open Tacexpr

(** Programmable destruction of hypotheses and conclusions. *)

val set_extern_interp : (glob_tactic_expr -> tactic) -> unit

(*
val dHyp : identifier -> tactic
val dConcl : tactic
*)
val h_destructHyp : bool -> identifier -> tactic
val h_destructConcl : tactic
val h_auto_tdb : int option -> tactic

val add_destructor_hint :
  Vernacexpr.locality_flag -> identifier -> (bool,unit) Tacexpr.location ->
    Rawterm.patvar list * Pattern.constr_pattern -> int ->
      glob_tactic_expr -> unit
