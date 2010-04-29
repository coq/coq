(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

open Tacmach
open Names
open Tacexpr
open Termops

val instantiate : int -> Tacinterp.interp_sign * Rawterm.rawconstr ->
  (identifier * hyp_location_flag, unit) location -> tactic

(*i
val instantiate_tac : tactic_arg list -> tactic
i*)

val let_evar : name -> Term.types -> tactic
