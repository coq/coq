(***************************************************************************

  This module provides a function for cleaning a solved problem, that is
  removing the equations giving the value of an existentially quantified 
  variable.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Problems
open Controle

let existential_quantifiers_elimination pb =
  match pb.global_status with 
      Solved ->
	List.filter
	  (function
	       Var x, _ -> VarSet.mem x pb.vars_for_eqe
	     | _,_ -> assert false) 
	  pb.solved_part
    | _ -> raise Not_appliable



