(*******************************************************************

This module defines the strings (or words) over a parametrized
  signature.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

********************************************************************)

		 
(*

  This module defines the strings (or words) over a string
  parametrized signature.

*)

open Parameterized_signatures_syntax

type operator = 
  | Power of Linear_constraints.expr 
  | Fp of Linear_constraints.var_id * 
      Linear_constraints.expr * Linear_constraints.expr 
  | No

type letter = {a: string ; index:  Linear_constraints.expr list}

type factor = { base : letter list ; 
		operator : operator;
	      }

type word = { env : Linear_constraints.var_id list ;
	      letters : factor list ;
	      constr : Linear_constraints.formula;
	    }

val from_abstract_word : 
 Parameterized_signatures.parameterized_signature -> 
  Parameterized_signatures_syntax.constrained_word -> word;;

val from_abstract_factor : 
  Linear_constraints.var_env ->
    Parameterized_signatures_syntax.factor ->
      Linear_constraints.var_env * factor

