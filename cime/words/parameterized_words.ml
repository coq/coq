(***************************************************************************

This module defines the strings (or words) over a parametrized signature

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



		 
(*

  This module defines the strings (or words) over a string parametrized signature

*)
(*
open Format
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

type word = { env : Linear_constraints.var_id list;
	      letters : factor list ;
	      constr : Linear_constraints.formula;
	    }



let from_abstract_letter env (id,expr_l) =
  let env,el = 
    Listutils.fold_right_env Linear_constraints.from_abstract_expr env expr_l
  in
  env,{ a = id ; index = el }

let from_abstract_simple_word env sw =
  Listutils.fold_right_env from_abstract_letter env sw

let from_abstract_factor env fact = 
  match fact with
    | Simple(sw) -> 
	let env1,w = from_abstract_simple_word env sw in
	env1,{ base = w ; operator = No }
    | Exp(sw,expr) ->
	let env1,w = from_abstract_simple_word env sw in
	let env2,expr2 = Linear_constraints.from_abstract_expr env1 expr in
	env2,{ base = w ; operator = Power(expr2) }
    | Product(i,e1,e2,sw) ->
	let env1,e1 = Linear_constraints.from_abstract_expr env e1 in
	let env2,e2 = Linear_constraints.from_abstract_expr env1 e2 in
	let v = Linear_constraints.make_var i in
	let env3,w = from_abstract_simple_word ((i,v)::env2) sw in
	List.filter (fun (_,x) -> not (x==v)) env3,
	{ base = w ; operator = Fp(v,e1,e2) }

let from_abstract_word s (word,constr) =
  let params = s#parameters#parameters in
  let env,c = Linear_constraints.from_abstract_formula params constr in
  let env,w = Listutils.fold_right_env from_abstract_factor env word in
  let local_vars = Listutils.map_filter 
		     snd
		     (function x -> not (List.memq x params))
		     env
  in
  { env = local_vars ; letters = w ; constr = c }

      


