(***************************************************************************

  This module provides some functions in order to repeat the application 
  of a transformation rule to a problem until a normal form is reached.
  The transformation rule may return several problems from a single one.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Lazy_list

exception No_solution
exception Not_appliable

type 'problem disjunction = 'problem llist

type 'a rule_result =
    Sol of 'a
  | No_sol
  | No_app

let repeat rule pb = 
  let rec rec_repeat = function
      Nil -> Nil
    | Cons ({head = pb; tail = Val list_of_pbs} as cell) ->
	begin
	  let new_pbs = 
	    try
	      Sol (rule pb)
	    with
		No_solution -> No_sol
	      | Not_appliable -> No_app in
	    
	    match new_pbs with
		Sol rule_pb -> 
		  rec_repeat (lazy_append rule_pb cell.tail)
	      | No_sol -> rec_repeat list_of_pbs
	      | No_app -> 
		  let thunk () = rec_repeat list_of_pbs in
		  Cons {head = pb; tail = Freeze thunk} 
	end
    | Cons ({head = pb; tail = Freeze th} as cell) -> 
	begin
	  let new_pbs = 
	    try
	      Sol (rule pb)
	    with
		No_solution -> No_sol
	      | Not_appliable -> No_app in
	    
	    match new_pbs with
		Sol rule_pb -> 
		  rec_repeat (lazy_append rule_pb cell.tail)
	      | No_sol -> 
		  let list_of_pbs = th () in 
		  let _ = cell.tail <- Val list_of_pbs in
		    rec_repeat list_of_pbs
	      | No_app ->
		  let thunk () =
		    let list_of_pbs = th () in 
		    let _ = cell.tail <- Val list_of_pbs in
		      rec_repeat list_of_pbs in
		    Cons {head = pb; tail = Freeze thunk}
		  
	end
  in
	  

    rec_repeat (Cons {head = pb; tail = Val Nil})
