(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

exception No_solution
exception Not_appliable

type 'problem disjunction = 'problem list

(*
val apply : ('problem -> 'problem set) -> 'problem -> 'problem_set
val repeat : ('problem -> 'problem set) -> 'problem set -> 'problem_set
*)


let orelse rule rule' pb = 
  try rule pb
  with Not_appliable -> rule' pb

type 'a rule_result =
    Sol of 'a
  | No_sol
  | No_app

let repeat rule pb = 
  let rec rec_repeat accu = function
      [] -> accu
    | pb :: list_of_pbs ->
	let new_pbs = 
	  try
	    Sol (rule pb)
	  with
	    No_solution -> No_sol
	  | Not_appliable -> No_app in
	  
	  match new_pbs with
	      Sol rule_pb -> 
		rec_repeat accu (List.rev_append rule_pb list_of_pbs)
	    | No_sol -> rec_repeat accu list_of_pbs
	    | No_app -> rec_repeat (pb :: accu) list_of_pbs in


    rec_repeat [] [pb]
