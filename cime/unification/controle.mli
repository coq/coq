(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



exception No_solution
exception Not_appliable

type 'problem disjunction = 'problem list

val orelse : 
  ('problem -> 'problem_disjunction) -> ('problem -> 'problem_disjunction) 
    -> 'problem -> 'problem_disjunction

val repeat : 
  ('problem -> 'problem disjunction) -> 'problem -> 'problem disjunction
