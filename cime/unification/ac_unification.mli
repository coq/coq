(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



(*

  [set_of_solutions ...]

*)

val set_of_solutions : 
  'symbol #Signatures.signature -> (*i Variables.user_variables -> i*)
    'symbol Gen_terms.term -> 'symbol Gen_terms.term 
      -> 'symbol Substitution.substitution list

val display_set_of_solutions : 
  'symbol #Signatures.signature -> Variables.user_variables -> 
    'symbol Gen_terms.term -> 'symbol Gen_terms.term 
      -> unit
