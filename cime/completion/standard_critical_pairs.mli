(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



val critical_pairs : 
  'symbol #Signatures.signature -> 
    'symbol Rewrite_rules.rewrite_rule -> 
      'symbol Rewrite_rules.rewrite_rule -> 
	('symbol Gen_terms.term * 'symbol Gen_terms.term) list

val self_critical_pairs : 
  'symbol #Signatures.signature -> 
    'symbol Rewrite_rules.rewrite_rule ->  
      ('symbol Gen_terms.term * 'symbol Gen_terms.term) list
