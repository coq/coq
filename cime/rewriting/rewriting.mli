(***************************************************************************

This module provides usual rewriting functions on a term wrt. a set of
rules.  The signature may contain AC or commutative function symbols
as well as free function symbols.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


(*

  [ac_rewrite_at_top_by_a_rule sigma rule t] returns the term obtained
  by rewriting the term [t] by the rule [rule] at the top
  position. When the term [t] does not match with the left-hand side
  of the rule, the exception Not_found is raised. The signature
  [sigma] over which the term [t] and the rule [rule] are build may
  contain some AC or commutative function symbols as well as free
  function symbols.

*)

val ac_rewrite_at_top_by_a_rule :
  'symbol #Signatures.signature -> 
    'symbol Rewrite_rules.rewrite_rule ->
      'symbol Gen_terms.term -> 
	'symbol Gen_terms.term * 'symbol Substitution.substitution;;

(*

  [ac_rewrite_at_top sigma ruleset t] returns the term obtained by
  rewriting the term [t] at the top position by the first rule of the
  set of rules [ruleset] which matches [t]. When there is not such a
  rule in [ruleset], the exception Not_found is raised. The signature
  [sigma] over which the term [t] and the set of rules [ruleset] are
  built may contain some AC or commutative function symbols as well as
  free function symbols.

*)

val ac_rewrite_at_top :  
  'symbol #Signatures.signature -> 
    'symbol Rewrite_rules.rewrite_rule list ->
      'symbol Gen_terms.term -> 
	'symbol Gen_terms.term * 'symbol Substitution.substitution;;
  

(*

  [compiled_ac_rewrite_at_top sigma ruleset t] is similar to
  [ac_rewrite_at_top sigma ruleset t], except that the set of rules
  [ruleset] is given by a discrimination net instead of a list of
  rules.

*)

val compiled_ac_rewrite_at_top :  
  'symbol #Signatures.signature -> 
    'symbol Naive_dnet.dnet ->
      'symbol Gen_terms.term -> 
	'symbol Gen_terms.term * 'symbol Substitution.substitution;;


