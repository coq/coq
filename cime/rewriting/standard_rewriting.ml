(***************************************************************************

This module provides usual rewriting functions on a term wrt. a set of
rules.  The signature may contain only free function symbols.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Rewrite_rules;;
open Substitution;;
open Standard_matching;;

 
(*

  [rewrite_at_top_by_a_rule sigma rule t] returns the term obtained by
  rewriting the term [t] by the rule [rule] at the top position. When
  the term [t] does not match with the left-hand side of the rule, the
  exception Not_found is raised. The signature [sigma] over which the
  term [t] and the rule [rule] are built may contain only free
  function symbols.

*)

let rewrite_at_top_by_a_rule rule t =
  try
    let sigma = Standard_matching.matching rule.lhs t
    in (rule.rhs,sigma)
  with
      No_match -> raise Not_found
;;

(*

  [rewrite_at_top sigma ruleset t] returns the term obtained by
  rewriting the term [t] at the top position by the first rule of the
  set of rules [ruleset] which matches [t]. When there is not such a
  rule in [ruleset], the exception Not_found is raised. The signature
  [sigma] over which the term [t] and the set of rules [ruleset] are
  built may contain only free function symbols.

*)

let rec rewrite_at_top ruleset t = 
  match ruleset with
      [] -> raise Not_found
    | r::s ->
	try
	  let sigma = Standard_matching.matching r.lhs t
	  in (r.rhs,sigma)
	with No_match -> rewrite_at_top s t
;;

open Format;;

(*

  [compiled_rewrite_at_top sigma ruleset t] is similar to
  [rewrite_at_top sigma ruleset t], except that the set of rules
  [ruleset] is given by a discrimination net instead of a list of
  rules.

*)

let compiled_rewrite_at_top dnet t =
  let ruleset = Naive_dnet.discriminate dnet t in
  (*i
  printf "rewrite at top of term ";
  Gen_terms.print_term (new Signatures.default) Variables.default t;
  printf "@.";
 
  printf "selected rules : ";
  Rewrite_rules.print_rewrite_rule_set (new Signatures.default) Variables.default ruleset;
  printf "@.";
    
  i*)
  rewrite_at_top ruleset t 
;;
