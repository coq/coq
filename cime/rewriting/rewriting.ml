(***************************************************************************

This module provides usual rewriting functions on a term wrt. a set of
rules.  The signature may contain AC or commutative function symbols
as well as free function symbols.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Rewrite_rules

let matching sigma p s =
  Matching.matching sigma p s

(*

  [ac_rewrite_at_top_by_a_rule sigma rule t] returns the term obtained
  by rewriting the term [t] by the rule [rule] at the top
  position. When the term [t] does not match with the left-hand side
  of the rule, the exception Not_found is raised. The signature
  [sigma] over which the term [t] and the rule [rule] are built may
  contain some AC or commutative function symbols as well as free
  function symbols.

*)

let ac_rewrite_at_top_by_a_rule sigma rule t =
  try
    let subst = matching sigma rule.lhs t
    in (rule.rhs,subst)
  with
      Matching.No_match -> 
	match rule.ext with
	  | None -> raise Not_found
	  | Some(lhs,rhs) ->
	      try
		let subst = matching sigma lhs t
		in (rhs,subst)
	      with
		  Matching.No_match -> 
		      raise Not_found
;;

(*

  [ac_rewrite_at_top sigma ruleset t] returns the term obtained by
  rewriting the term [t] at the top position by the first rule of the
  set of rules [ruleset] which matches [t]. When there is not such a
  rule in [ruleset], the exception Not_found is raised. The signature
  [sigma] over which the term [t] and the set of rules [ruleset] are
  built may contain some AC or commutative function symbols as well as
  free function symbols.

*)

let rec ac_rewrite_at_top sigma ruleset t = 
  match ruleset with
      [] -> raise Not_found
    | r::s ->
	try
	  ac_rewrite_at_top_by_a_rule sigma r t
	with Not_found -> ac_rewrite_at_top sigma s t
;;
 


(*

  [compiled_ac_rewrite_at_top sigma ruleset t] is similar to
  [ac_rewrite_at_top sigma ruleset t], except that the set of rules
  [ruleset] is given by a discrimination net instead of a list of
  rules.

*)

let compiled_ac_rewrite_at_top sigma dnet t =
(*i
  Format.printf "rewrite at top of term ";
  Gen_terms.print_term sigma Variables.default t;
  Format.printf "@.";
 
  Format.printf "dnet : ";
  Naive_dnet.print sigma dnet;
  Format.printf "@.";
i*)
 
  let ruleset = Naive_dnet.discriminate dnet t in
  (*i
  Format.printf "selected rules : ";
  Rewrite_rules.print_rewrite_rule_set sigma Variables.default ruleset;
  Format.printf "@.";
    
  i*)
  ac_rewrite_at_top sigma ruleset t 
;;
