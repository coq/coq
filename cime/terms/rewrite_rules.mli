(***************************************************************************

Module defining rewrite rules.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Gen_terms;;

(*

the type for rewrite rules, defined by the lefthand side, the
righthand side, and optionally the lhs and the rhs of the AC-extension
and the size of the rule

*)

type 'symbol rewrite_rule = 
    {
      lhs : 'symbol term;
      rhs : 'symbol term;
      ext : ('symbol term * 'symbol term) option;
      is_or : bool;
      nb : int
    }
;;


(*

[(make_rule sigma l r)] builds a rewrite rule over signature [sigma]
with lefthand side [l] and righthand side [r]. Determines whether the
rule needs to be AC-extended.

*)

val make_rule : 
  'symbol #Signatures.signature -> 'symbol term -> 'symbol term 
    -> 'symbol rewrite_rule;;


(*

  [(make_non_oriented_rule n sigma l r)] builds a rewrite
  rule as [(make_rule n sigma l r)], but the left-hand side
  [l] is not always greater than the right-hand side [r], it may
  depends on the instances. Only for unfailing completion purpose.

*)

val make_non_oriented_rule : 
  'symbol #Signatures.signature -> 'symbol term -> 'symbol term 
    -> 'symbol rewrite_rule;;
(*

[(make_numbered_rule n sigma l r)] builds a rewrite rule as [(make_rule sigma l r)], and this rule owns the number [n]. Only for completion purposes.

*)

val make_numbered_rule : 
  int -> 'symbol #Signatures.signature -> 'symbol term -> 'symbol term 
    -> 'symbol rewrite_rule;;


(*

  [(make_non_oriented_numbered_rule n sigma l r)] builds a rewrite
  rule as [(make_numbered_rule n sigma l r)], but the left-hand side
  [l] is not always greater than the right-hand side [r], it may
  depends on the instances. Only for unfailing completion purpose.

*)

val make_non_oriented_numbered_rule : 
  int -> 'symbol #Signatures.signature -> 'symbol term -> 'symbol term 
    -> 'symbol rewrite_rule;;


(*

  printing functions

*)

val print_rewrite_rule : 
  'symbol #Signatures.signature 
  -> Variables.user_variables -> 'symbol rewrite_rule -> unit;;

val print_rewrite_rule_set : 
  'symbol #Signatures.signature 
  -> Variables.user_variables -> 'symbol rewrite_rule list -> unit;;


