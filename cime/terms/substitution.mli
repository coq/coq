(***************************************************************************

Standard substitutions

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



open Gen_terms;;


type 'symbol substitution = (unit,'symbol term) Variables.VarMap.t;;



(* [(apply $\sigma$ t)] computes $t\sigma$ *)

val apply_term : 'symbol term -> 'symbol substitution -> 'symbol term

val apply_rewrite_rule : 
  'symbol #Signatures.signature -> 
    'symbol Rewrite_rules.rewrite_rule -> 'symbol substitution -> 
      'symbol Rewrite_rules.rewrite_rule

(* 

   [(merge_subst subst1 subst2)] merges substitutions [subst1] and
   [subst2], that is put them together verifying that if [subst1]
   binds a variable $x$ to a term $t_1$ and [subst2] binds the same
   variable to $t_2$, then $t_1=t_2$

   Raises Conflict if not.

   This is standard substitution merging: equality of $t_1$ and $t_2$
   is performed assuming that all symbols are free.

*)

exception Conflict;;

val merge_substs : 
  'symbol substitution -> 'symbol substitution -> 'symbol substitution;;


val substitute :
  'symbol #Signatures.signature -> 
    'symbol substitution -> 
      'symbol term -> 'symbol term;;

val apply_subst_to_eqs :
  'symbol #Signatures.signature -> 
    'symbol substitution -> 
      ('symbol term * 'symbol term) list -> ('symbol term * 'symbol term) list

val print : 
  'symbol #Signatures.signature -> Variables.user_variables 
    -> 'symbol substitution -> unit;;

