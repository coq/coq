(***************************************************************************

 Variable abstraction.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Gen_terms
open Theory

val purify_list_of_equations :
  unif_kind -> ('symbol -> 'symbol unif_elem_theory) ->
    ('symbol term * 'symbol term) list ->
      ('symbol term * 'symbol term) list
