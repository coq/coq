(***************************************************************************

  This module provides a function for cleaning a solved problem, that is
  removing the equations giving the value of an existentially quantified 
  variable.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Gen_terms
open Problems

val existential_quantifiers_elimination : 
  'symbol problem -> ('symbol term * 'symbol term) list


