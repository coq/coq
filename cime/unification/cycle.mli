(***************************************************************************

  This module provides a function which gives some constraints in
  order to break an occur-check cycle in a quasi-solved problem.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Problems

val cycle : 
  'symbol #Signatures.signature -> (*i Variables.user_variables -> i*)
    'symbol problem -> 'symbol problem list


