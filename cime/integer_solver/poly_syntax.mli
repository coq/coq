(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


exception Syntax_error of string;;

val constraint_of_string : string ->  Abstract_constraint.formula;;

val expr_of_string : string -> Abstract_constraint.expr;;
