(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Type_de_donnees_dioph;;


val is_solution : int -> noeud -> bool
;;

val extract_solution : noeud -> int array
;;

val add_solution : int array -> state -> unit
;;

(* 
val add_contraint_stack : int -> int array -> pile -> unit
;;
*)

val add_contraint : int array -> state -> unit
;;
