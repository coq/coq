(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Type_de_donnees_dioph;;

val copy_vect_entier : entier array -> entier array;;

val increm_index_list : 
      int -> int array -> int array array -> noeud -> int list
;;

val push_a_stack_elem :
      state -> noeud -> int -> unit
;;
