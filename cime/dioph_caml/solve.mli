(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Type_de_donnees_dioph

(* 
  dioph_solve prend comme arguments
   - un vecteur d'entiers [|v0;v0+v1;...;v0+v1+...+vk|] ou` v0 represente
     le nombre de variables non instanciees, et vi, i>0, le nombre
     de variables instanciees dans la theorie Ti, 
   - un systeme d'equations ligne par ligne

  et retourne les solutions minimales du systeme (m1,...,mn) telles
  que les composantes associees a des variables instanciees ne 
  peuvent prendre que les valeurs 0 et 1, et que de plus, si 
  une composante associee a une variable instanciee dans la theorie Ti
  vaut 1, alors toutes les composantes associees a des variables 
  instanciees dans une theorie Tj , i <> j, valent 0
*)
 
val show_state : state -> unit

val dioph_solve : int array -> int array array -> int array array


