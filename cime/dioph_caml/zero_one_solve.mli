(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


(*
  zero_one_solve [|(A1,B1),...,(An,Bn)|] retourne 
  les vecteurs v de la base des solutions de
  Aiv >= 1 <==> Biv >= 1 pour tout i, avec en plus les contraintes
  v.(i) = 1 avec i \in [v_type.(j), v_type.(j+1)[ ==>
  v.(j) = 0 pour tout j v_type.(0) <= j, j \notin  [v_type.(j), v_type.(j+1)[  
*)

val solve : (int array * int array) array -> int array array;;

