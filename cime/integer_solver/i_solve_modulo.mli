(***************************************************************************

  This module provides a function for solving systems of linear equations
  over the integers modulo a given integer $n$.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open I_solve

(* 
  [i_solve_modulo] prend comme arguments

   \begin{itemize}

   \item un entier n modulo lequel on travaille
     Au niveau de l'unification, ca correspond a l'unification ACUN(n),
     ou N(n) est la nilpotence d'ordre n: $x^n = 1$.

   \item un vecteur d'entiers [[|v0;v0+v1;...;v0+v1+...+vk|]] où [v0]
     represente le nombre de variables non instanciees, et vi, i>0, le
     nombre de variables instanciees dans la theorie Ti,

   \item un systeme d'equations ligne par ligne

   \item une liste qui correspond a [pe.edge]
   \end{itemize}

  et retourne un couple de vecteurs de solutions tel que:
  le premier element contient les solutions homogenes, i.e. qui valent
  0 sur les variables instanciees, 
  le second les autres solutions, sachant que les composantes associees 
  a des variables instanciees ne peuvent prendre que les valeurs 0 et 1, 
  et que de plus, si une composante associee a une variable instanciee 
  dans la theorie Ti vaut 1, alors toutes les composantes associees a 
  des variables instanciees dans une theorie Tj , i <> j, valent 0, Ti et
  Tj etant toutes deux des theories REGULIERES, COLLAPSE-FREE. 

  On va essayer autant que faire se peut de ne pas instancier des 
  variables par une valeur contenant une variable marquee interdite.
  
  Si des identifications de variables instanciees sont necessaires, on
  aura [AVEC_IDENT], sinon [SANS_IDENT].

*)

val i_solve_modulo : 
  int -> int array -> int array array -> (int * int) list -> 
    identifications_for_unification


