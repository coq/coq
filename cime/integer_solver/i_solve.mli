(***************************************************************************

  This module provides a function for solving systems of linear equations
  over the integers.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(* 

  [i_solve] prend comme arguments

   \begin{itemize}
   \item un vecteur d'entiers [[|v0;v0+v1;...;v0+v1+...+vk|]] où [v0]
     représente le nombre de variables non instanciées, et [vi], $i>0$, le
     nombre de variables instanciées dans la theorie $Ti$, 
   \item un systeme d'equations ligne par ligne ;
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

  [i_solve_modulo] fonctionne comme [i_solve], avec un premier argument 
  supplementaire, n, qui est l'entier modulo lequel on travaille.
  Au niveau de l'unification, ca correspond a l'unification ACUN(n),
  ou N(n) est la nilpotence d'ordre n: $x^n = 1$.

*)

type identifications_for_unification = 
     Without_identifications of (int array array) * (int array array)
   | With_identifications of (int array array) * (int array array)
   | No_sol


(*
  Careful extension of the functions [/] and [mod], quotient and reminder of
  the integer division over the negative and positive integers in such a 
  way that
  \[
  p = (p \mathop{zquo} q) * q + (p \mathop{zmod} q),
  \]
  where $0 <= (p \mathop{zmod} q) < \mathop{abs}(q)$.
*)

val zquo : int -> int -> int
val zmod : int -> int -> int

(* 

   [(divides c n v)] checks whether the integer [c] divides the [n]th
   first elements of the array of integers [v].

*)

val divides : int -> int -> int array -> bool

val i_solve : 
  int array -> int array array -> (int * int) list -> 
    identifications_for_unification


