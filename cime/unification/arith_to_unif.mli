(***************************************************************************

  This module provides some functions in order to translate back a
  solved arithmetic problem into a solved unification problem modulo
  an AC-like theory.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Bit_field
open Variables
open Gen_terms
open Theory
open Problems

(*
  cache est une fonction qui prend un vecteur de vecteurs d'entiers 
  positifs (solutions diophantiennes d'un systeme), et qui retourne un vecteur 
  de naturels codant des vecteurs de bits,
  tel que chaque 1 correspond a un entier non-nul de l'entree, et
  chaque 0 correspond a un 0, le tout transpose, pour avoir directement
  acces aux colonnes associees a chaque variable.
*)

val pcache : int array array -> int array

val psmall_enough : int -> int -> int array -> int -> bool

val pgreat_enough : int -> int -> int array -> int -> bool

val gcache : int array array -> Large_bit_field.t array

val gsmall_enough : 
  int -> int -> Large_bit_field.t array -> Large_bit_field.t -> bool

val ggreat_enough : 
  int -> int -> Large_bit_field.t array -> Large_bit_field.t -> bool


(*
  [combinaison_lineaire + vect_var vect_sols vect_nouv_var vect_car]
  retourne une liste d'equations de la forme
  var (de [vect_var]) = un terme de symbole de tete +, dont les 
  variables sont celles de [vect_nouv_var] avec les coefficients
  apparaissant dans [vect_sols]. 
*)

val linear_combination : 
  unif_kind -> 'symbol elem_theory -> var_id VarSet.t -> 
    (unit, int) VarMap.t -> int array array -> 'symbol term array -> 
      int array -> ('symbol term * 'symbol term) list 

(*
  [nettoyer pe_edge vect_var vect_sols] enleve de [vect_sols] les 
  solutions qui vont provoquer un echec pour OC, grace a [pe_edge].
*)

val clean_solutions : 
  'symbol elem_pb -> (unit, int) VarMap.t -> int array array ->
    int array array


(*
  [classer pe_edge vect_var v_type vect_sols] classe le vecteur de solutions
  [vect_sols] en mettant d'abord les solutions qui valent 0 sur toutes 
  les variables instanciees. 
*)
(*i
val classer : 
(var_id * var_id) list -> var_id array -> int array -> int array array ->
 ((int array array) * (int array array)) 
;;
i*)

(*

  [(classify elem_pb array_of_vars map_var_int v_type vect_sols)] returns 
  a pair [(vect_homogeneous_sols,vect_heterogeneous_sols)] where
  \begin{itemize} 
  \item [vect_homogeneous_sols] contains the solutions from the array
  [vect_sols] which are equal to 0 over the marked variables,
  \item [vect_heterogeneous_sols] contains the other solutions of
  [vect_sols]
  \end{itemize} 

  Remark : The solutions of [vect_sols] creating a cycle of size 2 are
  removed in [sorted_vect_sols].

*)

val classify : 
  'symbol elem_pb -> var_id array -> (unit, int) VarMap.t -> int array 
    -> int array array -> (int array array) * (int array array)

(*
rearranger v0v1 reconstruit un vecteur de vecteurs
solutions, ou les vecteurs-solutions qui valent 0 sur toutes 
les composantes correspondant a des variables instanciees sont 
en tete
*)
(*i
val rearranger : ((int array array) * (int array array)) -> int array array
;;
i*)
(*

  [(sum_of_columns matrix)] returns an array containing the sum of 
  the columns of the argument [matrix].

*)

val sum_of_columns : int array array -> int array


(*

  [(associated_var_with_sol sum_of_sols array_of_vars v_type sol)] returns
  \begin{itemize}
  \item [Some c] when the value of the solution [sol] is equal to 1
  for the component corresponding to the marked variable [c] (when
  there are several such marked variables, the function returns the
  first one encountered).
  \item [Some x] when the value of the solution [sol] is equal to 1
  for the component corresponding to the variable [x], and there is no
  other such variable.
  \item [None] otherwise.
  \end{itemize}

*)

val associated_var_with_sol :
  int array -> var_id array -> int array -> int array -> var_id option


(*

  [(associated_marked_var_with_sol array_of_vars v_type sol)] 
  returns
  \begin{itemize}
  \item [Some c] when the value of the solution [sol] is equal to 1
  for the component corresponding to the marked variable [c] (when
  there are several such marked variables, the function returns the
  first one encountered).
  \item [None] otherwise.
  \end{itemize}

*)

val  associated_marked_var_with_sol :
     var_id array -> int array -> int array -> var_id option


(*

  [(generate_vect_char_cst nb_var nb_true_var vect_sols_cst)] generates
  the list of subsets of non-homogeneous Diophantine solutions
  (encoded as 0-1 vectors) which are usefull in order to build
  unifiers for "arithmetic" theories which possess a unit, that is
  ACU, ACUN and AG.

*)

val generate_vect_char_cst : int -> int -> int array array -> int array list


