(***************************************************************************

  This module provides the function [mark] which adds some constraints
  on a unification problem in order to solve the clashes between the 
  elementary unification theories.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Theory
open Problems


val add_a_mark :
  var_id -> 'symbol mark -> 'symbol unif_elem_theory -> 'symbol problem 
    -> 'symbol problem

(* 

   [(mark pb)] applies the {\bf Mark} rule on the unification problem
   [pb] and returns
   \begin{itemize}
   \item either the exception [Not_appliable]
   \item either the exception [No_solution]
   \item or a list of marked unification problems.
   \end{itemize}

*)

val mark : 'symbol problem -> 'symbol problem list
