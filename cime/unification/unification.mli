(***************************************************************************

Unification modulo some predefined theories

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Signatures
open Gen_terms
open Theory

(*

  [set_of_unifiers unif_k S E term1 term2] returns a complete set of unifiers
  of [term1] and [term2] modulo the equational theory [E], where [S]
  is the signature over which [term1] and [term2] are built. [E] may
  be any combination of some elementary theories among
  \begin{itemize}
  \item the free theory
  \item C 
  \item AC
  \item ACU
  \item ACI
  \item AG
  \item ACUN
  \item BR
  \end{itemize}
  provided that they are pairwise signature-disjoint.



*)

val verbose : int ref

val set_of_solutions : 
  unif_kind -> 'symbol #signature -> (*i Variables.user_variables -> i*)
    ('symbol -> 'symbol unif_elem_theory) -> 'symbol term -> 'symbol term ->
      (unit,'symbol term) VarMap.t list

val plain_set_of_solutions :
  'symbol #signature -> 'symbol TheorySet.t -> (*i user_variables -> i*)
    'symbol term -> 'symbol term -> 
      (unit, 'symbol term) VarMap.t list

val display_plain_set_of_solutions :
  'symbol #signature -> 'symbol TheorySet.t -> user_variables -> 
    'symbol term -> 'symbol term -> unit

val has_a_solution : 
  'symbol #signature -> 'symbol UnifTheorySet.t 
    -> 'symbol term -> 'symbol term 
      -> bool

val free_unification : 
  'symbol #signature -> (*i user_variables -> i*) 
    'symbol term -> 'symbol term -> 
      (unit,'symbol term) Variables.VarMap.t;; 
  
