(***************************************************************************

  This module provides some functions in order to translate a
  unification problem modulo an AC-like theory into an arithmetic
  problem.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Problems
open Theory

(*
(*
  accumulation [|v0;v1;...;vn|] retourne [|v0;v0+v1;...;v0+v1+...+vn|].
*)
val accumulation : int array -> int array;;
*)

(*

  This module provides some functions in order to translate a
  unification modulo AC (resp. ACU, resp. AG) into a system of linear
  equations over the non-negative integers (resp. non-negative
  integers, resp. integers). The variables of the problem are sorted
  according to the theory (other than the current one) where they are
  instanciated:
\begin{verbatim}
   x ....... x     x    .... x     x    ... x   .....
    1         k0    k0+1      k1    k1+1     k2
   \____  ____/   \_____  _____/   \____  ____/
        \/              \/              \/
  non inst. vars    vars inst.       vars int.
                     in Th1           in Th2
\end{verbatim}

  The integer solver returns only solutions of the form
\begin{verbatim}
   n ... n     0 .... 0  ... 0 .... 0   (0 ou 1) ... (0 ou 1) 0 .... 0 ...  
    1     k0                          
  \___  ___/   \__  __/      \__  __/   \________  ________/
      \/          \/            \/               \/

   non inst.   vars inst.     vars int.        vars int.      vars int.
     vars       in Th1        in Th2           in Th(l-1)      in Thl
\end{verbatim}

*)

val add_term :
  'symbol elem_theory -> (unit, int) VarMap.t -> int array -> 
    'symbol term -> unit

(*

  [unif_to_arith_without_matrix elem_pb] returns a pair made of
  \begin{itemize} 
  \item a map giving the indices corresponding to the variables, 
  \item an array of variables corresponding to the inverse map of 
  the above map
  \item an array [[|k1;k2;...|]] of indices as described above.
  \end{itemize}

  Remark : this function should be called only on problems with
  AC-like theories, that is AC, ACU, ACI, ACUN, and AG.

*)

val unif_to_arith_without_matrix : 
    'symbol elem_pb -> (unit, int) VarMap.t * var_id array * int array 

(*

  [unif_to_arith elem_pb] returns a quadruple made of
  \begin{itemize} 
  \item a map giving the indices corresponding to the variables, 
  \item an array of variables corresponding to the inverse map of 
  the above map
  \item an array [[|k1;k2;...|]] of indices as described above.
  \item a matrix of non-negative integers corresponding to the
  translation of the equations of the elementary problem.
  \end{itemize}

  Remark : this function should be called only on problems with
  AC-like theories, that is AC, ACU, ACI, ACUN, and AG.

*)

val unif_to_arith : 
    'symbol elem_pb -> 
      (unit, int) VarMap.t * var_id array * int array * int array array




