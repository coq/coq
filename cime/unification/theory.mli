(***************************************************************************

 Equational theories handled by unification and matching modulo

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Signatures

(*
There 3 kinds of unifications in \CiME{}:
\begin{itemize}
\item the [PLAIN] unification is the usual unification modulo;
\item the [AC_COMPLETE] unification provides a representation of the 
  unifiers modulo C and AC by a set of unifiers modulo all the current 
  theories (see \cite{boudet96rta} for more details);
\item the [AC] unification provides a complete set of unifiers modulo C 
  and AC, the others axioms of the theory being ignored.
\end{itemize}
*)

type unif_kind = 
    PLAIN
  | AC_COMPLETE
  | AC_ONLY

val unif_type : unif_kind ref

type 'symbol elem_theory = 
    Empty of 'symbol option
  | C of 'symbol
  | AC of 'symbol
  | ACU of 'symbol * 'symbol
  | ACI of 'symbol
  | AG of 'symbol * 'symbol * 'symbol
  | ACUN of 'symbol * 'symbol * int
  | BR of 'symbol * 'symbol * 'symbol * 'symbol 


exception No_theory

type 'symbol unif_elem_theory =
    'symbol option * 'symbol elem_theory


module OrderedElemTheory :
  Ordered_types.OrderedPolyType with type 'a t = 'a elem_theory

module TheorySet : 
  Ordered_sets.OrderedSet with type 'a elt = 'a elem_theory

module OrderedUnifElemTheory :
  Ordered_types.OrderedPolyType with type 'a t = 'a unif_elem_theory 

module UnifTheorySet : 
  Ordered_sets.OrderedSet with type 'a elt = 'a unif_elem_theory

val additive_symbol_of_theory : 'symbol elem_theory -> 'symbol

val unit_symbol_of_theory : 'symbol elem_theory -> 'symbol

val minus_symbol_of_theory : 'symbol elem_theory -> 'symbol

val elem_theory_from_unif_elem_theory :
  'symbol unif_elem_theory -> 'symbol elem_theory

val string_of_elem_theory :
  'symbol #signature -> 'symbol elem_theory -> string

val string_of_unif_elem_theory :
  'symbol #signature -> 'symbol unif_elem_theory -> string

val print_theory : 'symbol #signature -> 'symbol TheorySet.t -> unit

exception Syntax_error of string

val theory_check : 
  User_signatures.user_signature -> 
    User_signatures.symbol_id elem_theory -> 
      User_signatures.symbol_id elem_theory

