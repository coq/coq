(***************************************************************************

Definition of terms on an arbitrary signature

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Positions

type 'symbol term = 
    Term of 'symbol * 'symbol term list
  | Var of Variables.var_id
;;

val leftify_term : 'symbol term -> 'symbol term

val rightify_term : 'symbol term -> 'symbol term

(*

  [(root_symbol t)] returns the root symbol of [t], raises [Not_found]
  if [t] is a variable

*)

val root_symbol : 'a term -> 'a

(*

  [(make_term sigma f l)] builds the term whose top symbol is [f] and
  list of subterms from left to right is [l]. Verifies the
  compatibility with the arity of [f] as given in [sigma]. Raises
  [Bad_arity "f"] in case of incompatibility.
  
  To avoid this tests for efficiency, simply use [Term] directly,
  together with [flatten_term]

*)


exception Bad_arity of string;;

val make_term : 
  'symbol #Signatures.signature -> 'symbol -> 'symbol term list 
    -> 'symbol term;;


val make_term_from_string_term :
  'symbol #Signatures.parseable_signature -> string term -> 'symbol term ;;

(*
  
  [(subterm_at_position p t)] returns the subterm of the term [t] at the
  position [p]. It raises the exception No_subterm when the position [p] 
  is not a position of the term [t].
  
*)

exception No_subterm;;

val subterm_at_position :
  position -> 'symbol term -> 'symbol term

(*

  [(replace_subterm_at_position_in_term u p t)] returns the term [t] with the
  term [u] plugged at the position [p]. It raises the exception No_subterm 
  when the position [p] is not a position of the term [t].

*)

val replace_subterm_at_position_in_term :
  'symbol term -> position -> 'symbol term -> 'symbol term

(*

  [(flatten_term sigma t)] flattens [t] with respect to AC symbols in
  signature [sigma]

  [(head_flatten_term sigma t)] flattens [t] with respect to AC
  symbols in signature [sigma], but only at root

*)

val flatten_term : 
  'symbol #Signatures.signature -> 'symbol term -> 'symbol term;;

val head_flatten_term : 
  'symbol #Signatures.signature -> 'symbol term -> 'symbol term;;

val head_flatten : 
  'symbol #Signatures.signature -> 
    'symbol -> 'symbol term list -> 'symbol term;;


(*

  [(set_of_symbols t)] returns the set of symbols occuring in [t]

*)

val set_of_symbols : 
  'symbol term -> 'symbol Signatures.SymbolSet.t;;

(*

  [(set_of_variables t)] returns the set of variables occuring in [t]

*)

val set_of_variables : 'symbol term -> Variables.var_id Variables.VarSet.t;;


(*

  [(var_occurs_in_term x t)] returns [true] if variable [x] occurs
  somewhere in term [t]. [(var_occurs_in_term_list x t)] is the same
  for a list of terms [l].

*)

val var_occurs_in_term : Variables.var_id -> 'symbol term -> bool;;
val var_occurs_in_term_list : Variables.var_id -> 'symbol term list -> bool;;

(*
  
  [(check_for_right_regularity t1 t2)] returns the set of variables of the
  term [t2] which do not occur in the term [t2].

*)

val check_for_right_regularity : 
  'symbol term -> 'symbol term -> Variables.var_id Variables.VarSet.t;;

(*

  [(build_a_term_for_a_right_regular_pair a t1 t2)] returns the term
  [t2] where all the variables which do not occur in the term [t1] have
  been substituted by the term [a]; [a] is intended to be a constant.
  It raises [Exit] whenever all the variables in [t2] do occur in [t1].
*)

val build_a_term_for_a_right_regular_pair : 
  'symbol term -> 'symbol term -> 'symbol term -> 'symbol term;;

(*

  [(size sigma t)] returns the size of the term [t] built over the
  signature [sign].

*)

val size : 'symbol #Signatures.signature -> 'symbol term -> int


(*
  
  [(compare_terms t1 t2)] returns an integer $n$ such that
  \begin{itemize}
  \item $n=0$ when the terms [t1] and [t2] are identical
  \item $n<0$ when [t1] is strictly smaller than [t2] for an ordering
  \item $n>0$ otherwise
  \end{itemize}
  The only condition known about the ordering is that a variable 
  is strictly greater than a non-variable term.
*)


val compare_terms : 'symbol term -> 'symbol term -> int

(*

  [(sort_term sigma t)] returns a term [t'] which is AC-equivalent to the
  term [t], but where the arguments of an AC (or a C) function symbol have 
  been sorted according to an ordering such that the non-variables are at
  the left-most positions.

*)

val sort_term : 
  'symbol #Signatures.signature -> 'symbol term -> 'symbol term

(*

  [(equals sigma t1 t2)] checks equality of [t1] and [t2] with respect
  to commutative or AC declarations in [sign].

*)

val equals : 
  'symbol #Signatures.signature -> 'symbol term -> 'symbol term -> bool 

(*

[(print_term sigma t)] prints to standard output the term [t] over the
signature [sigma].

*)

val print_term : 
  'symbol #Signatures.signature -> Variables.user_variables -> 'symbol term 
    -> unit;;


(*
  
  [(print_equation_list sigma vars l)] prints to standard output the list of 
  pair of terms [l] built over the signature [sigma] and the variables [vars].

*)

val print_equation_list : 
  'symbol #Signatures.signature -> Variables.user_variables -> 
    ('symbol term * 'symbol term) list ->  unit;;

