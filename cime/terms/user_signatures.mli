(***************************************************************************

Definition of user signatures, given by a syntactic string

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

  This module provides a subclass of the class [Signatures.signature], which allow to build a new signature from a user syntactical declaration. 

*)

type symbol_id;;



(*
  class for user signature. 
*)

class type user_signature = 
  object
    inherit [symbol_id] Signatures.parseable_signature
  end



(*

  Construction of [user_signature] from a given symbol table.

*)

class type symbol_entry =
  object
    method name : string
    method arity : int 
    method fix : Signatures.symbol_fix
    method theory : Signature_syntax.symbol_theory
  end
;;

class from_table : symbol_entry array -> user_signature;;

(*

Constructor of user signatures from a user syntax.  Argument is a
string that represents syntactically a signature. Example :

\begin{verbatim}
  new User_signatures.from_string
    "+ : AC ; 
     0 : constant ; 
     - : unary ;"
\end{verbatim}

*)

val from_string : string -> user_signature;;



(*

  \subsection{Base functions for union of signatures}

  We assume we are given $n$ signatures and we want to build the union
  of them. The following functions provide basic way of converting
  symbol_id between the union of these signatures and the original
  ones.

 
  [extend_symbol f n i] produces a new symbol_id for the symbol id [f]
  of the [i]-th signature in the union of $n$ signatures.

  [ancestor_sig f n] returns the number [i] of the signature from
  which [f] originates.

  [symbol_in_ancestor f n] returns the original symbol id from
  which [f] originates.

  In other words, we have [ancestor_sig (extend_symbol f n i) n = i] and
  [symbol_in_ancestor (extend_symbol f n i) n = f].

*)

(*i
val extend_symbol : symbol_id -> int -> int -> symbol_id;;
val ancestor_sig : symbol_id -> int -> int;;
val symbol_in_ancestor : symbol_id -> int -> symbol_id;;
i*)


val default : user_signature;;
