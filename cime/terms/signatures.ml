(***************************************************************************

This module defines the class of first-order signatures, allowing
commutative or associative-commutative symbols.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

		 
(*

  This module defines the class of first-order signatures, allowing
  commutative or associative-commutative symbols.

  \subsection{The signature class type}

  The signature class type is a very general definition of a
   signature: it is a arbitrary set (even infinite) equipped with an
   arity function and some others. The set is modelized here by a type
   parameter.

  [(arity f)] returns the arity of the symbol [f].

  [(is_ac f)] returns [true] if [f] is an associative-commutative symbol. 

  [(is_commutative f)] returns [true] if [f] is a commutative (but not
  associative) symbol.

  [(is_free f)] returns [true] if [f] is neither commutative nor
  associative-commutative.

  [contains_ac_symbols] is [true] there is at least one AC symbol an
  that signature.

  [contains_only_free_symbols] is [true] there all symbols are free.

  [(string_of_symbol f)] must returns a printable representation of
  the symbol [f].

  [(symbol_fix f)] returns a concrete value that tells if [f] must
  printed, in a term, as a prefix symbol, an infix symbol (like $+$ in
  $x+y$, or a postfix symbol (like $!$ in $n!$). The default fix value
  is infix for AC symbols are prefix for others.

  [(smallest_constant o)] returns the smallest constant of the signature
  with respect to the ordering [o].
*)

type symbol_fix = Prefix | Infix | Postfix | Default;;

class type ['a] signature = 
  object
    method arity : 'a -> int
    method is_ac : 'a -> bool
    method is_commutative : 'a -> bool
    method is_free : 'a -> bool
    method contains_ac_symbols : bool      
    method contains_only_free_symbols : bool      
    method string_of_symbol : 'a -> string
    method symbol_fix : 'a -> symbol_fix
    method smallest_constant : 'a Orderings_generalities.ordering -> 'a
  end
;;

class type ['a] parseable_signature = 
      object
	inherit ['a] signature
	method symbol_of_string : string -> 'a
      end
;;



(*

For example, one may defined the infinite signature made of the
natural numbers seen as constant by saying :
\begin{verbatim}
class nat_signature =
  object
    method arity (f:int) = 0
    method is_ac (f:int) = false
    method is_commutative (f:int) = false
    method is_free (f:int) = true
    method contains_ac_symbols = false
    method contains_only_free_symbols = true
    method string_of_symbol (f:int) = string_of_int f
    method symbol_fix (f:int) = Prefix
    method smallest_constant _ = 0
  end;;
let nat_signature = new nat_signature;;
\end{verbatim}


\subsection{Finite symbol sets and maps}

polymorphic set and map module for symbols, compared by the CAML
polymorphic comparaison function.

*)

module SymbolOrd = 
  struct
    type 'a t = 'a
    let compare = compare
  end
;;

module SymbolSet = Ordered_sets.MakePoly(SymbolOrd);;

module SymbolMap = Ordered_maps.MakePoly(SymbolOrd);;


class ['a] default =
  object
    method arity (f : 'a) = 0
    method is_ac (f : 'a) = false
    method is_commutative (f : 'a) = false
    method is_free (f : 'a) = true
    method contains_ac_symbols = false
    method contains_only_free_symbols = true
    method string_of_symbol (f : 'a) = ""
    method symbol_of_string (s : string) = ((raise Not_found) : 'a)
    method symbol_fix (f : 'a) = Prefix
    method smallest_constant (o : 'a Orderings_generalities.ordering) = 
      ((raise Not_found) : 'a)
  end

