(***************************************************************************

This module defines the class of signatures for words

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



		 
(*

  This module defines the class of signatures for words
  
  \subsection{The parameterized signature type}

*)

class type ['a] word_signature =
  object
    method string_of_symbol : 'a -> string
  end


(*

  [(from_list l)] builds the finite string signature made from symbols
  in [l]

*)

type symbol_id;;

class type user_word_signature =
  object
    inherit [symbol_id] word_signature
    method string_of_symbol : symbol_id -> string

    (*

      [(symbol_of_string s)] returns the symbol represented by [s],
      raises [Not_found] if no such symbol exists in the signature

    *)
	  
    method symbol_of_string : string -> symbol_id
  end

val from_list : string list -> user_word_signature;; 

val from_string : string -> user_word_signature;;


