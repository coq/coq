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

type symbol_id = int;;

class type user_word_signature =
  object
    inherit [symbol_id] word_signature
    method string_of_symbol : symbol_id -> string
    method symbol_of_string : string -> symbol_id
  end

class from_table (t : string array) =
  object
    val symbol_table = t;
    method string_of_symbol a = symbol_table.(a);
    method symbol_of_string s = 
      let index = ref 0 in
	try
	  for i=0 to pred (Array.length symbol_table) do
	    if symbol_table.(i) = s 
	    then 
	      begin
		index := i;
		raise Exit;
	      end
	  done;
	  raise Not_found
	with
	    Exit -> !index
  end


let from_list l = new from_table (Array.of_list l);;

let from_string s = from_list (Listutils.split s);;

