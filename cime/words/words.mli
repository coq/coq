(***************************************************************************

This module defines the strings (or words) over a string signature

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



		 
(*

  This module defines the strings (or words) over a string signature


  \subsection{type for words}

  A word over an alphabet in explicitly represented by a list of
  elements of this alphabet.

*)

type 'symbol word = 'symbol list;;

val length : 'symbol word -> int ;;

(*

  \subsection{Printing words}

  [(print sigma w)] prints the word [w], its letters being printed
  according to [sigma#string_of_symbol]. The letters are separated by
  spaces. Beware that the printing is done using printing functions of
  the module [Format].

  [(pretty_print sigma w)] does the same, but factorizing consecutive
  occurences of the same letter.

*)

val print : 
  'symbol #String_signatures.word_signature -> 'symbol word -> unit;;


val pretty_print : 
  'symbol #String_signatures.word_signature -> 'symbol word -> unit;;


