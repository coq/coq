(***************************************************************************

This module defines string rewriting

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



		 
(*

  This module defines functions for performing string rewriting of
  words.

  \subsection{String rewriting systems}

  A string rewriting system is defined by a set of pairs of words
  (left-hand side, right-hand side), represented by a list.

*)

type 'symbol rewrite_rule = ('symbol Words.word * 'symbol Words.word)

type 'symbol srs = ('symbol Words.word * 'symbol Words.word) list;;


(*

  ([normalize S w)] returns the normal form of [w] w.r.t the SRS [S]
  by the rightmost strategy. Warning! If the righmost reduction of [w]
  is infinite, this function loops.

*)

val normalize : 
    'symbol srs -> 'symbol Words.word -> 'symbol Words.word ;;

(*

  \subsection{Efficient normalization}

  The complexity of the former normalization function increases
  linearly in the number of rules. The latter increases linearly in
  the maximal length of the left-hand sides of rules.

  [compiled_srs] is an abstract data type that allows efficient
  matching (discrimination net)

*)

type 'symbol compiled_srs;;

(*

  [(compiled_normalize S w)] returns the normal form of [w] w.r.t the SRS [S]
  by the rightmost strategy. Warning! If the righmost reduction of [w]
  is infinite, this function loops.

*)

val compiled_normalize : 
    'symbol compiled_srs -> 'symbol Words.word -> 'symbol Words.word ;;


(*

  [(compile_srs S)] returns a discrimination net equivalent to [S], the
  be used in the previous function.

*)

val compile_srs : 
    'symbol srs -> 'symbol compiled_srs 
;;

(*i [(is_nf S t)] is true when [t] is a normal form of [S] and false otherwise.*)

(*val is_nf :
    'symbol srs -> 'symbol Words.word -> bool 
i*)

val is_nf_compiled :
    'symbol compiled_srs -> 'symbol Words.word -> bool 

(*

  \subsection{Printing SRSs}

  [(print sigma srs)] prints the SRS [srs], its letters being printed
  according to [sigma#string_of_symbol]. The letters are separated by
  spaces. Beware that the printing is done using printing functions of
  the module [Format].

  [(pretty_print sigma srs)] does the same, but factorizing consecutive
  occurences of the same letter.

*)

val print : 
  'symbol #String_signatures.word_signature -> 'symbol srs -> unit;;


val pretty_print : 
  'symbol #String_signatures.word_signature -> 'symbol srs -> unit;;


