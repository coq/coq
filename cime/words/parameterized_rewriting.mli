(********************************************************************

This module defines parameterized string rewriting.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

********************************************************************)

		 
(*

  This module defines functions for performing parameterized 
  string rewriting of words.

  \subsection{String rewriting systems}

  A string rewriting system is defined by a set of constrained pairs of words
  (left-hand side, right-hand side, constraint), represented by a list.

*)

type rewrite_rule = 
    {rrule :
       (Parameterized_words.factor list * Parameterized_words.factor list) ;
     rconstr : Linear_constraints.formula;
     renv :  Linear_constraints.var_id list
    }

type srs = rewrite_rule list


(*

pretty print

*)

val pretty_print : srs -> unit



(*

  parsing

*)



val from_abstract_srs :  
  Parameterized_signatures.parameterized_signature -> 
  Parameterized_signatures_syntax.rules -> srs ;;


	     
val normalize : 
    srs -> 
      Parameterized_words.word -> 
	Parameterized_words.word

val is_nf :
      srs -> 
	Parameterized_words.word -> 
	  bool
	    
	    
type c_triple = (Parameterized_words.factor list * 
		 Parameterized_words.factor list *
		 Parameterized_words.factor list *
		 Linear_constraints.formula)

val decompose :
  Parameterized_words.word -> Linear_constraints.var_id list * c_triple list
  

val is_reducible : 
    srs -> 
      Parameterized_words.word -> 
	bool

exception Nf of Parameterized_words.word

val reduce :  
    srs -> 
      Parameterized_words.word -> 
	Parameterized_words.word

val is_localy_confluent : 
    srs -> bool

val is_localy_confluent_extended : 
      srs -> 
	srs -> 
	  bool
	
val critical_pairs : rewrite_rule -> rewrite_rule -> 
  (Parameterized_words.word * Parameterized_words.word) list
