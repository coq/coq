(***************************************************************************

Standard matching

CiME Project - D�mons research team - LRI - Universit� Paris XI

$Id$

***************************************************************************)



open Gen_terms;;
open Substitution;;


(* [(matching pattern subject)] returns the most general filter of
  [subject] over [pattern]. Raises [No_match] if no match is found.

   This is standard matching : all symbols are assumed to be free.

*)

exception No_match;;

val matching : 'symbol term -> 'symbol term -> 'symbol substitution;;








